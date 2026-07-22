//! Seeded-violation tests (bead fln-8mj acceptance): each structural CI check must
//! demonstrably fail on a synthetic workspace carrying exactly the defect it exists to
//! catch, and pass once the defect is repaired. These are the permanent, in-tree form
//! of "add a test-only violation in CI to prove detection, then remove".

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use structure_guard::checks::{self, RunOutcome};

/// An immutable workspace recipe. Every execution materializes a fresh, uniquely named
/// root and retains it for inspection, as required by the repository's no-deletion rule.
struct TempWs {
    tag: String,
    files: RefCell<BTreeMap<String, String>>,
}

impl TempWs {
    fn new(tag: &str) -> TempWs {
        TempWs {
            tag: tag.to_string(),
            files: RefCell::new(BTreeMap::new()),
        }
    }

    fn write(&self, rel: &str, content: &str) {
        self.files
            .borrow_mut()
            .insert(rel.to_string(), content.to_string());
    }

    fn materialize(&self) -> Result<PathBuf, String> {
        static NEXT_ROOT: AtomicU64 = AtomicU64::new(0);
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|error| format!("system clock precedes Unix epoch: {error}"))?
            .as_nanos();
        let root = loop {
            let sequence = NEXT_ROOT.fetch_add(1, Ordering::Relaxed);
            let candidate = std::env::temp_dir().join(format!(
                "structure-guard-test-{}-{stamp}-{sequence}-{}",
                std::process::id(),
                self.tag
            ));
            match fs::create_dir(&candidate) {
                Ok(()) => break candidate,
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(format!("create retained fixture root: {error}")),
            }
        };

        for (rel, content) in self.files.borrow().iter() {
            let path = root.join(rel);
            let parent = path
                .parent()
                .ok_or_else(|| format!("fixture path has no parent: {rel}"))?;
            fs::create_dir_all(parent)
                .map_err(|error| format!("create fixture directories for {rel}: {error}"))?;
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&path)
                .map_err(|error| format!("create fixture file {rel} without overwrite: {error}"))?;
            file.write_all(content.as_bytes())
                .map_err(|error| format!("write fixture file {rel}: {error}"))?;
        }
        eprintln!("retained structure-guard fixture: {}", root.display());
        Ok(root)
    }

    fn run(&self) -> RunOutcome {
        let root = self.materialize().expect("materialize retained fixture");
        checks::run(&root).expect("guard runs")
    }
}

const BASE_GRAPH: &str = "\
schema fln-workspace-graph/1
crate fln-core       rank=0  kind=ordinary
crate fln-hash       rank=1  kind=ordinary
crate fln-unsafe-abi rank=2  kind=unsafe-boundary
crate fln-kernel     rank=6  kind=ordinary
crate fln-mid        rank=8  kind=ordinary
crate fln-unsafe-jit rank=12 kind=unsafe-boundary
prohibit fln-unsafe-* ->* fln-kernel
allow-direct fln-kernel = fln-core
covenant fln-kernel max-loc=100
suite-dep asupersync
";

const EMPTY_LEDGER: &str = "schema fln-unsafe-ledger/1\n";

fn manifest(name: &str, deps: &[&str]) -> String {
    let mut m = format!(
        "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\nlicense = \"MIT\"\npublish = false\n\n[dependencies]\n"
    );
    for dep in deps {
        m.push_str(&format!("{dep} = {{ path = \"../{dep}\" }}\n"));
    }
    m
}

fn lib_rs(boundary: bool) -> &'static str {
    if boundary {
        "//! boundary stub\n#![deny(unsafe_code)]\n"
    } else {
        "//! stub\n#![forbid(unsafe_code)]\n"
    }
}

/// Baseline clean fixture: six crates matching BASE_GRAPH, no edges.
fn base(ws: &TempWs) {
    ws.write("ci/WORKSPACE_GRAPH.txt", BASE_GRAPH);
    ws.write("ci/UNSAFE_LEDGER.txt", EMPTY_LEDGER);
    for (name, boundary) in [
        ("fln-core", false),
        ("fln-hash", false),
        ("fln-unsafe-abi", true),
        ("fln-kernel", false),
        ("fln-mid", false),
        ("fln-unsafe-jit", true),
    ] {
        ws.write(&format!("crates/{name}/Cargo.toml"), &manifest(name, &[]));
        ws.write(&format!("crates/{name}/src/lib.rs"), lib_rs(boundary));
    }
}

fn codes(outcome: &RunOutcome) -> Vec<&'static str> {
    outcome.findings.iter().map(|f| f.code).collect()
}

fn graph_with_edges(edges: &[&str]) -> String {
    let mut g = String::from(BASE_GRAPH);
    for e in edges {
        g.push_str(&format!("edge {e}\n"));
    }
    g
}

#[test]
fn clean_fixture_passes() {
    let ws = TempWs::new("clean");
    base(&ws);
    let out = ws.run();
    assert!(out.findings.is_empty(), "unexpected: {:?}", out.findings);
    assert_eq!(out.crate_count, 6);
}

#[test]
fn upward_edge_violates_layering() {
    let ws = TempWs::new("upward");
    base(&ws);
    ws.write(
        "crates/fln-core/Cargo.toml",
        &manifest("fln-core", &["fln-kernel"]),
    );
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-core -> fln-kernel"]),
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-007"]);
}

#[test]
fn unacknowledged_edge_is_flagged_and_recovers_when_acknowledged() {
    let ws = TempWs::new("unack-edge");
    base(&ws);
    ws.write(
        "crates/fln-hash/Cargo.toml",
        &manifest("fln-hash", &["fln-core"]),
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-005"]);

    // Recovery: acknowledge the edge in the reviewed file; the gate goes green.
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-hash -> fln-core"]),
    );
    assert!(ws.run().findings.is_empty());
}

#[test]
fn stale_acknowledged_edge_is_flagged() {
    let ws = TempWs::new("stale-edge");
    base(&ws);
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-hash -> fln-core"]),
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-006"]);
}

#[test]
fn undeclared_crate_on_disk_is_flagged() {
    let ws = TempWs::new("rogue");
    base(&ws);
    ws.write("crates/fln-rogue/Cargo.toml", &manifest("fln-rogue", &[]));
    ws.write("crates/fln-rogue/src/lib.rs", lib_rs(false));
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-001"]);
}

#[test]
fn declared_crate_missing_on_disk_is_flagged() {
    let ws = TempWs::new("ghost");
    base(&ws);
    let g = BASE_GRAPH.replace("prohibit", "crate fln-ghost rank=3 kind=ordinary\nprohibit");
    ws.write("ci/WORKSPACE_GRAPH.txt", &g);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-002"]);
}

#[test]
fn prohibited_transitive_path_is_flagged() {
    let ws = TempWs::new("transitive");
    base(&ws);
    // Both hops are individually legal (12 > 8 > 6) — only the D3 transitive
    // prohibition fln-unsafe-* ->* fln-kernel catches the composition.
    ws.write(
        "crates/fln-unsafe-jit/Cargo.toml",
        &manifest("fln-unsafe-jit", &["fln-mid"]),
    );
    ws.write(
        "crates/fln-mid/Cargo.toml",
        &manifest("fln-mid", &["fln-kernel"]),
    );
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-unsafe-jit -> fln-mid", "fln-mid -> fln-kernel"]),
    );
    let out = ws.run();
    assert_eq!(codes(&out), vec!["FLN-STRUCT-008"]);
    assert!(
        out.findings[0]
            .detail
            .contains("fln-unsafe-jit -> fln-mid -> fln-kernel"),
        "path missing from detail: {}",
        out.findings[0].detail
    );
}

#[test]
fn allow_direct_covenant_is_enforced() {
    let ws = TempWs::new("allow-direct");
    base(&ws);
    // fln-kernel -> fln-hash is downward and acknowledged, but outside the kernel's
    // exhaustive direct-dependency allowlist (fln-core only).
    ws.write(
        "crates/fln-kernel/Cargo.toml",
        &manifest("fln-kernel", &["fln-hash"]),
    );
    ws.write(
        "ci/WORKSPACE_GRAPH.txt",
        &graph_with_edges(&["fln-kernel -> fln-hash"]),
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-009"]);
}

#[test]
fn external_dep_outside_closed_universe_is_flagged() {
    let ws = TempWs::new("serde");
    base(&ws);
    let mut m = manifest("fln-hash", &[]);
    m.push_str("serde = \"1\"\n");
    ws.write("crates/fln-hash/Cargo.toml", &m);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-010"]);
}

#[test]
fn suite_dep_requires_path_form() {
    let ws = TempWs::new("suite-path");
    base(&ws);
    let mut m = manifest("fln-hash", &[]);
    m.push_str("asupersync = \"1\"\n");
    ws.write("crates/fln-hash/Cargo.toml", &m);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-010"]);

    // Recovery: the path form is the allowed shape (pin lands with SUITE.lock).
    let mut m = manifest("fln-hash", &[]);
    m.push_str("asupersync = { path = \"/dp/asupersync\" }\n");
    ws.write("crates/fln-hash/Cargo.toml", &m);
    assert!(ws.run().findings.is_empty());
}

#[test]
fn missing_forbid_pragma_is_flagged() {
    let ws = TempWs::new("no-forbid");
    base(&ws);
    ws.write(
        "crates/fln-hash/src/lib.rs",
        "//! stub without the pragma\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-011"]);
}

#[test]
fn boundary_crate_with_forbid_is_flagged() {
    let ws = TempWs::new("boundary-forbid");
    base(&ws);
    ws.write("crates/fln-unsafe-abi/src/lib.rs", lib_rs(false));
    let out = ws.run();
    assert!(!out.findings.is_empty());
    assert!(codes(&out).iter().all(|c| *c == "FLN-STRUCT-012"));
}

#[test]
fn unledgered_allow_site_is_flagged_and_ledgered_site_passes() {
    let ws = TempWs::new("unledgered");
    base(&ws);
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "//! boundary stub\n#![deny(unsafe_code)]\n\n#[allow(unsafe_code)]\npub fn peek() {}\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-013"]);

    // Recovery: marker + matching ledger row make the same site legal.
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "//! boundary stub\n#![deny(unsafe_code)]\n\n// UNSAFE-LEDGER: FLN-UL-0001\n#[allow(unsafe_code)]\npub fn peek() {}\n",
    );
    ws.write(
        "ci/UNSAFE_LEDGER.txt",
        "schema fln-unsafe-ledger/1\nrow FLN-UL-0001 | crates/fln-unsafe-abi/src/lib.rs | layout law | rig T-1 | safe copy path | result never enters a checked declaration\n",
    );
    assert!(ws.run().findings.is_empty());
}

#[test]
fn stale_ledger_row_is_flagged() {
    let ws = TempWs::new("stale-row");
    base(&ws);
    ws.write(
        "ci/UNSAFE_LEDGER.txt",
        "schema fln-unsafe-ledger/1\nrow FLN-UL-0009 | crates/fln-unsafe-abi/src/lib.rs | inv | ev | fb | ncb\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-014"]);
}

#[test]
fn comment_mentions_of_allow_are_not_sites() {
    // Doc comments and comments may mention the attribute (the boundary stubs do, to
    // document the ledger discipline) without creating a ledgerable site.
    let ws = TempWs::new("comment-mention");
    base(&ws);
    ws.write(
        "crates/fln-unsafe-abi/src/lib.rs",
        "//! docs may mention #[allow(unsafe_code)] freely\n#![deny(unsafe_code)]\n// a comment naming #[allow(unsafe_code)] is not a site either\n",
    );
    assert!(ws.run().findings.is_empty());
}

#[test]
fn kernel_line_covenant_is_enforced() {
    let ws = TempWs::new("covenant");
    base(&ws);
    let mut big = String::from("//! stub\n#![forbid(unsafe_code)]\n");
    for i in 0..100 {
        big.push_str(&format!("pub fn f{i}() {{}}\n"));
    }
    // Doc comment excluded; 1 pragma line + 100 fns = 101 covenant-relevant lines,
    // exceeding the fixture covenant max-loc=100 (kept small so the test stays fast).
    ws.write("crates/fln-kernel/src/lib.rs", &big);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-015"]);
}

#[test]
fn wrong_edition_is_flagged() {
    let ws = TempWs::new("edition");
    base(&ws);
    let m = manifest("fln-hash", &[]).replace("edition = \"2024\"", "edition = \"2021\"");
    ws.write("crates/fln-hash/Cargo.toml", &m);
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-004"]);
}

#[test]
fn unsafe_prefix_and_kind_must_coincide() {
    let ws = TempWs::new("prefix-kind");
    base(&ws);
    let g = BASE_GRAPH.replace(
        "crate fln-unsafe-abi rank=2  kind=unsafe-boundary",
        "crate fln-unsafe-abi rank=2  kind=ordinary",
    );
    ws.write("ci/WORKSPACE_GRAPH.txt", &g);
    // The kind mismatch fires; the deny-rooted lib under an "ordinary" kind fires too.
    let out = ws.run();
    assert!(
        codes(&out).contains(&"FLN-STRUCT-017"),
        "got {:?}",
        out.findings
    );
}

#[test]
fn unparseable_manifest_is_a_finding_not_a_guess() {
    let ws = TempWs::new("bad-manifest");
    base(&ws);
    ws.write(
        "crates/fln-hash/Cargo.toml",
        "[package]\nname = \"fln-hash\"\nedition = \"2024\"\n[patch.crates-io]\nx = \"1\"\n",
    );
    assert_eq!(codes(&ws.run()), vec!["FLN-STRUCT-016"]);
}

/// The guard runs against a root missing the reviewed files -> setup failure (exit 2
/// path), never a silent pass.
#[test]
fn missing_reviewed_files_are_setup_failures() {
    let ws = TempWs::new("no-files");
    let root = ws.materialize().expect("materialize retained fixture");
    assert!(checks::run(Path::new(&root)).is_err());
}
