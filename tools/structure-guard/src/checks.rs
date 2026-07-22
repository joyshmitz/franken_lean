//! The structural checks. Each violation is a `Finding` with a stable code:
//!
//! * `FLN-STRUCT-001` crate on disk not declared in the graph file
//! * `FLN-STRUCT-002` declared crate missing on disk
//! * `FLN-STRUCT-003` package name does not match its directory name
//! * `FLN-STRUCT-004` edition is not 2024
//! * `FLN-STRUCT-005` dependency edge present in a manifest but not acknowledged
//! * `FLN-STRUCT-006` acknowledged edge absent from the manifests (stale)
//! * `FLN-STRUCT-007` edge violates strict downward layering / tool-direction law
//! * `FLN-STRUCT-008` prohibited transitive dependency path exists (D3)
//! * `FLN-STRUCT-009` direct dependency outside an `allow-direct` covenant
//! * `FLN-STRUCT-010` external dependency outside the closed universe (D1)
//! * `FLN-STRUCT-011` ordinary/tool crate root missing `#![forbid(unsafe_code)]`
//! * `FLN-STRUCT-012` unsafe-boundary crate root lint wrong (needs `deny`, not `forbid`)
//! * `FLN-STRUCT-013` unledgered `#[allow(unsafe_code)]` site
//! * `FLN-STRUCT-014` stale or mismatched unsafe-ledger row
//! * `FLN-STRUCT-015` line-count covenant exceeded
//! * `FLN-STRUCT-016` parse/shape error (graph file, ledger, manifest, missing roots)
//! * `FLN-STRUCT-017` crate location or naming inconsistent with its declared kind

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};

use crate::graph::{self, CrateKind, GraphFile};
use crate::ledger::{self, AllowSite};
use crate::manifest::{self, Manifest};
use crate::report::fnv1a64;
use crate::{GRAPH_FILE, LEDGER_FILE};

#[derive(Debug)]
pub struct Finding {
    pub code: &'static str,
    pub path: String,
    pub detail: String,
}

#[derive(Debug)]
pub struct RunOutcome {
    pub findings: Vec<Finding>,
    pub crate_count: usize,
    pub edge_count: usize,
    pub graph_digest: u64,
}

struct DiscoveredCrate {
    name: String, // directory name
    dir: PathBuf,
    rel: String,            // e.g. "crates/fln-core"
    location: &'static str, // "crates" | "tools"
    manifest: Option<Manifest>,
}

fn discover(
    root: &Path,
    subdir: &'static str,
    out: &mut Vec<DiscoveredCrate>,
) -> Result<(), String> {
    let dir = root.join(subdir);
    if !dir.is_dir() {
        return Ok(());
    }
    let mut entries: Vec<_> = fs::read_dir(&dir)
        .map_err(|e| format!("cannot read {subdir}/: {e}"))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| format!("cannot read {subdir}/: {e}"))?;
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let path = entry.path();
        if path.is_dir() && path.join("Cargo.toml").is_file() {
            let name = entry.file_name().to_string_lossy().into_owned();
            out.push(DiscoveredCrate {
                rel: format!("{subdir}/{name}"),
                name,
                dir: path,
                location: subdir,
                manifest: None,
            });
        }
    }
    Ok(())
}

/// Count covenant-relevant lines: non-blank, not starting with `//` after trim.
/// Block comments count as code — the covenant is deliberately conservative.
fn count_loc(dir: &Path) -> Result<usize, String> {
    let mut total = 0;
    if !dir.is_dir() {
        return Ok(0);
    }
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let mut entries: Vec<_> = fs::read_dir(&d)
            .map_err(|e| format!("cannot read {}: {e}", d.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| format!("cannot read {}: {e}", d.display()))?;
        entries.sort_by_key(|e| e.file_name());
        for entry in entries {
            let p = entry.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|e| e == "rs") {
                let text = fs::read_to_string(&p)
                    .map_err(|e| format!("cannot read {}: {e}", p.display()))?;
                total += text
                    .lines()
                    .filter(|l| {
                        let t = l.trim();
                        !t.is_empty() && !t.starts_with("//")
                    })
                    .count();
            }
        }
    }
    Ok(total)
}

/// Root files whose lint posture is checked: whichever of `src/lib.rs`/`src/main.rs` exist.
fn crate_roots(c: &DiscoveredCrate) -> Vec<PathBuf> {
    ["lib.rs", "main.rs"]
        .iter()
        .map(|f| c.dir.join("src").join(f))
        .filter(|p| p.is_file())
        .collect()
}

pub fn run(root: &Path) -> Result<RunOutcome, String> {
    let mut findings: Vec<Finding> = Vec::new();

    // ---- load the reviewed files -------------------------------------------------------
    let graph_path = root.join(GRAPH_FILE);
    let graph_text =
        fs::read_to_string(&graph_path).map_err(|e| format!("cannot read {GRAPH_FILE}: {e}"))?;
    let graph_digest = fnv1a64(graph_text.as_bytes());
    let g: GraphFile = graph::parse(&graph_text)?;

    let ledger_text = fs::read_to_string(root.join(LEDGER_FILE))
        .map_err(|e| format!("cannot read {LEDGER_FILE}: {e}"))?;
    let unsafe_ledger = ledger::parse(&ledger_text)?;

    // ---- discover the actual workspace -------------------------------------------------
    let mut discovered: Vec<DiscoveredCrate> = Vec::new();
    discover(root, "crates", &mut discovered)?;
    discover(root, "tools", &mut discovered)?;

    for c in &mut discovered {
        let manifest_rel = format!("{}/Cargo.toml", c.rel);
        let text = fs::read_to_string(c.dir.join("Cargo.toml"))
            .map_err(|e| format!("cannot read {manifest_rel}: {e}"))?;
        match manifest::parse(&text, &manifest_rel) {
            Ok(m) => c.manifest = Some(m),
            Err(e) => findings.push(Finding {
                code: "FLN-STRUCT-016",
                path: manifest_rel,
                detail: e,
            }),
        }
    }

    // ---- snapshot law: crates on disk <-> crates declared ------------------------------
    let on_disk: BTreeMap<&str, &DiscoveredCrate> =
        discovered.iter().map(|c| (c.name.as_str(), c)).collect();
    for c in &discovered {
        match g.crates.get(&c.name) {
            None => findings.push(Finding {
                code: "FLN-STRUCT-001",
                path: c.rel.clone(),
                detail: format!(
                    "crate `{}` exists on disk but is not acknowledged in {GRAPH_FILE}",
                    c.name
                ),
            }),
            Some(decl) => {
                let expected_location = match decl.kind {
                    CrateKind::Tool => "tools",
                    _ => "crates",
                };
                if c.location != expected_location {
                    findings.push(Finding {
                        code: "FLN-STRUCT-017",
                        path: c.rel.clone(),
                        detail: format!(
                            "crate `{}` is declared kind={} and must live under {expected_location}/",
                            c.name,
                            decl.kind.as_str()
                        ),
                    });
                }
                let name_is_boundary = c.name.starts_with("fln-unsafe-");
                let kind_is_boundary = decl.kind == CrateKind::UnsafeBoundary;
                if name_is_boundary != kind_is_boundary {
                    findings.push(Finding {
                        code: "FLN-STRUCT-017",
                        path: c.rel.clone(),
                        detail: format!(
                            "crate `{}`: the `fln-unsafe-` prefix and kind=unsafe-boundary must coincide (D3)",
                            c.name
                        ),
                    });
                }
            }
        }
    }
    for decl in g.crates.values() {
        if !on_disk.contains_key(decl.name.as_str()) {
            findings.push(Finding {
                code: "FLN-STRUCT-002",
                path: GRAPH_FILE.to_string(),
                detail: format!("declared crate `{}` is missing on disk", decl.name),
            });
        }
    }

    // ---- manifest sanity: name matches dir, edition pinned -----------------------------
    for c in &discovered {
        let Some(m) = &c.manifest else { continue };
        if m.name != c.name {
            findings.push(Finding {
                code: "FLN-STRUCT-003",
                path: format!("{}/Cargo.toml", c.rel),
                detail: format!("package name `{}` != directory name `{}`", m.name, c.name),
            });
        }
        if m.edition != "2024" {
            findings.push(Finding {
                code: "FLN-STRUCT-004",
                path: format!("{}/Cargo.toml", c.rel),
                detail: format!("edition `{}` — the workspace pins edition 2024", m.edition),
            });
        }
    }

    // ---- actual edge set + closed universe ---------------------------------------------
    let suite: BTreeSet<&str> = g.suite_deps.iter().map(String::as_str).collect();
    let mut actual_edges: BTreeSet<(String, String)> = BTreeSet::new();
    for c in &discovered {
        let Some(m) = &c.manifest else { continue };
        for dep in &m.deps {
            if on_disk.contains_key(dep.name.as_str()) || g.crates.contains_key(&dep.name) {
                if !dep.has_path {
                    findings.push(Finding {
                        code: "FLN-STRUCT-010",
                        path: format!("{}/Cargo.toml", c.rel),
                        detail: format!(
                            "workspace dependency `{}` must be a path dependency",
                            dep.name
                        ),
                    });
                }
                actual_edges.insert((c.name.clone(), dep.name.clone()));
            } else if suite.contains(dep.name.as_str()) {
                if !dep.has_path {
                    findings.push(Finding {
                        code: "FLN-STRUCT-010",
                        path: format!("{}/Cargo.toml", c.rel),
                        detail: format!(
                            "FrankenSuite dependency `{}` must be a path dependency (D1; SUITE.lock pending)",
                            dep.name
                        ),
                    });
                }
            } else {
                findings.push(Finding {
                    code: "FLN-STRUCT-010",
                    path: format!("{}/Cargo.toml", c.rel),
                    detail: format!(
                        "dependency `{}` ({}) is outside the closed universe (D1)",
                        dep.name, dep.section
                    ),
                });
            }
        }
    }

    // ---- edge acknowledgment (snapshot law over edges) ---------------------------------
    let declared_edges: BTreeSet<(String, String)> = g.edges.iter().cloned().collect();
    for (from, to) in &actual_edges {
        if !declared_edges.contains(&(from.clone(), to.clone())) {
            findings.push(Finding {
                code: "FLN-STRUCT-005",
                path: format!("crates/{from}/Cargo.toml"),
                detail: format!(
                    "dependency edge `{from} -> {to}` is not acknowledged in {GRAPH_FILE}"
                ),
            });
        }
    }
    for (from, to) in &declared_edges {
        if !actual_edges.contains(&(from.clone(), to.clone())) {
            findings.push(Finding {
                code: "FLN-STRUCT-006",
                path: GRAPH_FILE.to_string(),
                detail: format!(
                    "acknowledged edge `{from} -> {to}` no longer exists in any manifest"
                ),
            });
        }
    }

    // ---- layering: strictly downward; tools are one-way --------------------------------
    for (from, to) in &actual_edges {
        let (Some(fd), Some(td)) = (g.crates.get(from), g.crates.get(to)) else {
            continue; // unacknowledged crates already reported
        };
        match (fd.kind, td.kind) {
            (CrateKind::Tool, _) => {} // tools may observe the product graph
            (_, CrateKind::Tool) => findings.push(Finding {
                code: "FLN-STRUCT-007",
                path: format!("crates/{from}/Cargo.toml"),
                detail: format!("product crate `{from}` must not depend on tool crate `{to}`"),
            }),
            _ => {
                let (fr, tr) = (fd.rank.unwrap_or(0), td.rank.unwrap_or(0));
                if fr <= tr {
                    findings.push(Finding {
                        code: "FLN-STRUCT-007",
                        path: format!("crates/{from}/Cargo.toml"),
                        detail: format!(
                            "edge `{from}` (rank {fr}) -> `{to}` (rank {tr}) violates strict downward layering (§5)"
                        ),
                    });
                }
            }
        }
    }

    // ---- D3 transitive prohibitions ----------------------------------------------------
    let mut adjacency: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (from, to) in &actual_edges {
        adjacency
            .entry(from.as_str())
            .or_default()
            .push(to.as_str());
    }
    for (src_pat, dst_pat) in &g.prohibits {
        for src in g.crates.keys().filter(|n| src_pat.matches(n)) {
            // BFS with parent tracking so the finding shows the offending path.
            let mut parent: BTreeMap<&str, &str> = BTreeMap::new();
            let mut queue: VecDeque<&str> = VecDeque::new();
            queue.push_back(src.as_str());
            let mut seen: BTreeSet<&str> = BTreeSet::from([src.as_str()]);
            while let Some(cur) = queue.pop_front() {
                for next in adjacency.get(cur).into_iter().flatten() {
                    if !seen.insert(next) {
                        continue;
                    }
                    parent.insert(next, cur);
                    if dst_pat.matches(next) && *next != src.as_str() {
                        let mut path_nodes = vec![*next];
                        let mut walk = *next;
                        while let Some(p) = parent.get(walk) {
                            path_nodes.push(p);
                            walk = p;
                        }
                        path_nodes.reverse();
                        findings.push(Finding {
                            code: "FLN-STRUCT-008",
                            path: format!("crates/{src}"),
                            detail: format!(
                                "prohibited path `{}` (rule: {} ->* {})",
                                path_nodes.join(" -> "),
                                src_pat.as_str(),
                                dst_pat.as_str()
                            ),
                        });
                    }
                    queue.push_back(next);
                }
            }
        }
    }

    // ---- trust-base direct-dependency covenants ----------------------------------------
    for (crate_name, allowed) in &g.allow_direct {
        let Some(c) = on_disk.get(crate_name.as_str()) else {
            continue;
        };
        let Some(m) = &c.manifest else { continue };
        for dep in &m.deps {
            if !allowed.iter().any(|a| a == &dep.name) {
                findings.push(Finding {
                    code: "FLN-STRUCT-009",
                    path: format!("{}/Cargo.toml", c.rel),
                    detail: format!(
                        "`{crate_name}` direct dependency `{}` is outside its allow-direct covenant ({})",
                        dep.name,
                        if allowed.is_empty() {
                            "empty".to_string()
                        } else {
                            allowed.join(", ")
                        }
                    ),
                });
            }
        }
    }

    // ---- unsafe posture at crate roots -------------------------------------------------
    for c in &discovered {
        let Some(decl) = g.crates.get(&c.name) else {
            continue;
        };
        let roots = crate_roots(c);
        if roots.is_empty() {
            findings.push(Finding {
                code: "FLN-STRUCT-016",
                path: c.rel.clone(),
                detail: "crate has neither src/lib.rs nor src/main.rs".to_string(),
            });
            continue;
        }
        for root_file in roots {
            let rel = format!(
                "{}/src/{}",
                c.rel,
                root_file.file_name().unwrap_or_default().to_string_lossy()
            );
            let text =
                fs::read_to_string(&root_file).map_err(|e| format!("cannot read {rel}: {e}"))?;
            let has_forbid = text.lines().any(|l| l.trim() == "#![forbid(unsafe_code)]");
            let has_deny = text.lines().any(|l| l.trim() == "#![deny(unsafe_code)]");
            match decl.kind {
                CrateKind::UnsafeBoundary => {
                    if has_forbid {
                        findings.push(Finding {
                            code: "FLN-STRUCT-012",
                            path: rel.clone(),
                            detail: "boundary crate must use deny(unsafe_code), not forbid (D3)"
                                .to_string(),
                        });
                    }
                    if !has_deny {
                        findings.push(Finding {
                            code: "FLN-STRUCT-012",
                            path: rel,
                            detail: "boundary crate root missing `#![deny(unsafe_code)]` (D3)"
                                .to_string(),
                        });
                    }
                }
                _ => {
                    if !has_forbid {
                        findings.push(Finding {
                            code: "FLN-STRUCT-011",
                            path: rel,
                            detail: "crate root missing `#![forbid(unsafe_code)]` (D3)".to_string(),
                        });
                    }
                }
            }
        }
    }

    // ---- unsafe-ledger discipline ------------------------------------------------------
    // Only the boundary crates are scanned for allow-sites: ordinary and tool crates
    // are closed by the `#![forbid(unsafe_code)]` root check above plus rustc itself
    // (forbid cannot be overridden by an inner allow).
    let mut sites: Vec<AllowSite> = Vec::new();
    for c in &discovered {
        let is_boundary = g
            .crates
            .get(&c.name)
            .is_some_and(|d| d.kind == CrateKind::UnsafeBoundary);
        if !is_boundary {
            continue;
        }
        let src = c.dir.join("src");
        if src.is_dir() {
            ledger::scan_allow_sites(&src, &format!("{}/src", c.rel), &mut sites)?;
        }
    }
    let mut used_ids: BTreeMap<&str, usize> = BTreeMap::new();
    for site in &sites {
        match &site.id {
            None => findings.push(Finding {
                code: "FLN-STRUCT-013",
                path: format!("{}:{}", site.path, site.line),
                detail:
                    "allow(unsafe_code) site missing its `// UNSAFE-LEDGER: FLN-UL-NNNN` marker"
                        .to_string(),
            }),
            Some(id) => {
                *used_ids.entry(id.as_str()).or_insert(0) += 1;
                match unsafe_ledger.rows.iter().find(|r| &r.id == id) {
                    None => findings.push(Finding {
                        code: "FLN-STRUCT-013",
                        path: format!("{}:{}", site.path, site.line),
                        detail: format!("marker `{id}` has no row in {LEDGER_FILE}"),
                    }),
                    Some(row) if row.path != site.path => findings.push(Finding {
                        code: "FLN-STRUCT-014",
                        path: LEDGER_FILE.to_string(),
                        detail: format!(
                            "row `{id}` names path `{}` but the site is at `{}`",
                            row.path, site.path
                        ),
                    }),
                    Some(_) => {}
                }
            }
        }
    }
    for (id, count) in &used_ids {
        if *count > 1 {
            findings.push(Finding {
                code: "FLN-STRUCT-013",
                path: LEDGER_FILE.to_string(),
                detail: format!("marker `{id}` is used by {count} sites — one row per site (D3)"),
            });
        }
    }
    for row in &unsafe_ledger.rows {
        if !used_ids.contains_key(row.id.as_str()) {
            findings.push(Finding {
                code: "FLN-STRUCT-014",
                path: LEDGER_FILE.to_string(),
                detail: format!(
                    "row `{}` has no matching allow(unsafe_code) site (stale)",
                    row.id
                ),
            });
        }
    }

    // ---- line-count covenants ----------------------------------------------------------
    for (crate_name, limit) in &g.covenants {
        let Some(c) = on_disk.get(crate_name.as_str()) else {
            continue;
        };
        let loc = count_loc(&c.dir.join("src"))?;
        if loc > *limit {
            findings.push(Finding {
                code: "FLN-STRUCT-015",
                path: format!("{}/src", c.rel),
                detail: format!(
                    "`{crate_name}` has {loc} covenant-relevant lines, exceeding max-loc={limit}; growth requires amending the plan first (§8)"
                ),
            });
        }
    }

    findings.sort_by(|a, b| (a.code, &a.path, &a.detail).cmp(&(b.code, &b.path, &b.detail)));
    Ok(RunOutcome {
        findings,
        crate_count: discovered.len(),
        edge_count: actual_edges.len(),
        graph_digest,
    })
}
