//! KERNEL_CONTRACT.md is CI-checked like code (bead franken_lean-79k):
//!
//! * **anchor resolution** — every cited Reference source location must exist at the
//!   pin, and its `expect="token"` must appear on that exact line — drift fails;
//! * **coverage** — every rule names at least one fixture, or an explicit stub with
//!   an owner bead — no silently unevidenced rule;
//! * **ledger linkage** — every Parity-Ledger row on the `kernel` surface must name
//!   an existing rule id as its symbol — a dangling link fails.
//!
//! Rule-block grammar the checker parses (inside the markdown):
//!
//! ```text
//! ### KR-NNN · <title>
//! anchor: <repo-relative-path>:<line> (<function>) expect="<token>"
//! fixtures: <path>[, <path>...]        OR   fixtures: stub owner=<bead-id>
//! ```
//!
//! A rule may carry several `anchor:` lines; every one is resolved.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

fn workspace_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
}

#[derive(Debug, Default)]
struct Rule {
    id: String,
    heading_line: usize,
    anchors: Vec<(usize, String)>,
    fixtures: Vec<String>,
    stub_owner: Option<String>,
}

fn parse_rules(text: &str) -> (Vec<Rule>, Vec<String>) {
    let mut rules: Vec<Rule> = Vec::new();
    let mut problems: Vec<String> = Vec::new();
    for (idx, line) in text.lines().enumerate() {
        let lineno = idx + 1;
        if let Some(rest) = line.strip_prefix("### ") {
            if let Some(id) = rest.split_whitespace().next()
                && id.starts_with("KR-")
            {
                rules.push(Rule {
                    id: id.to_string(),
                    heading_line: lineno,
                    ..Rule::default()
                });
            }
            continue;
        }
        let Some(rule) = rules.last_mut() else {
            continue;
        };
        if let Some(anchor) = line.trim().strip_prefix("anchor: ") {
            rules_push_anchor(rule, anchor, lineno, &mut problems);
        } else if let Some(fixtures) = line.trim().strip_prefix("fixtures: ") {
            if let Some(owner_part) = fixtures.strip_prefix("stub owner=") {
                let owner = owner_part.trim();
                if owner.is_empty() {
                    problems.push(format!("line {lineno}: stub without an owner"));
                } else {
                    rule.stub_owner = Some(owner.to_string());
                }
            } else {
                rule.fixtures.extend(
                    fixtures
                        .split(',')
                        .map(str::trim)
                        .filter(|s| !s.is_empty())
                        .map(str::to_string),
                );
            }
        }
    }
    (rules, problems)
}

fn rules_push_anchor(rule: &mut Rule, anchor: &str, lineno: usize, problems: &mut Vec<String>) {
    // `<path>:<line> (<function>) expect="<token>"` — function is informative,
    // path/line/token are checked.
    let Some((location, tail)) = anchor.split_once(' ') else {
        problems.push(format!("line {lineno}: malformed anchor `{anchor}`"));
        return;
    };
    let Some((path, line_str)) = location.rsplit_once(':') else {
        problems.push(format!("line {lineno}: anchor without a line number"));
        return;
    };
    let Ok(cited_line) = line_str.parse::<usize>() else {
        problems.push(format!("line {lineno}: non-numeric anchor line"));
        return;
    };
    let token = tail
        .split_once("expect=\"")
        .and_then(|(_, rest)| rest.split_once('"'))
        .map(|(token, _)| token.to_string());
    let Some(token) = token else {
        problems.push(format!(
            "line {lineno}: anchor for {} lacks expect=\"token\"",
            rule.id
        ));
        return;
    };
    rule.anchors.push((cited_line, format!("{path}|{token}")));
}

#[test]
fn the_contract_parses_resolves_and_covers() {
    let root = workspace_root();
    let text = fs::read_to_string(root.join("KERNEL_CONTRACT.md")).expect("contract exists");
    let (rules, problems) = parse_rules(&text);
    assert!(
        problems.is_empty(),
        "malformed rule blocks:\n{}",
        problems.join("\n")
    );
    assert!(
        rules.len() >= 30,
        "the judgment inventory is present ({} rules)",
        rules.len()
    );

    let mut failures: Vec<String> = Vec::new();
    let mut ids = BTreeSet::new();
    for rule in &rules {
        if !ids.insert(rule.id.clone()) {
            failures.push(format!("{}: duplicate rule id", rule.id));
        }
        if rule.anchors.is_empty() {
            failures.push(format!("{}: no Reference anchor", rule.id));
        }
        for (cited_line, path_token) in &rule.anchors {
            let (path, token) = path_token.split_once('|').expect("packed above");
            let source = match fs::read_to_string(root.join(path)) {
                Ok(source) => source,
                Err(_) => {
                    failures.push(format!("{}: anchor file `{path}` missing", rule.id));
                    continue;
                }
            };
            match source.lines().nth(cited_line - 1) {
                None => failures.push(format!(
                    "{}: anchor {path}:{cited_line} beyond end of file",
                    rule.id
                )),
                Some(line) if !line.contains(token) => failures.push(format!(
                    "{}: anchor {path}:{cited_line} drifted — expected `{token}`, line is `{}`",
                    rule.id,
                    line.trim()
                )),
                Some(_) => {}
            }
        }
        // Coverage: fixtures exist, or an explicit stub with an owner.
        if rule.fixtures.is_empty() && rule.stub_owner.is_none() {
            failures.push(format!(
                "{}: neither fixtures nor a stub owner (heading line {})",
                rule.id, rule.heading_line
            ));
        }
        for fixture in &rule.fixtures {
            if !root.join(fixture).exists() {
                failures.push(format!("{}: fixture `{fixture}` missing", rule.id));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} contract check failure(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn kernel_surface_ledger_rows_link_to_existing_rules() {
    let root = workspace_root();
    let contract = fs::read_to_string(root.join("KERNEL_CONTRACT.md")).expect("contract exists");
    let (rules, _) = parse_rules(&contract);
    let ids: BTreeSet<&str> = rules.iter().map(|r| r.id.as_str()).collect();

    let ledger_text = fs::read_to_string(root.join("ci/PARITY_LEDGER.txt")).expect("ledger exists");
    let ledger = fln_conformance::ledger::parse(&ledger_text).expect("ledger parses");
    for row in &ledger.rows {
        if row.surface == "kernel" {
            assert!(
                ids.contains(row.symbol.as_str()),
                "kernel ledger row `{}` does not name an existing KR- rule id",
                row.symbol
            );
        }
    }
}

#[test]
fn the_checker_detects_planted_drift_and_gaps() {
    // Planted drift: an anchor whose expect token is not on the cited line.
    let planted = "### KR-999 · planted\nanchor: SUITE.lock:1 (nowhere) expect=\"no-such-token\"\nfixtures: stub owner=fln-test\n";
    let (rules, problems) = parse_rules(planted);
    assert!(problems.is_empty());
    assert_eq!(rules.len(), 1);
    let root = workspace_root();
    let source = fs::read_to_string(root.join("SUITE.lock")).expect("exists");
    let line = source.lines().next().expect("non-empty");
    assert!(!line.contains("no-such-token"), "drift would be detected");

    // Planted gap: a rule with neither fixtures nor stub.
    let gap = "### KR-998 · gap\nanchor: SUITE.lock:1 (x) expect=\"SUITE\"\n";
    let (rules, _) = parse_rules(gap);
    assert!(rules[0].fixtures.is_empty() && rules[0].stub_owner.is_none());

    // Malformed stub: owner required.
    let bad_stub = "### KR-997 · bad\nfixtures: stub owner=\n";
    let (_, problems) = parse_rules(bad_stub);
    assert!(problems.iter().any(|p| p.contains("stub without an owner")));
}
