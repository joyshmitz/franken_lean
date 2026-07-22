//! The Parity-Ledger gate (bead fln-euo): the REAL ledger must parse, every cited
//! fixture must exist, and the aggregate view must be derivable — on every CI run.
//! A ledger that cites missing evidence is marketing and fails here.

#![forbid(unsafe_code)]

use std::path::Path;

use fln_conformance::ledger::{self, ClaimState, LLevel};

fn workspace_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
}

#[test]
fn the_real_ledger_parses_validates_and_aggregates() {
    let root = workspace_root();
    let text = std::fs::read_to_string(root.join("ci/PARITY_LEDGER.txt")).expect("ledger exists");
    let parsed = ledger::parse(&text).expect("ledger parses");
    assert!(!parsed.rows.is_empty(), "the ledger has rows");
    ledger::validate_fixtures(&parsed, root).expect("every cited fixture exists");

    let agg = ledger::aggregate(&parsed);
    assert_eq!(agg.total_rows, parsed.rows.len());
    // The bootstrap posture: the proven core observables sit at L2 OBSERVED.
    assert!(
        agg.by_surface_level
            .get(&("meta-api".to_string(), LLevel::L2))
            .copied()
            .unwrap_or(0)
            >= 5,
        "the p8a-proven observable rows are present at L2"
    );
    assert!(agg.by_claim.contains_key(&ClaimState::Observed));
}

#[test]
fn rows_above_l0_cite_real_evidence() {
    let root = workspace_root();
    let text = std::fs::read_to_string(root.join("ci/PARITY_LEDGER.txt")).expect("ledger exists");
    let parsed = ledger::parse(&text).expect("ledger parses");
    for row in &parsed.rows {
        if row.level > LLevel::L0 {
            assert!(
                !row.fixtures.is_empty(),
                "row `{}` is above L0 with no fixtures",
                row.symbol
            );
        }
    }
}
