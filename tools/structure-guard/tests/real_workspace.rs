//! The workspace-graph snapshot test (bead fln-8mj): the REAL repository must be
//! structurally clean against its reviewed acknowledgment files. Any new crate or
//! dependency edge fails this test until `ci/WORKSPACE_GRAPH.txt` is edited in the
//! same change — that edit is the review surface.

use std::path::Path;

#[test]
fn real_workspace_is_structurally_clean() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root");
    let outcome = structure_guard::checks::run(root).expect("structure-guard setup");
    assert!(
        outcome.findings.is_empty(),
        "structural findings against the real workspace:\n{}",
        structure_guard::report::render_human(&root.display().to_string(), &outcome)
    );
    assert!(
        outcome.crate_count > 0,
        "workspace discovery found no crates"
    );
}
