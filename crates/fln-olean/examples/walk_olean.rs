//! walk_olean — robot-lane driver for the G0-1 region reader (bead
//! franken_lean-y24). Walks each `.olean` argument with full object-graph
//! integrity checking plus `ModuleData` decoding and emits one tab-separated
//! line per file:
//!
//!   `path <TAB> version <TAB> objects <TAB> imports <TAB> consts <TAB> ext_blocks <TAB> ext_entries <TAB> status`
//!
//! `status` is `ok` or `error:<typed reason>`. Exit code 0 iff every file
//! walked clean. stdout is data-only; diagnostics go to stderr.

#![forbid(unsafe_code)]

use std::process::ExitCode;

use fln_olean::region::{OleanView, WalkBudget};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        eprintln!("usage: walk_olean <file.olean> [...]");
        return ExitCode::from(2);
    }
    let budget = WalkBudget::default();
    let mut failures = 0u32;
    for path in &args {
        let line = match std::fs::read(path) {
            Err(e) => format!("{path}\t-\t-\t-\t-\t-\t-\terror:io:{e}"),
            Ok(bytes) => match walk_one(&bytes, budget) {
                Ok((version, objects, imports, consts, blocks, entries)) => format!(
                    "{path}\t{version}\t{objects}\t{imports}\t{consts}\t{blocks}\t{entries}\tok"
                ),
                Err(e) => format!("{path}\t-\t-\t-\t-\t-\t-\terror:{e}"),
            },
        };
        if line.ends_with("\tok") {
            println!("{line}");
        } else {
            println!("{line}");
            failures += 1;
        }
    }
    if failures > 0 {
        eprintln!("walk_olean: {failures}/{} files failed", args.len());
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

#[allow(clippy::type_complexity)]
fn walk_one(
    bytes: &[u8],
    budget: WalkBudget,
) -> Result<(u8, u64, usize, u64, usize, u64), fln_olean::region::RegionError> {
    let view = OleanView::parse(bytes)?;
    let report = view.walk(budget)?;
    let md = view.module_data(budget)?;
    let entry_total: u64 = md.extensions.iter().map(|e| e.entries).sum();
    Ok((
        view.header.version,
        report.objects,
        md.imports.len(),
        md.constants,
        md.extensions.len(),
        entry_total,
    ))
}
