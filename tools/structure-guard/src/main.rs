//! CLI for the structural gate. See `lib.rs` for what is enforced.
//!
//! Usage: `structure-guard [--root <path>] [--robot]`
//! Exit codes: 0 = clean, 1 = findings, 2 = setup/parse failure at the root.

#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use structure_guard::{checks, report};

const USAGE: &str = "usage: structure-guard [--root <path>] [--robot]\n\
  --root <path>  workspace root to check (default: current directory)\n\
  --robot        NDJSON output (schema structure-guard/1) on stdout\n\
exit codes: 0 clean, 1 findings, 2 setup failure";

fn main() -> ExitCode {
    let mut root = PathBuf::from(".");
    let mut robot = false;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--root" => match args.next() {
                Some(p) => root = PathBuf::from(p),
                None => {
                    eprintln!("--root requires a path\n{USAGE}");
                    return ExitCode::from(2);
                }
            },
            "--robot" => robot = true,
            "--help" | "-h" => {
                println!("{USAGE}");
                return ExitCode::SUCCESS;
            }
            other => {
                eprintln!("unknown argument `{other}`\n{USAGE}");
                return ExitCode::from(2);
            }
        }
    }

    let started = Instant::now();
    let root_display = root.display().to_string();
    match checks::run(&root) {
        Ok(outcome) => {
            let clean = outcome.findings.is_empty();
            if robot {
                print!(
                    "{}",
                    report::render_ndjson(&root_display, &outcome, started.elapsed().as_millis())
                );
            } else {
                print!("{}", report::render_human(&root_display, &outcome));
            }
            if clean {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            }
        }
        Err(e) => {
            eprintln!("structure-guard: setup failure: {e}");
            ExitCode::from(2)
        }
    }
}
