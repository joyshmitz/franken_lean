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

use std::fs::File;
use std::io::{BufWriter, Write};
use std::process::ExitCode;

use fln_olean::format;
use fln_olean::region::ModuleImport;
use fln_olean::region::{OleanView, WalkBudget};

struct WalkOutcome {
    version: u8,
    objects: u64,
    imports: Vec<ModuleImport>,
    constants: u64,
    extension_blocks: usize,
    extension_entries: u64,
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let import_path = if args.first().map(String::as_str) == Some("--imports-tsv") {
        if args.len() < 3 {
            eprintln!("usage: walk_olean [--imports-tsv PATH] <file.olean> [...]");
            return ExitCode::from(2);
        }
        args.remove(0);
        Some(args.remove(0))
    } else {
        None
    };
    if args.is_empty() {
        eprintln!("usage: walk_olean [--imports-tsv PATH] <file.olean> [...]");
        return ExitCode::from(2);
    }
    let mut import_writer = match import_path {
        Some(path) => match File::options().write(true).create_new(true).open(&path) {
            Ok(file) => {
                let mut writer = BufWriter::new(file);
                if writeln!(writer, "# schema fln.olean-imports/1").is_err()
                    || writeln!(writer, "# pin {} {}", format::PIN_TAG, format::PIN_COMMIT).is_err()
                    || writeln!(
                        writer,
                        "# columns fixture index module import_all is_exported is_meta"
                    )
                    .is_err()
                {
                    eprintln!("walk_olean: cannot initialize import manifest {path}");
                    return ExitCode::FAILURE;
                }
                Some(writer)
            }
            Err(error) => {
                eprintln!("walk_olean: cannot create import manifest {path}: {error}");
                return ExitCode::FAILURE;
            }
        },
        None => None,
    };
    let budget = WalkBudget::default();
    let mut failures = 0u32;
    for path in &args {
        let line = match std::fs::read(path) {
            Err(e) => format!("{path}\t-\t-\t-\t-\t-\t-\terror:io:{e}"),
            Ok(bytes) => match walk_one(&bytes, budget) {
                Ok(outcome) => {
                    if let Some(writer) = import_writer.as_mut()
                        && let Err(error) = write_import_rows(writer, path, &outcome.imports)
                    {
                        eprintln!("walk_olean: cannot write import rows for {path}: {error}");
                        failures += 1;
                    }
                    format!(
                        "{path}\t{}\t{}\t{}\t{}\t{}\t{}\tok",
                        outcome.version,
                        outcome.objects,
                        outcome.imports.len(),
                        outcome.constants,
                        outcome.extension_blocks,
                        outcome.extension_entries
                    )
                }
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
    if let Some(mut writer) = import_writer
        && let Err(error) = writer.flush()
    {
        eprintln!("walk_olean: cannot flush import manifest: {error}");
        failures += 1;
    }
    if failures > 0 {
        eprintln!("walk_olean: {failures}/{} files failed", args.len());
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn walk_one(
    bytes: &[u8],
    budget: WalkBudget,
) -> Result<WalkOutcome, fln_olean::region::RegionError> {
    let view = OleanView::parse(bytes)?;
    let report = view.walk(budget)?;
    let md = view.module_data(budget)?;
    let entry_total: u64 = md.extensions.iter().map(|e| e.entries).sum();
    Ok(WalkOutcome {
        version: view.header.version,
        objects: report.objects,
        imports: md.imports,
        constants: md.constants,
        extension_blocks: md.extensions.len(),
        extension_entries: entry_total,
    })
}

fn write_import_rows(
    writer: &mut impl Write,
    path: &str,
    imports: &[ModuleImport],
) -> std::io::Result<()> {
    for (index, import) in imports.iter().enumerate() {
        writeln!(
            writer,
            "{}\t{index}\t{}\t{}\t{}\t{}",
            tsv_field(path),
            tsv_field(&import.module.to_display_string()),
            import.import_all,
            import.is_exported,
            import.is_meta
        )?;
    }
    Ok(())
}

fn tsv_field(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for character in value.chars() {
        match character {
            '\\' => escaped.push_str("\\\\"),
            '\t' => escaped.push_str("\\t"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            _ => escaped.push(character),
        }
    }
    escaped
}
