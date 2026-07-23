//! Parser for `ci/ABI_EXPORT_STATUS.txt` — the per-symbol status taxonomy of
//! the exported `lean_*` C surface (plan §6.5; bead franken_lean-83r).
//!
//! The C-ABI half of the no-admission export covenant: every `Linkage::Export`
//! symbol of the generated census carries exactly one reviewed status row —
//! `NativeSafe`, `RawPlatform`, `CompatWrapper`, `ReferenceSemanticAdapter`
//! (the implemented statuses), or `Unsupported` (with the owning bead). There
//! is no unclassified symbol. `support` rows cover non-census symbols the
//! pin's `LEAN_MIMALLOC` inlines link-demand from generated C (the mimalloc
//! membrane twins); they are always implemented — an unimplemented support
//! row would be a link hole, not a status.
//!
//! `tools/structure-guard` (FLN-STRUCT-026) joins these rows against the
//! census and against every `#[unsafe(export_name)]` site in the one crate
//! allowed to export (`fln-unsafe-abi`), both directions.

use std::fs;
use std::path::Path;

/// Statuses whose symbol must have exactly one export site.
pub const IMPLEMENTED_STATUSES: &[&str] = &[
    "NativeSafe",
    "RawPlatform",
    "CompatWrapper",
    "ReferenceSemanticAdapter",
];

#[derive(Debug)]
pub struct StatusRow {
    pub symbol: String,
    pub status: String,
    /// `support` rows are the non-census membrane symbols (mimalloc twins).
    pub support: bool,
    /// `extern` rows are runtime symbols outside `lean.h` that generated C
    /// declares itself — the `contracts/extern_census.tsv` universe (e.g.
    /// `lean_sorry`). They join export sites exactly like `row`s but must
    /// not shadow a `lean.h` census symbol.
    pub extern_row: bool,
}

impl StatusRow {
    pub fn implemented(&self) -> bool {
        IMPLEMENTED_STATUSES.contains(&self.status.as_str())
    }
}

#[derive(Debug, Default)]
pub struct ExportStatus {
    pub rows: Vec<StatusRow>,
}

fn valid_symbol(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

pub fn parse(text: &str) -> Result<ExportStatus, String> {
    let mut out = ExportStatus::default();
    let mut saw_schema = false;
    for (idx, raw) in text.lines().enumerate() {
        let lineno = idx + 1;
        let line = match raw.find('#') {
            Some(pos) => &raw[..pos],
            None => raw,
        }
        .trim();
        if line.is_empty() {
            continue;
        }
        let err = |msg: &str| format!("ABI_EXPORT_STATUS.txt:{lineno}: {msg}");
        if !saw_schema {
            if line == "schema fln-abi-export-status/1" {
                saw_schema = true;
                continue;
            }
            return Err(err(
                "first directive must be `schema fln-abi-export-status/1`",
            ));
        }
        let (support, extern_row, rest) = if let Some(rest) = line.strip_prefix("row ") {
            (false, false, rest)
        } else if let Some(rest) = line.strip_prefix("support ") {
            (true, false, rest)
        } else if let Some(rest) = line.strip_prefix("extern ") {
            (false, true, rest)
        } else {
            return Err(err(
                "expected `row <symbol> | <status> | <site-or-owner> | <evidence> | <notes>` (or `support …` / `extern …`)",
            ));
        };
        let fields: Vec<&str> = rest.split('|').map(str::trim).collect();
        if fields.len() != 5 {
            return Err(err("row must have exactly five '|'-separated fields"));
        }
        if fields.iter().any(|f| f.is_empty()) {
            return Err(err("every field must be non-empty"));
        }
        let symbol = fields[0];
        if !valid_symbol(symbol) {
            return Err(err("symbol must be a plain C identifier"));
        }
        let status = fields[1];
        if !IMPLEMENTED_STATUSES.contains(&status) && status != "Unsupported" {
            return Err(err(&format!(
                "unknown status `{status}` (§6.5: NativeSafe | RawPlatform | CompatWrapper | ReferenceSemanticAdapter | Unsupported)"
            )));
        }
        if support && status == "Unsupported" {
            return Err(err(
                "a `support` row cannot be Unsupported — support symbols exist because generated C link-demands them",
            ));
        }
        if out.rows.iter().any(|r| r.symbol == symbol) {
            return Err(err("duplicate symbol row"));
        }
        out.rows.push(StatusRow {
            symbol: symbol.to_string(),
            status: status.to_string(),
            support,
            extern_row,
        });
    }
    if !saw_schema {
        return Err("ABI_EXPORT_STATUS.txt: missing schema line".to_string());
    }
    Ok(out)
}

/// Load the file if present. `Ok(None)` when absent — legal only while no
/// crate carries an export-name site (the caller enforces that).
pub fn load(root: &Path, rel: &str) -> Result<Option<ExportStatus>, String> {
    let path = root.join(rel);
    if !path.is_file() {
        return Ok(None);
    }
    let text = fs::read_to_string(&path).map_err(|error| format!("cannot read {rel}: {error}"))?;
    parse(&text).map(Some)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_rows_and_rejects_bad_shapes() {
        let ok = "schema fln-abi-export-status/1\n\
                  row lean_alloc_object | CompatWrapper | crates/fln-unsafe-abi/src/export.rs | suite | membrane big path\n\
                  row lean_apply_1 | Unsupported | franken_lean-7xe | census | apply machinery\n\
                  support mi_free | RawPlatform | crates/fln-unsafe-abi/src/export.rs | suite | mimalloc twin\n";
        let api = parse(ok).expect("parses");
        assert_eq!(api.rows.len(), 3);
        assert!(api.rows[0].implemented());
        assert!(!api.rows[1].implemented());
        assert!(api.rows[2].support);

        assert!(parse("row lean_x | CompatWrapper | a | b | c\n").is_err());
        assert!(
            parse("schema fln-abi-export-status/1\nrow lean_x | Wat | a | b | c\n").is_err(),
            "unknown status rejected"
        );
        assert!(
            parse("schema fln-abi-export-status/1\nsupport mi_x | Unsupported | a | b | c\n")
                .is_err(),
            "unsupported support row rejected"
        );
        assert!(
            parse(
                "schema fln-abi-export-status/1\nrow lean_x | CompatWrapper | a | b | c\nrow lean_x | Unsupported | a | b | c\n"
            )
            .is_err(),
            "duplicate symbol rejected"
        );
        assert!(
            parse("schema fln-abi-export-status/1\nrow bad-sym | CompatWrapper | a | b | c\n")
                .is_err(),
            "non-identifier symbol rejected"
        );
        assert!(
            parse("schema fln-abi-export-status/1\nrow lean_x | CompatWrapper | a | b\n").is_err(),
            "four fields rejected"
        );
    }
}
