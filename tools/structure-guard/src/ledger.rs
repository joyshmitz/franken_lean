//! Parser for `ci/UNSAFE_LEDGER.txt` and the scanner for `#[allow(unsafe_code)]` sites.

use std::fs;
use std::path::Path;

#[derive(Debug)]
pub struct LedgerRow {
    pub id: String,
    /// Workspace-relative path ('/'-separated) of the file containing the site.
    pub path: String,
}

#[derive(Debug, Default)]
pub struct Ledger {
    pub rows: Vec<LedgerRow>,
}

fn valid_id(s: &str) -> bool {
    s.strip_prefix("FLN-UL-")
        .is_some_and(|d| !d.is_empty() && d.len() <= 6 && d.chars().all(|c| c.is_ascii_digit()))
}

pub fn parse(text: &str) -> Result<Ledger, String> {
    let mut ledger = Ledger::default();
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
        let err = |msg: &str| format!("UNSAFE_LEDGER.txt:{lineno}: {msg}");

        if !saw_schema {
            if line == "schema fln-unsafe-ledger/1" {
                saw_schema = true;
                continue;
            }
            return Err(err("first directive must be `schema fln-unsafe-ledger/1`"));
        }
        let Some(rest) = line.strip_prefix("row ") else {
            return Err(err("expected `row <id> | <path> | ... ` (six fields)"));
        };
        let fields: Vec<&str> = rest.split('|').map(str::trim).collect();
        if fields.len() != 6 {
            return Err(err("row must have exactly six '|'-separated fields"));
        }
        if !valid_id(fields[0]) {
            return Err(err("row id must match FLN-UL-NNNN"));
        }
        if fields.iter().any(|f| f.is_empty()) {
            return Err(err("every ledger field must be non-empty"));
        }
        if ledger.rows.iter().any(|r| r.id == fields[0]) {
            return Err(err("duplicate ledger row id"));
        }
        ledger.rows.push(LedgerRow {
            id: fields[0].to_string(),
            path: fields[1].to_string(),
        });
    }

    if !saw_schema {
        return Err("UNSAFE_LEDGER.txt: missing schema line".to_string());
    }
    Ok(ledger)
}

/// One `#[allow(unsafe_code)]` (or inner `#![allow(unsafe_code)]`) occurrence.
#[derive(Debug)]
pub struct AllowSite {
    /// Workspace-relative path, '/'-separated.
    pub path: String,
    pub line: usize,
    /// Ledger id from the `// UNSAFE-LEDGER: FLN-UL-NNNN` marker, if present on the
    /// same line or the nearest non-empty line above.
    pub id: Option<String>,
}

fn marker_id(line: &str) -> Option<String> {
    let pos = line.find("UNSAFE-LEDGER:")?;
    let rest = line[pos + "UNSAFE-LEDGER:".len()..].trim();
    let id: String = rest
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '-')
        .collect();
    if id.is_empty() { None } else { Some(id) }
}

/// Recursively scan every `.rs` file under `dir` for allow-sites. `rel_prefix` is the
/// workspace-relative path of `dir`.
pub fn scan_allow_sites(
    dir: &Path,
    rel_prefix: &str,
    out: &mut Vec<AllowSite>,
) -> Result<(), String> {
    let entries =
        fs::read_dir(dir).map_err(|e| format!("cannot read directory {rel_prefix}: {e}"))?;
    let mut entries: Vec<_> = entries
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| format!("cannot read directory {rel_prefix}: {e}"))?;
    entries.sort_by_key(|e| e.file_name());

    for entry in entries {
        let name = entry.file_name().to_string_lossy().into_owned();
        let rel = format!("{rel_prefix}/{name}");
        let path = entry.path();
        if path.is_dir() {
            scan_allow_sites(&path, &rel, out)?;
        } else if name.ends_with(".rs") {
            let text = fs::read_to_string(&path).map_err(|e| format!("cannot read {rel}: {e}"))?;
            let lines: Vec<&str> = text.lines().collect();
            for (i, line) in lines.iter().enumerate() {
                let code = line.trim_start();
                if code.starts_with("//") {
                    // Comments (including doc comments) may mention the attribute
                    // without declaring a site.
                    continue;
                }
                if !(code.contains("#[allow(unsafe_code)]")
                    || code.contains("#![allow(unsafe_code)]"))
                {
                    continue;
                }
                let mut id = marker_id(line);
                if id.is_none() {
                    // nearest non-empty line above
                    for above in lines[..i].iter().rev() {
                        if above.trim().is_empty() {
                            continue;
                        }
                        id = marker_id(above);
                        break;
                    }
                }
                out.push(AllowSite {
                    path: rel.clone(),
                    line: i + 1,
                    id,
                });
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_empty_ledger() {
        let l = parse("schema fln-unsafe-ledger/1\n# none\n").expect("parses");
        assert!(l.rows.is_empty());
    }

    #[test]
    fn parses_row_and_rejects_bad_rows() {
        let ok = "schema fln-unsafe-ledger/1\n\
                  row FLN-UL-0001 | crates/fln-unsafe-abi/src/lib.rs | layout law | rig T-1 | safe copy | no admission\n";
        let l = parse(ok).expect("parses");
        assert_eq!(l.rows.len(), 1);
        assert_eq!(l.rows[0].id, "FLN-UL-0001");

        assert!(parse("schema fln-unsafe-ledger/1\nrow BAD-1 | a | b | c | d | e\n").is_err());
        assert!(parse("schema fln-unsafe-ledger/1\nrow FLN-UL-1 | a | b | c | d\n").is_err());
        assert!(parse("schema fln-unsafe-ledger/1\nrow FLN-UL-1 | a |  | c | d | e\n").is_err());
        let dup = "schema fln-unsafe-ledger/1\n\
                   row FLN-UL-1 | a | b | c | d | e\nrow FLN-UL-1 | a | b | c | d | e\n";
        assert!(parse(dup).is_err());
    }

    #[test]
    fn marker_extraction() {
        assert_eq!(
            marker_id("// UNSAFE-LEDGER: FLN-UL-0042 layout"),
            Some("FLN-UL-0042".to_string())
        );
        assert_eq!(marker_id("no marker here"), None);
    }
}
