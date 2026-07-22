//! Minimal parser for this workspace's constrained Cargo.toml style.
//!
//! The guard does not embed a general TOML parser (the universe is closed, D1); it
//! parses exactly the uniform manifest shape the workspace uses and reports anything
//! else as a finding rather than guessing. Supported: `[package]` with `name`/`edition`,
//! the three dependency sections with single-line entries, and passively ignored
//! `[features]`/`[lib]`/`[[bin]]`/`[profile.*]` sections.

#[derive(Debug)]
pub struct Dep {
    pub name: String,
    /// Section the dependency was declared in (`dependencies`, `dev-dependencies`,
    /// `build-dependencies`). All sections are held to the same closed-universe rule
    /// until SUITE.lock introduces per-policy tracking (D1).
    pub section: String,
    /// Whether the entry carries a `path = "..."` key.
    pub has_path: bool,
}

#[derive(Debug)]
pub struct Manifest {
    pub name: String,
    pub edition: String,
    pub deps: Vec<Dep>,
}

const DEP_SECTIONS: [&str; 3] = ["dependencies", "dev-dependencies", "build-dependencies"];
const IGNORED_SECTIONS: [&str; 3] = ["features", "lib", "bin"];

fn unquote(v: &str) -> Option<&str> {
    v.strip_prefix('"')?.strip_suffix('"')
}

pub fn parse(text: &str, display_path: &str) -> Result<Manifest, String> {
    let mut name: Option<String> = None;
    let mut edition: Option<String> = None;
    let mut deps: Vec<Dep> = Vec::new();
    let mut section: Option<String> = None;

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
        let err = |msg: &str| format!("{display_path}:{lineno}: {msg}: `{line}`");

        if line.starts_with('[') {
            let inner = line
                .trim_start_matches('[')
                .trim_end_matches(']')
                .to_string();
            let known = inner == "package"
                || DEP_SECTIONS.contains(&inner.as_str())
                || IGNORED_SECTIONS.contains(&inner.as_str())
                || inner.starts_with("profile");
            if !known {
                // Anything unrecognized that could smuggle dependencies (target-specific
                // tables, patch/replace) is rejected, not skipped.
                return Err(err("unsupported manifest section"));
            }
            section = Some(inner);
            continue;
        }

        match section.as_deref() {
            Some("package") => {
                if let Some((k, v)) = line.split_once('=') {
                    let (k, v) = (k.trim(), v.trim());
                    match k {
                        "name" => {
                            name = Some(
                                unquote(v)
                                    .ok_or_else(|| err("name must be a quoted string"))?
                                    .to_string(),
                            );
                        }
                        "edition" => {
                            edition = Some(
                                unquote(v)
                                    .ok_or_else(|| err("edition must be a quoted string"))?
                                    .to_string(),
                            );
                        }
                        _ => {} // version, license, publish, …
                    }
                } else {
                    return Err(err("expected `key = value`"));
                }
            }
            Some(s) if DEP_SECTIONS.contains(&s) => {
                let (key, value) = line
                    .split_once('=')
                    .ok_or_else(|| err("expected `<dep> = <spec>`"))?;
                let dep_name = key.trim().split('.').next().unwrap_or("").to_string();
                if dep_name.is_empty()
                    || !dep_name
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_')
                {
                    return Err(err("invalid dependency name"));
                }
                let value = value.trim();
                if value.ends_with('{') || (value.contains('{') && !value.contains('}')) {
                    return Err(err("multi-line dependency tables are not supported"));
                }
                let has_path = value.contains("path");
                if key.contains("workspace") || value.contains("workspace") {
                    return Err(err("workspace-inherited dependencies are not supported"));
                }
                deps.push(Dep {
                    name: dep_name,
                    section: s.to_string(),
                    has_path,
                });
            }
            Some(_) => {} // ignored sections
            None => return Err(err("content before any section header")),
        }
    }

    Ok(Manifest {
        name: name.ok_or_else(|| format!("{display_path}: missing package.name"))?,
        edition: edition.ok_or_else(|| format!("{display_path}: missing package.edition"))?,
        deps,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const OK: &str = "[package]\nname = \"fln-core\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\n[dependencies]\n";

    #[test]
    fn parses_stub_manifest() {
        let m = parse(OK, "t").expect("parses");
        assert_eq!(m.name, "fln-core");
        assert_eq!(m.edition, "2024");
        assert!(m.deps.is_empty());
    }

    #[test]
    fn parses_path_and_version_deps() {
        let text = format!(
            "{OK}fln-core = {{ path = \"../fln-core\" }}\nserde = \"1\"\n\n[dev-dependencies]\nfln-hash = {{ path = \"../fln-hash\" }}\n"
        );
        let m = parse(&text, "t").expect("parses");
        assert_eq!(m.deps.len(), 3);
        assert!(m.deps[0].has_path);
        assert!(!m.deps[1].has_path);
        assert_eq!(m.deps[2].section, "dev-dependencies");
    }

    #[test]
    fn rejects_unknown_sections_and_workspace_inheritance() {
        assert!(parse("[patch.crates-io]\nx = \"1\"\n", "t").is_err());
        assert!(parse("[target.'cfg(unix)'.dependencies]\nlibc = \"1\"\n", "t").is_err());
        let ws = format!("{OK}serde.workspace = true\n");
        assert!(parse(&ws, "t").is_err());
    }

    #[test]
    fn features_section_is_ignored() {
        let text = format!("{OK}\n[features]\niron = []\n");
        let m = parse(&text, "t").expect("parses");
        assert!(m.deps.is_empty());
    }
}
