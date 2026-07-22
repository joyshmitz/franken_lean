//! Human and robot (NDJSON) rendering. Robot output is line-oriented, schema-versioned,
//! deterministic (findings pre-sorted by the checker), and never mixed with human
//! decoration (AGENTS.md, Agent Ergonomics).

use crate::NDJSON_SCHEMA;
use crate::checks::{Finding, RunOutcome};

/// FNV-1a 64-bit — a dependency-free content digest for run provenance. Labeled as
/// `fnv1a64` in output; not a cryptographic hash (fln-hash owns those, later).
pub fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

pub fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

pub fn render_human(root_display: &str, outcome: &RunOutcome) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "structure-guard: root={root_display} crates={} edges={} graph-digest=fnv1a64:{:016x}\n",
        outcome.crate_count, outcome.edge_count, outcome.graph_digest
    ));
    for f in &outcome.findings {
        out.push_str(&format!("{} {}: {}\n", f.code, f.path, f.detail));
    }
    out.push_str(&format!(
        "structure-guard: {} — {} finding(s)\n",
        if outcome.findings.is_empty() {
            "PASS"
        } else {
            "FAIL"
        },
        outcome.findings.len()
    ));
    out
}

fn finding_ndjson(f: &Finding) -> String {
    format!(
        "{{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"finding\",\"code\":\"{}\",\"severity\":\"error\",\"path\":\"{}\",\"detail\":\"{}\"}}",
        json_escape(f.code),
        json_escape(&f.path),
        json_escape(&f.detail)
    )
}

pub fn render_ndjson(root_display: &str, outcome: &RunOutcome, duration_ms: u128) -> String {
    let mut lines = Vec::with_capacity(outcome.findings.len() + 2);
    lines.push(format!(
        "{{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_start\",\"root\":\"{}\",\"graph_digest\":\"fnv1a64:{:016x}\",\"crates\":{},\"edges\":{}}}",
        json_escape(root_display),
        outcome.graph_digest,
        outcome.crate_count,
        outcome.edge_count
    ));
    lines.extend(outcome.findings.iter().map(finding_ndjson));
    lines.push(format!(
        "{{\"schema\":\"{NDJSON_SCHEMA}\",\"event\":\"run_end\",\"verdict\":\"{}\",\"findings\":{},\"duration_ms\":{duration_ms}}}",
        if outcome.findings.is_empty() {
            "pass"
        } else {
            "fail"
        },
        outcome.findings.len()
    ));
    lines.join("\n") + "\n"
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fnv_vectors() {
        assert_eq!(fnv1a64(b""), 0xcbf29ce484222325);
        assert_eq!(fnv1a64(b"a"), 0xaf63dc4c8601ec8c);
    }

    #[test]
    fn escaping() {
        assert_eq!(json_escape("a\"b\\c\nd"), "a\\\"b\\\\c\\nd");
    }
}
