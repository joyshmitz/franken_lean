//! The `ORACLE_FALLBACK` poison machinery (plan §18.10, D8; bead fln-euo).
//!
//! This module exists ONLY under the `oracle-fallback-dev` feature, which is never a
//! default and is compiled out of releases (the compile-out check lives in
//! `tests/poison_compile_out.rs` and in the workspace-wide grep test). Every product
//! of the development-only lockstep harness is wrapped here: poisoned values render
//! with the tag, are cache-inadmissible, and satisfy no gate.

/// The poison tag. Its appearance anywhere outside fln-conformance is a CI failure.
pub const POISON_TAG: &str = "ORACLE_FALLBACK";

/// A value produced with Reference assistance during lockstep diagnosis. It cannot
/// be unwrapped silently: every access path names the poison.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleFallback<T> {
    value: T,
}

impl<T> OracleFallback<T> {
    pub fn poison(value: T) -> OracleFallback<T> {
        OracleFallback { value }
    }

    /// The only way out, named after what it is. Call sites read as what they do:
    /// `use_poisoned_diagnosis_value_gate_inert()`.
    pub fn use_poisoned_diagnosis_value_gate_inert(self) -> T {
        self.value
    }

    /// Poisoned values may never become cache keys or receipts.
    pub fn cache_admissible(&self) -> bool {
        false
    }
}

impl<T: std::fmt::Display> std::fmt::Display for OracleFallback<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{POISON_TAG}] {}", self.value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn poison_renders_the_tag_and_is_cache_inadmissible() {
        let poisoned = OracleFallback::poison(42u32);
        assert!(format!("{poisoned}").contains(POISON_TAG));
        assert!(!poisoned.cache_admissible());
        assert_eq!(poisoned.use_poisoned_diagnosis_value_gate_inert(), 42);
    }
}
