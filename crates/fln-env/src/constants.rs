//! The constant-declaration model (plan §7.1), mirroring the pin's `ConstantInfo`
//! shape field-for-field so metaprograms observe the same structure.
//!
//! Semantics anchors (vendor/lean4-src at the SUITE.lock pin,
//! src/Lean/Declaration.lean): `ConstantVal` (:95), `AxiomVal` (:101),
//! `ReducibilityHints` (:46), `DefinitionSafety` (:116), `DefinitionVal` (:120),
//! `TheoremVal` (:142), `OpaqueVal` (:156), `InductiveVal` (:261),
//! `ConstructorVal` (:328), `RecursorRule` (:348), `RecursorVal` (:357),
//! `QuotKind`/`QuotVal` (:410-427), `ConstantInfo` (:429).
//!
//! Counts use `u32` (they are structural arities); the codec beads own the
//! decode-time range guards. Byte-level olean parity for these structures is proven
//! at G0-1 against the extracted `OLEAN_CONTRACT.md`, not asserted here.

use fln_core::expr::Expr;
use fln_core::name::Name;

/// `ConstantVal` (Declaration.lean:95-99): the fields every constant carries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub type_: Expr,
}

/// `ReducibilityHints` (Declaration.lean:46-50).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityHints {
    Opaque,
    Abbrev,
    Regular(u32),
}

impl ReducibilityHints {
    /// `ReducibilityHints.getHeightEx` (Declaration.lean:56-60): non-regular is 0.
    pub fn height(self) -> u32 {
        match self {
            ReducibilityHints::Regular(h) => h,
            _ => 0,
        }
    }
}

/// `DefinitionSafety` (Declaration.lean:116-118).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial,
}

/// `AxiomVal` (Declaration.lean:101-103).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AxiomVal {
    pub base: ConstantVal,
    pub is_unsafe: bool,
}

/// `DefinitionVal` (Declaration.lean:120-136).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefinitionVal {
    pub base: ConstantVal,
    pub value: Expr,
    pub hints: ReducibilityHints,
    pub safety: DefinitionSafety,
    /// All declarations in the same mutual block (including this one).
    pub all: Vec<Name>,
}

/// `TheoremVal` (Declaration.lean:142-148).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoremVal {
    pub base: ConstantVal,
    pub value: Expr,
    pub all: Vec<Name>,
}

/// `OpaqueVal` (Declaration.lean:156-163).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpaqueVal {
    pub base: ConstantVal,
    pub value: Expr,
    pub is_unsafe: bool,
    pub all: Vec<Name>,
}

/// `InductiveVal` (Declaration.lean:261-300).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveVal {
    pub base: ConstantVal,
    pub num_params: u32,
    pub num_indices: u32,
    /// All inductive types in the mutual declaration (including this one).
    pub all: Vec<Name>,
    pub ctors: Vec<Name>,
    pub num_nested: u32,
    pub is_rec: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}

/// `ConstructorVal` (Declaration.lean:328-338).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorVal {
    pub base: ConstantVal,
    pub induct: Name,
    pub cidx: u32,
    pub num_params: u32,
    pub num_fields: u32,
    pub is_unsafe: bool,
}

/// `RecursorRule` (Declaration.lean:348-354).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorRule {
    pub ctor: Name,
    pub nfields: u32,
    pub rhs: Expr,
}

/// `RecursorVal` (Declaration.lean:357-380).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorVal {
    pub base: ConstantVal,
    pub all: Vec<Name>,
    pub num_params: u32,
    pub num_indices: u32,
    pub num_motives: u32,
    pub num_minors: u32,
    pub rules: Vec<RecursorRule>,
    pub k: bool,
    pub is_unsafe: bool,
}

/// `QuotKind` (Declaration.lean:410-415).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

/// `QuotVal` (Declaration.lean:417-419).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuotVal {
    pub base: ConstantVal,
    pub kind: QuotKind,
}

/// `ConstantInfo` (Declaration.lean:429-438): the eight constant kinds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstantInfo {
    Axiom(AxiomVal),
    Defn(DefinitionVal),
    Thm(TheoremVal),
    Opaque(OpaqueVal),
    Quot(QuotVal),
    Induct(InductiveVal),
    Ctor(ConstructorVal),
    Rec(RecursorVal),
}

impl ConstantInfo {
    /// `ConstantInfo.toConstantVal` (Declaration.lean:441-449).
    pub fn constant_val(&self) -> &ConstantVal {
        match self {
            ConstantInfo::Axiom(v) => &v.base,
            ConstantInfo::Defn(v) => &v.base,
            ConstantInfo::Thm(v) => &v.base,
            ConstantInfo::Opaque(v) => &v.base,
            ConstantInfo::Quot(v) => &v.base,
            ConstantInfo::Induct(v) => &v.base,
            ConstantInfo::Ctor(v) => &v.base,
            ConstantInfo::Rec(v) => &v.base,
        }
    }

    pub fn name(&self) -> &Name {
        &self.constant_val().name
    }

    /// Stable kind name, exhaustively matched (taxonomy discipline: adding a kind
    /// breaks every consumer until handled).
    pub fn kind_name(&self) -> &'static str {
        match self {
            ConstantInfo::Axiom(_) => "axiom",
            ConstantInfo::Defn(_) => "definition",
            ConstantInfo::Thm(_) => "theorem",
            ConstantInfo::Opaque(_) => "opaque",
            ConstantInfo::Quot(_) => "quotient",
            ConstantInfo::Induct(_) => "inductive",
            ConstantInfo::Ctor(_) => "constructor",
            ConstantInfo::Rec(_) => "recursor",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::level::Level;

    fn n(s: &str) -> Name {
        Name::str(Name::anonymous(), s)
    }

    fn base(name: &str) -> ConstantVal {
        ConstantVal {
            name: n(name),
            level_params: vec![n("u")],
            type_: Expr::sort(Level::param(n("u"))),
        }
    }

    #[test]
    fn all_eight_kinds_expose_their_base_and_kind_name() {
        let cases: Vec<ConstantInfo> = vec![
            ConstantInfo::Axiom(AxiomVal {
                base: base("ax"),
                is_unsafe: false,
            }),
            ConstantInfo::Defn(DefinitionVal {
                base: base("d"),
                value: Expr::sort(Level::zero()),
                hints: ReducibilityHints::Regular(3),
                safety: DefinitionSafety::Safe,
                all: vec![n("d")],
            }),
            ConstantInfo::Thm(TheoremVal {
                base: base("t"),
                value: Expr::sort(Level::zero()),
                all: vec![n("t")],
            }),
            ConstantInfo::Opaque(OpaqueVal {
                base: base("o"),
                value: Expr::sort(Level::zero()),
                is_unsafe: false,
                all: vec![n("o")],
            }),
            ConstantInfo::Quot(QuotVal {
                base: base("q"),
                kind: QuotKind::Lift,
            }),
            ConstantInfo::Induct(InductiveVal {
                base: base("i"),
                num_params: 1,
                num_indices: 0,
                all: vec![n("i")],
                ctors: vec![n("mk")],
                num_nested: 0,
                is_rec: false,
                is_unsafe: false,
                is_reflexive: false,
            }),
            ConstantInfo::Ctor(ConstructorVal {
                base: base("mk"),
                induct: n("i"),
                cidx: 0,
                num_params: 1,
                num_fields: 2,
                is_unsafe: false,
            }),
            ConstantInfo::Rec(RecursorVal {
                base: base("rec"),
                all: vec![n("i")],
                num_params: 1,
                num_indices: 0,
                num_motives: 1,
                num_minors: 1,
                rules: vec![RecursorRule {
                    ctor: n("mk"),
                    nfields: 2,
                    rhs: Expr::sort(Level::zero()),
                }],
                k: false,
                is_unsafe: false,
            }),
        ];
        let mut kinds = std::collections::BTreeSet::new();
        for info in &cases {
            assert_eq!(info.constant_val().level_params.len(), 1);
            assert!(kinds.insert(info.kind_name()));
        }
        assert_eq!(kinds.len(), 8, "the eight constant kinds of §7.1");
    }

    #[test]
    fn reducibility_height_matches_the_pin_accessor() {
        assert_eq!(ReducibilityHints::Regular(7).height(), 7);
        assert_eq!(ReducibilityHints::Opaque.height(), 0);
        assert_eq!(ReducibilityHints::Abbrev.height(), 0);
    }
}
