//! Verdicts and the resource algebra slice (plan §8.2b/§8.2c; bead franken_lean-zht).
//!
//! The kernel's one authority speaks in exactly these values. FL-INV-07 is
//! structural: [`Verdict::Inconclusive`] is a distinct arm carrying a consumption
//! profile; nothing converts it to or from [`Verdict::Rejected`], and no caller can
//! observe exhaustion as a judgment about the term.
//!
//! Bootstrap slice: receipts and the full typestate envelope (§8.2b) are follow-up
//! slices recorded on the bead; the verdict shape and the budget discipline are
//! final.

/// Stable rejection classes — cross-release comparable, KERNEL_CONTRACT-aligned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RejectClass {
    /// KR-100: loose bound variables reach the kernel.
    LooseBVar,
    /// KR-103: a metavariable reaches the kernel.
    MVarInKernel,
    /// KR-102: unknown free variable.
    UnknownFVar,
    /// KR-105: unknown constant, or level-arity mismatch.
    UnknownConstant,
    UniverseArityMismatch,
    /// KR-140-class: an undeclared universe parameter.
    UndefinedLevelParam,
    /// KR-106: the head of an application is not a function.
    FunctionExpected,
    /// KR-106/KR-109: an argument/value type failed defeq against the expected type.
    TypeMismatch,
    /// KR-107/108/109: a binder domain (or let type) is not a sort.
    SortExpected,
    /// KR-112: an ill-formed projection.
    InvalidProjection,
    /// KR-970: the one-name-one-constant law.
    AlreadyDeclared,
    /// KR-971: duplicate universe parameters.
    DuplicateLevelParams,
    /// KR-974: a theorem whose type is not a proposition.
    TheoremNotProp,
    /// The declared type and inferred body type are not defeq (KR-974).
    DefinitionTypeMismatch,
    /// The two sides are simply not definitionally equal (defeq query verdict).
    NotDefEq,
    /// KR-973 (pin type_checker.cpp:101/105): a non-unsafe context referenced an
    /// unsafe declaration, or a safe context referenced a partial definition.
    SafetyViolation,
    /// KR-6xx/95x/97x: a decoded declaration-block observable (flag, count,
    /// name list, generated recursor) does not match the kernel's own
    /// regeneration from the declaration.
    BlockMismatch,
}

impl RejectClass {
    pub fn as_str(self) -> &'static str {
        match self {
            RejectClass::LooseBVar => "loose_bvar",
            RejectClass::MVarInKernel => "mvar_in_kernel",
            RejectClass::UnknownFVar => "unknown_fvar",
            RejectClass::UnknownConstant => "unknown_constant",
            RejectClass::UniverseArityMismatch => "universe_arity_mismatch",
            RejectClass::UndefinedLevelParam => "undefined_level_param",
            RejectClass::FunctionExpected => "function_expected",
            RejectClass::TypeMismatch => "type_mismatch",
            RejectClass::SortExpected => "sort_expected",
            RejectClass::InvalidProjection => "invalid_projection",
            RejectClass::AlreadyDeclared => "already_declared",
            RejectClass::DuplicateLevelParams => "duplicate_level_params",
            RejectClass::TheoremNotProp => "theorem_not_prop",
            RejectClass::DefinitionTypeMismatch => "definition_type_mismatch",
            RejectClass::NotDefEq => "not_def_eq",
            RejectClass::SafetyViolation => "safety_violation",
            RejectClass::BlockMismatch => "block_mismatch",
        }
    }
}

/// The typed budget the caller hands the kernel (§8.2c slice: reduction/inference
/// steps and traversal depth). Exhaustion is a verdict about the run (KR-403).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Budget {
    /// Counted work steps (inference nodes + reduction steps + defeq queries).
    pub steps: u64,
    /// Maximum traversal depth — the recursion bound that makes host traversal
    /// safe over attacker-controlled terms (well below stack capacity).
    pub depth: u32,
}

impl Budget {
    /// A generous default for interactive checking; callers with real budgets
    /// pass their own.
    pub const DEFAULT: Budget = Budget {
        steps: 10_000_000,
        depth: 4_096,
    };
}

/// What a run actually consumed — attached to every verdict, so exhaustion
/// diagnoses itself (§8.2c).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Consumption {
    pub steps_used: u64,
    pub max_depth: u32,
}

/// Why a run could not finish (FL-INV-07: never a judgment about the term).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExhaustionReason {
    Steps,
    Depth,
}

/// The kernel's answer. Exactly one of these; no other channel exists.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// The declaration is admitted. (Receipts: follow-up slice.)
    Accepted { consumption: Consumption },
    /// A real negative judgment about the term.
    Rejected {
        class: RejectClass,
        message: String,
        consumption: Consumption,
    },
    /// The run exhausted its budget — a verdict about the RUN. Never rendered as,
    /// cached as, or promoted to acceptance or rejection.
    Inconclusive {
        reason: ExhaustionReason,
        consumption: Consumption,
    },
}

impl Verdict {
    pub fn is_accepted(&self) -> bool {
        matches!(self, Verdict::Accepted { .. })
    }

    pub fn is_rejected(&self) -> bool {
        matches!(self, Verdict::Rejected { .. })
    }

    pub fn is_inconclusive(&self) -> bool {
        matches!(self, Verdict::Inconclusive { .. })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_three_arms_are_disjoint_observables() {
        let consumption = Consumption::default();
        let accepted = Verdict::Accepted { consumption };
        let rejected = Verdict::Rejected {
            class: RejectClass::TypeMismatch,
            message: "x".into(),
            consumption,
        };
        let inconclusive = Verdict::Inconclusive {
            reason: ExhaustionReason::Steps,
            consumption,
        };
        assert!(accepted.is_accepted() && !accepted.is_rejected() && !accepted.is_inconclusive());
        assert!(rejected.is_rejected() && !rejected.is_accepted() && !rejected.is_inconclusive());
        assert!(
            inconclusive.is_inconclusive()
                && !inconclusive.is_accepted()
                && !inconclusive.is_rejected(),
            "FL-INV-07: exhaustion is neither acceptance nor rejection"
        );
    }

    #[test]
    fn reject_classes_are_stable_strings() {
        let mut seen = std::collections::BTreeSet::new();
        for class in [
            RejectClass::LooseBVar,
            RejectClass::MVarInKernel,
            RejectClass::UnknownFVar,
            RejectClass::UnknownConstant,
            RejectClass::UniverseArityMismatch,
            RejectClass::UndefinedLevelParam,
            RejectClass::FunctionExpected,
            RejectClass::TypeMismatch,
            RejectClass::SortExpected,
            RejectClass::InvalidProjection,
            RejectClass::AlreadyDeclared,
            RejectClass::DuplicateLevelParams,
            RejectClass::TheoremNotProp,
            RejectClass::DefinitionTypeMismatch,
            RejectClass::NotDefEq,
            RejectClass::SafetyViolation,
            RejectClass::BlockMismatch,
        ] {
            assert!(seen.insert(class.as_str()), "duplicate class string");
        }
    }
}
