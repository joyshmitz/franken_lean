//! The oracle-precedence ladder as data (plan §18, bead fln-euo): when evidence
//! sources disagree about what the Reference means, this order decides — and an
//! unclassified divergence blocks the claim, it never rounds up.

/// Evidence authorities, strongest first. `Ord`: a lower rank outranks a higher one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OracleAuthority {
    /// The type theory itself — soundness beats bug-parity (D23 carve-out).
    CoreTheory,
    /// What the pinned Reference binary observably does.
    ObservedBinaryBehavior,
    /// What the pinned sources and upstream tests say it should do.
    SourcesAndTests,
    /// What stable downstream ecosystems demonstrably depend on.
    StableDownstreamDependence,
    /// A documented, numbered divergence (Behavior Note).
    DocumentedDivergence,
    /// Not yet classified. Blocks every claim it touches.
    Unclassified,
}

impl OracleAuthority {
    /// The full ladder, strongest first — the data form rigs iterate for triage.
    pub const LADDER: [OracleAuthority; 6] = [
        OracleAuthority::CoreTheory,
        OracleAuthority::ObservedBinaryBehavior,
        OracleAuthority::SourcesAndTests,
        OracleAuthority::StableDownstreamDependence,
        OracleAuthority::DocumentedDivergence,
        OracleAuthority::Unclassified,
    ];

    /// Whether a divergence attributed to this authority blocks the surface's claim.
    pub fn blocks_claim(self) -> bool {
        self == OracleAuthority::Unclassified
    }

    /// Resolve a disagreement between two authorities: the stronger one governs.
    pub fn resolve(a: OracleAuthority, b: OracleAuthority) -> OracleAuthority {
        a.min(b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_ladder_is_strictly_ordered_and_complete() {
        for pair in OracleAuthority::LADDER.windows(2) {
            assert!(
                pair[0] < pair[1],
                "{:?} must outrank {:?}",
                pair[0],
                pair[1]
            );
        }
        assert_eq!(OracleAuthority::LADDER.len(), 6);
    }

    #[test]
    fn core_theory_beats_observed_behavior() {
        // The D23 carve-out: soundness beats bug-parity.
        assert_eq!(
            OracleAuthority::resolve(
                OracleAuthority::ObservedBinaryBehavior,
                OracleAuthority::CoreTheory
            ),
            OracleAuthority::CoreTheory
        );
    }

    #[test]
    fn only_unclassified_blocks() {
        for authority in OracleAuthority::LADDER {
            assert_eq!(
                authority.blocks_claim(),
                authority == OracleAuthority::Unclassified
            );
        }
    }
}
