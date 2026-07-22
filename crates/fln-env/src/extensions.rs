//! The environment-extension registry (plan §7.1): every extension declares its
//! merge and checkpoint semantics **in a registry**, so branching and merging an
//! environment includes its extensions *by contract*, not by each author's memory.
//!
//! The honesty laws, structural here:
//! * an extension payload understood only as opaque bytes is preserved losslessly,
//!   is **flagged in provenance** ([`ExtensionState::provenance`] reports
//!   [`PayloadProvenance::Opaque`]), and **honestly blocks fine-grained
//!   invalidation** through it ([`ExtensionState::supports_fine_invalidation`] is
//!   `false`) — never guessed safe;
//! * import-time replay preserves the Reference's entry ordering exactly: entries
//!   are an append-only journal, and replay yields them in recorded order.

use std::sync::Arc;

use fln_core::name::Name;

/// Declared merge semantics for one extension — the contract branch/merge consults.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MergeSemantics {
    /// Entries concatenate in branch order (the common upstream replay shape).
    AppendOrdered,
    /// Entries form a set keyed by their bytes; duplicates collapse.
    SetUnion,
    /// The extension cannot be merged automatically; a branch merge touching it is
    /// a semantic conflict surfaced to the caller (plan §15.3b), never silent.
    ConflictsRequireReview,
}

/// Declared checkpoint semantics: what a snapshot must capture.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckpointSemantics {
    /// The journal suffix since the base commit fully describes the state.
    JournalSuffix,
    /// The full journal must be captured (state is order-sensitive beyond suffixes).
    FullJournal,
}

/// How well the toolchain understands a payload — provenance, not a guess.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PayloadProvenance {
    /// The payload schema is native-understood; fine-grained invalidation may see
    /// through it.
    Understood,
    /// Opaque bytes: preserved losslessly, flagged, and conservatively blocking.
    Opaque,
}

/// One registered extension: identity plus declared contracts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionDescriptor {
    pub name: Name,
    pub merge: MergeSemantics,
    pub checkpoint: CheckpointSemantics,
    pub provenance: PayloadProvenance,
}

/// One replay entry: bytes as imported, order-significant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionEntry {
    pub payload: Arc<[u8]>,
}

/// The state of one extension inside an environment: its descriptor plus the
/// append-only entry journal. Cloning is cheap (shared journal tail via `Arc`s in
/// the persistent environment map).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionState {
    pub descriptor: ExtensionDescriptor,
    entries: Vec<ExtensionEntry>,
}

impl ExtensionState {
    pub fn new(descriptor: ExtensionDescriptor) -> ExtensionState {
        ExtensionState {
            descriptor,
            entries: Vec::new(),
        }
    }

    /// Append one imported entry (replay order is the Reference's order).
    pub fn push_entry(&self, payload: impl Into<Arc<[u8]>>) -> ExtensionState {
        let mut next = self.clone();
        next.entries.push(ExtensionEntry {
            payload: payload.into(),
        });
        next
    }

    /// Entries in exact recorded order — replay IS iteration.
    pub fn entries(&self) -> &[ExtensionEntry] {
        &self.entries
    }

    pub fn provenance(&self) -> PayloadProvenance {
        self.descriptor.provenance
    }

    /// Fine-grained invalidation may only see through understood payloads; opaque
    /// ones block conservatively (plan §7.1: honestly blocks, never guessed safe).
    pub fn supports_fine_invalidation(&self) -> bool {
        self.descriptor.provenance == PayloadProvenance::Understood
    }

    /// Merge `ours` and `theirs` (both derived from `self` as the common base)
    /// under the DECLARED semantics. Returns `Err` with the extension name when the
    /// contract says the merge needs review — a typed conflict, never a silent
    /// union.
    pub fn merge(
        base: &ExtensionState,
        ours: &ExtensionState,
        theirs: &ExtensionState,
    ) -> Result<ExtensionState, MergeConflict> {
        debug_assert_eq!(base.descriptor, ours.descriptor);
        debug_assert_eq!(base.descriptor, theirs.descriptor);
        match base.descriptor.merge {
            MergeSemantics::AppendOrdered => {
                let mut merged = ours.clone();
                for entry in theirs.entries.iter().skip(base.entries.len()) {
                    merged.entries.push(entry.clone());
                }
                Ok(merged)
            }
            MergeSemantics::SetUnion => {
                let mut merged = ours.clone();
                for entry in theirs.entries.iter().skip(base.entries.len()) {
                    if !merged.entries.contains(entry) {
                        merged.entries.push(entry.clone());
                    }
                }
                Ok(merged)
            }
            MergeSemantics::ConflictsRequireReview => {
                let ours_changed = ours.entries.len() != base.entries.len();
                let theirs_changed = theirs.entries.len() != base.entries.len();
                if ours_changed && theirs_changed {
                    Err(MergeConflict {
                        extension: base.descriptor.name.clone(),
                    })
                } else if theirs_changed {
                    Ok(theirs.clone())
                } else {
                    Ok(ours.clone())
                }
            }
        }
    }
}

/// A typed semantic-merge conflict (plan §15.3b: blocked and explained, the failure
/// mode Git cannot even see).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MergeConflict {
    pub extension: Name,
}

impl std::fmt::Display for MergeConflict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "extension `{}` declares conflicts-require-review merge semantics and both branches changed it",
            self.extension.to_display_string()
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn descriptor(merge: MergeSemantics, provenance: PayloadProvenance) -> ExtensionDescriptor {
        ExtensionDescriptor {
            name: Name::str(Name::anonymous(), "simpExt"),
            merge,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance,
        }
    }

    fn bytes(v: &[u8]) -> Arc<[u8]> {
        Arc::from(v.to_vec().into_boxed_slice())
    }

    #[test]
    fn replay_preserves_exact_recorded_order() {
        let state = ExtensionState::new(descriptor(
            MergeSemantics::AppendOrdered,
            PayloadProvenance::Understood,
        ))
        .push_entry(bytes(b"a"))
        .push_entry(bytes(b"b"))
        .push_entry(bytes(b"c"));
        let replayed: Vec<&[u8]> = state.entries().iter().map(|e| &*e.payload).collect();
        assert_eq!(replayed, vec![b"a".as_slice(), b"b", b"c"]);
    }

    #[test]
    fn opaque_payloads_are_lossless_flagged_and_block_invalidation() {
        let opaque = ExtensionState::new(descriptor(
            MergeSemantics::AppendOrdered,
            PayloadProvenance::Opaque,
        ))
        .push_entry(bytes(&[0xde, 0xad, 0xbe, 0xef]));
        assert_eq!(&*opaque.entries()[0].payload, &[0xde, 0xad, 0xbe, 0xef]);
        assert_eq!(opaque.provenance(), PayloadProvenance::Opaque);
        assert!(!opaque.supports_fine_invalidation(), "never guessed safe");
        let understood = ExtensionState::new(descriptor(
            MergeSemantics::AppendOrdered,
            PayloadProvenance::Understood,
        ));
        assert!(understood.supports_fine_invalidation());
    }

    #[test]
    fn merge_follows_the_declared_contract() {
        let base = ExtensionState::new(descriptor(
            MergeSemantics::AppendOrdered,
            PayloadProvenance::Understood,
        ))
        .push_entry(bytes(b"base"));
        let ours = base.push_entry(bytes(b"ours"));
        let theirs = base.push_entry(bytes(b"theirs"));
        let merged = ExtensionState::merge(&base, &ours, &theirs).expect("append-ordered merges");
        let seen: Vec<&[u8]> = merged.entries().iter().map(|e| &*e.payload).collect();
        assert_eq!(seen, vec![b"base".as_slice(), b"ours", b"theirs"]);
    }

    #[test]
    fn set_union_collapses_duplicates() {
        let base = ExtensionState::new(descriptor(
            MergeSemantics::SetUnion,
            PayloadProvenance::Understood,
        ));
        let ours = base.push_entry(bytes(b"x"));
        let theirs = base.push_entry(bytes(b"x")).push_entry(bytes(b"y"));
        let merged = ExtensionState::merge(&base, &ours, &theirs).expect("set union merges");
        assert_eq!(merged.entries().len(), 2, "duplicate `x` collapsed");
    }

    #[test]
    fn review_required_merges_are_typed_conflicts_never_silent() {
        let base = ExtensionState::new(descriptor(
            MergeSemantics::ConflictsRequireReview,
            PayloadProvenance::Understood,
        ));
        let ours = base.push_entry(bytes(b"o"));
        let theirs = base.push_entry(bytes(b"t"));
        let conflict = ExtensionState::merge(&base, &ours, &theirs).expect_err("both changed");
        assert_eq!(conflict.extension, Name::str(Name::anonymous(), "simpExt"));
        // One-sided changes pass through unchanged.
        let one_sided =
            ExtensionState::merge(&base, &ours, &base).expect("one-sided change is safe");
        assert_eq!(one_sided.entries().len(), 1);
    }
}
