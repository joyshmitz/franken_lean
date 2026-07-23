//! The Grimoire environment (plan §7.1): semantically the Reference's name→constant
//! map plus contract-registered extensions; mechanically ours — persistent maps with
//! structural sharing, so a snapshot is an O(1) clone and mutation after a fork is
//! invisible to the fork (the primitive under Athanor's speculative parallelism,
//! Lantern's per-request views, and Envoy's search trees).
//!
//! Every commit exposes two roots: the **logical root** (declarations + extension
//! deltas + options; the cache key the Ledger, receipts, and Envoy speak) and a
//! separate **operational-metadata root** — two hosts producing the same trusted
//! environment share a logical root even when their operational manifests differ.

use std::sync::Arc;

use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_hash::canon::{CanonWriter, Canonical};
use fln_hash::domain::{Digest, Domain, hash};
use fln_hash::root::{LogicalRoot, LogicalRootBuilder};

use crate::constants::{ConstantInfo, DefinitionSafety, QuotKind, ReducibilityHints};
use crate::extensions::{
    CheckpointError, CheckpointLimits, CheckpointSemantics, ExtensionCheckpoint,
    ExtensionDescriptor, ExtensionState,
};
#[cfg(test)]
use crate::extensions::{MergeSemantics, PayloadProvenance};
use crate::pmap::{PKey, PMap};

/// Stable `Domain::DeclContent` tags. These are schema values, not Rust enum
/// discriminants: changing them requires an explicit identity/epoch decision.
fn definition_safety_tag(safety: DefinitionSafety) -> u8 {
    match safety {
        DefinitionSafety::Unsafe => 0,
        DefinitionSafety::Safe => 1,
        DefinitionSafety::Partial => 2,
    }
}

fn quot_kind_tag(kind: QuotKind) -> u8 {
    match kind {
        QuotKind::Type => 0,
        QuotKind::Ctor => 1,
        QuotKind::Lift => 2,
        QuotKind::Ind => 3,
    }
}

/// Write a mutual-block membership list into declaration identity.
///
/// The order and multiplicity are semantic input. Keep this as one forward pass:
/// no sorting, deduplication, or structure proportional to the containing
/// [`Environment`] belongs in declaration identity.
fn write_mutual_membership(w: &mut CanonWriter, members: &[Name]) {
    w.u64(members.len() as u64);
    for member in members {
        member.write_body(w);
    }
}

impl PKey for Name {
    fn key_hash(&self) -> u64 {
        // The stored Reference-observable hash; collisions are handled by the trie's
        // buckets, equality stays structural.
        self.hash()
    }
}

/// Typed refusals — an environment mutation never panics and never silently drops.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvError {
    /// The kernel's already-declared law: one name, one constant.
    DuplicateDeclaration {
        name: Name,
    },
    DuplicateExtension {
        name: Name,
    },
    UnknownExtension {
        name: Name,
    },
    Checkpoint(CheckpointError),
}

impl std::fmt::Display for EnvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnvError::DuplicateDeclaration { name } => {
                write!(
                    f,
                    "constant `{}` is already declared",
                    name.to_display_string()
                )
            }
            EnvError::DuplicateExtension { name } => {
                write!(
                    f,
                    "extension `{}` is already registered",
                    name.to_display_string()
                )
            }
            EnvError::UnknownExtension { name } => {
                write!(
                    f,
                    "extension `{}` is not registered",
                    name.to_display_string()
                )
            }
            EnvError::Checkpoint(error) => error.fmt(f),
        }
    }
}

/// The environment. `Clone` IS `snapshot`: O(1), fully isolated.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Environment {
    constants: PMap<Name, Arc<ConstantInfo>>,
    extensions: PMap<Name, Arc<ExtensionState>>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment::default()
    }

    pub fn len(&self) -> usize {
        self.constants.len()
    }

    pub fn is_empty(&self) -> bool {
        self.constants.is_empty()
    }

    /// `Environment.find`.
    pub fn find(&self, name: &Name) -> Option<&ConstantInfo> {
        self.constants.get(name).map(Arc::as_ref)
    }

    pub fn contains(&self, name: &Name) -> bool {
        self.constants.contains_key(name)
    }

    /// Add a constant. One name, one constant — a duplicate is a typed refusal
    /// (the kernel's admission law; nothing here can overwrite a declaration).
    pub fn add_decl(&self, info: ConstantInfo) -> Result<Environment, EnvError> {
        let name = info.name().clone();
        if self.constants.contains_key(&name) {
            return Err(EnvError::DuplicateDeclaration { name });
        }
        Ok(Environment {
            constants: self.constants.insert(name, Arc::new(info)),
            extensions: self.extensions.clone(),
        })
    }

    /// Register an extension with its declared contracts.
    pub fn register_extension(
        &self,
        descriptor: ExtensionDescriptor,
    ) -> Result<Environment, EnvError> {
        let name = descriptor.name.clone();
        if self.extensions.contains_key(&name) {
            return Err(EnvError::DuplicateExtension { name });
        }
        Ok(Environment {
            constants: self.constants.clone(),
            extensions: self
                .extensions
                .insert(name, Arc::new(ExtensionState::new(descriptor))),
        })
    }

    /// Append one replay entry to a registered extension.
    pub fn push_extension_entry(
        &self,
        extension: &Name,
        payload: impl Into<Arc<[u8]>>,
    ) -> Result<Environment, EnvError> {
        let Some(state) = self.extensions.get(extension) else {
            return Err(EnvError::UnknownExtension {
                name: extension.clone(),
            });
        };
        let next = state.push_entry(payload);
        Ok(Environment {
            constants: self.constants.clone(),
            extensions: self.extensions.insert(extension.clone(), Arc::new(next)),
        })
    }

    pub fn extension(&self, name: &Name) -> Option<&ExtensionState> {
        self.extensions.get(name).map(Arc::as_ref)
    }

    /// Capture one registered extension under its declared checkpoint contract.
    /// A suffix base is another immutable environment snapshot; full-journal mode
    /// requires `None` and carries no ambient extension history.
    pub fn checkpoint_extension(
        &self,
        extension: &Name,
        base: Option<&Environment>,
        limits: CheckpointLimits,
    ) -> Result<ExtensionCheckpoint, EnvError> {
        let state = self
            .extension(extension)
            .ok_or_else(|| EnvError::UnknownExtension {
                name: extension.clone(),
            })?;
        let base_state = match base {
            Some(base) => {
                Some(
                    base.extension(extension)
                        .ok_or_else(|| EnvError::UnknownExtension {
                            name: extension.clone(),
                        })?,
                )
            }
            None => None,
        };
        state
            .checkpoint(base_state, limits)
            .map_err(EnvError::Checkpoint)
    }

    /// Apply a checkpoint to the matching registry slot and return a new isolated
    /// environment snapshot. Declarations and unrelated extensions remain shared.
    pub fn apply_extension_checkpoint(
        &self,
        checkpoint: &ExtensionCheckpoint,
        limits: CheckpointLimits,
    ) -> Result<Environment, EnvError> {
        let name = &checkpoint.descriptor().name;
        let registered = self
            .extension(name)
            .ok_or_else(|| EnvError::UnknownExtension { name: name.clone() })?;
        if checkpoint.mode() == CheckpointSemantics::FullJournal
            && registered.descriptor != *checkpoint.descriptor()
        {
            let error = if registered.descriptor.name != checkpoint.descriptor().name {
                CheckpointError::ExtensionNameMismatch {
                    expected: checkpoint.descriptor().name.clone(),
                    actual: registered.descriptor.name.clone(),
                }
            } else {
                CheckpointError::ContractMismatch {
                    expected: checkpoint.descriptor().clone(),
                    actual: registered.descriptor.clone(),
                }
            };
            return Err(EnvError::Checkpoint(error));
        }
        let base = match checkpoint.mode() {
            CheckpointSemantics::JournalSuffix => Some(registered),
            CheckpointSemantics::FullJournal => None,
        };
        let restored =
            ExtensionState::restore(base, checkpoint, limits).map_err(EnvError::Checkpoint)?;
        Ok(Environment {
            constants: self.constants.clone(),
            extensions: self.extensions.insert(name.clone(), Arc::new(restored)),
        })
    }

    /// The canonical content digest of one constant (Domain::DeclContent): the
    /// deterministic projection the logical root aggregates. Byte-level olean parity
    /// is the codec's business; this digest is FrankenLean's own identity.
    pub fn decl_content_digest(info: &ConstantInfo) -> Digest {
        let mut w = CanonWriter::new();
        w.str(info.kind_name());
        info.name().write_body(&mut w);
        let base = info.constant_val();
        w.u64(base.level_params.len() as u64);
        for p in &base.level_params {
            p.write_body(&mut w);
        }
        base.type_.write_body(&mut w);
        match info {
            ConstantInfo::Axiom(v) => w.bool(v.is_unsafe),
            ConstantInfo::Defn(v) => {
                v.value.write_body(&mut w);
                match v.hints {
                    ReducibilityHints::Opaque => w.u8(0),
                    ReducibilityHints::Abbrev => w.u8(1),
                    ReducibilityHints::Regular(h) => {
                        w.u8(2);
                        w.u32(h);
                    }
                }
                w.u8(definition_safety_tag(v.safety));
                write_mutual_membership(&mut w, &v.all);
            }
            ConstantInfo::Thm(v) => {
                v.value.write_body(&mut w);
                write_mutual_membership(&mut w, &v.all);
            }
            ConstantInfo::Opaque(v) => {
                v.value.write_body(&mut w);
                w.bool(v.is_unsafe);
                write_mutual_membership(&mut w, &v.all);
            }
            ConstantInfo::Quot(v) => w.u8(quot_kind_tag(v.kind)),
            ConstantInfo::Induct(v) => {
                w.u32(v.num_params);
                w.u32(v.num_indices);
                w.u32(v.num_nested);
                w.bool(v.is_rec);
                w.bool(v.is_unsafe);
                w.bool(v.is_reflexive);
                w.u64(v.ctors.len() as u64);
                for n in &v.ctors {
                    n.write_body(&mut w);
                }
                // The mutual-inductive block is part of the declaration's content
                // (as it is for `Defn`/`Thm`): two inductives identical except for
                // their block grouping are distinct declarations and must not share
                // a content digest.
                write_mutual_membership(&mut w, &v.all);
            }
            ConstantInfo::Ctor(v) => {
                v.induct.write_body(&mut w);
                w.u32(v.cidx);
                w.u32(v.num_params);
                w.u32(v.num_fields);
                w.bool(v.is_unsafe);
            }
            ConstantInfo::Rec(v) => {
                w.u32(v.num_params);
                w.u32(v.num_indices);
                w.u32(v.num_motives);
                w.u32(v.num_minors);
                w.bool(v.k);
                w.bool(v.is_unsafe);
                w.u64(v.rules.len() as u64);
                for rule in &v.rules {
                    rule.ctor.write_body(&mut w);
                    w.u32(rule.nfields);
                    rule.rhs.write_body(&mut w);
                }
                // The mutual block is content here too (mirrors `Defn`/`Thm`).
                write_mutual_membership(&mut w, &v.all);
            }
        }
        hash(Domain::DeclContent, &w.into_bytes())
    }

    /// The logical root of this commit: declarations + extension deltas + options —
    /// and nothing else (wall-clock, paths, and schedule have no way in).
    pub fn logical_root(&self, options: &KVMap) -> LogicalRoot {
        let mut builder = LogicalRootBuilder::new();
        for (name, info) in self.constants.iter() {
            builder.add_decl(name, Environment::decl_content_digest(info));
        }
        for (name, state) in self.extensions.iter() {
            builder.add_extension_delta(name, state.content_digest());
        }
        builder.set_options(options);
        builder.finalize()
    }

    /// The operational-metadata root: host facts, paths, timings — everything the
    /// logical root deliberately excludes, digested separately so receipts can carry
    /// both without ever mixing them.
    pub fn operational_root(metadata: &KVMap) -> Digest {
        hash(Domain::OperationalMeta, &metadata.to_canonical_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{
        AxiomVal, ConstantVal, DefinitionVal, InductiveVal, OpaqueVal, RecursorRule, RecursorVal,
        TheoremVal,
    };
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_core::options::DataValue;

    fn n(s: &str) -> Name {
        Name::str(Name::anonymous(), s)
    }

    fn axiom(name: &str) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n(name),
                level_params: vec![],
                type_: Expr::sort(Level::zero()),
            },
            is_unsafe: false,
        })
    }

    #[derive(Debug, Clone, Copy)]
    enum AllBearingKind {
        Definition,
        Theorem,
        Opaque,
        Inductive,
        Recursor,
    }

    impl AllBearingKind {
        const ALL: [AllBearingKind; 5] = [
            AllBearingKind::Definition,
            AllBearingKind::Theorem,
            AllBearingKind::Opaque,
            AllBearingKind::Inductive,
            AllBearingKind::Recursor,
        ];

        const fn label(self) -> &'static str {
            match self {
                AllBearingKind::Definition => "definition",
                AllBearingKind::Theorem => "theorem",
                AllBearingKind::Opaque => "opaque",
                AllBearingKind::Inductive => "inductive",
                AllBearingKind::Recursor => "recursor",
            }
        }
    }

    #[derive(Debug, Clone, Copy)]
    enum MembershipModel {
        Canonical,
        DropList,
        OmitCount,
        SortMembers,
    }

    fn all_bearing_decl(kind: AllBearingKind, all: Vec<Name>) -> ConstantInfo {
        let body = || Expr::const_(n("body"), vec![Level::param(n("u"))]);
        let base = || ConstantVal {
            name: n("d"),
            level_params: vec![n("u")],
            type_: Expr::sort(Level::param(n("u"))),
        };
        match kind {
            AllBearingKind::Definition => ConstantInfo::Defn(DefinitionVal {
                base: base(),
                value: body(),
                hints: ReducibilityHints::Regular(7),
                safety: DefinitionSafety::Partial,
                all,
            }),
            AllBearingKind::Theorem => ConstantInfo::Thm(TheoremVal {
                base: base(),
                value: body(),
                all,
            }),
            AllBearingKind::Opaque => ConstantInfo::Opaque(OpaqueVal {
                base: base(),
                value: body(),
                is_unsafe: true,
                all,
            }),
            AllBearingKind::Inductive => ConstantInfo::Induct(InductiveVal {
                base: base(),
                num_params: 2,
                num_indices: 1,
                all,
                ctors: vec![n("mk"), n("mkAlt")],
                num_nested: 3,
                is_rec: true,
                is_unsafe: true,
                is_reflexive: true,
            }),
            AllBearingKind::Recursor => ConstantInfo::Rec(RecursorVal {
                base: base(),
                all,
                num_params: 2,
                num_indices: 1,
                num_motives: 1,
                num_minors: 2,
                rules: vec![
                    RecursorRule {
                        ctor: n("mk"),
                        nfields: 3,
                        rhs: body(),
                    },
                    RecursorRule {
                        ctor: n("mkAlt"),
                        nfields: 4,
                        rhs: Expr::const_(n("bodyAlt"), vec![Level::zero()]),
                    },
                ],
                k: true,
                is_unsafe: true,
            }),
        }
    }

    fn write_membership_model(w: &mut CanonWriter, members: &[Name], model: MembershipModel) {
        match model {
            MembershipModel::Canonical => {
                w.u64(members.len() as u64);
                for member in members {
                    member.write_body(w);
                }
            }
            MembershipModel::DropList => {}
            MembershipModel::OmitCount => {
                for member in members {
                    member.write_body(w);
                }
            }
            MembershipModel::SortMembers => {
                let mut sorted = members.to_vec();
                sorted.sort();
                w.u64(sorted.len() as u64);
                for member in &sorted {
                    member.write_body(w);
                }
            }
        }
    }

    /// Control-flow-independent declaration layout model for the five variants
    /// carrying mutual-block membership. It intentionally shares only the primitive
    /// canonical codecs and registered hash implementation with production.
    fn modeled_all_bearing_digest(
        info: &ConstantInfo,
        membership_model: MembershipModel,
        domain: Domain,
    ) -> Digest {
        let mut w = CanonWriter::new();
        let kind_name = match info {
            ConstantInfo::Defn(_) => "definition",
            ConstantInfo::Thm(_) => "theorem",
            ConstantInfo::Opaque(_) => "opaque",
            ConstantInfo::Induct(_) => "inductive",
            ConstantInfo::Rec(_) => "recursor",
            _ => unreachable!("the model accepts only all-bearing declarations"),
        };
        w.str(kind_name);
        info.name().write_body(&mut w);
        let base = info.constant_val();
        w.u64(base.level_params.len() as u64);
        for parameter in &base.level_params {
            parameter.write_body(&mut w);
        }
        base.type_.write_body(&mut w);
        match info {
            ConstantInfo::Defn(value) => {
                value.value.write_body(&mut w);
                match value.hints {
                    ReducibilityHints::Opaque => w.u8(0),
                    ReducibilityHints::Abbrev => w.u8(1),
                    ReducibilityHints::Regular(height) => {
                        w.u8(2);
                        w.u32(height);
                    }
                }
                let safety_tag = match value.safety {
                    DefinitionSafety::Unsafe => 0,
                    DefinitionSafety::Safe => 1,
                    DefinitionSafety::Partial => 2,
                };
                w.u8(safety_tag);
                write_membership_model(&mut w, &value.all, membership_model);
            }
            ConstantInfo::Thm(value) => {
                value.value.write_body(&mut w);
                write_membership_model(&mut w, &value.all, membership_model);
            }
            ConstantInfo::Opaque(value) => {
                value.value.write_body(&mut w);
                w.bool(value.is_unsafe);
                write_membership_model(&mut w, &value.all, membership_model);
            }
            ConstantInfo::Induct(value) => {
                w.u32(value.num_params);
                w.u32(value.num_indices);
                w.u32(value.num_nested);
                w.bool(value.is_rec);
                w.bool(value.is_unsafe);
                w.bool(value.is_reflexive);
                w.u64(value.ctors.len() as u64);
                for ctor in &value.ctors {
                    ctor.write_body(&mut w);
                }
                write_membership_model(&mut w, &value.all, membership_model);
            }
            ConstantInfo::Rec(value) => {
                w.u32(value.num_params);
                w.u32(value.num_indices);
                w.u32(value.num_motives);
                w.u32(value.num_minors);
                w.bool(value.k);
                w.bool(value.is_unsafe);
                w.u64(value.rules.len() as u64);
                for rule in &value.rules {
                    rule.ctor.write_body(&mut w);
                    w.u32(rule.nfields);
                    rule.rhs.write_body(&mut w);
                }
                write_membership_model(&mut w, &value.all, membership_model);
            }
            _ => unreachable!("the model accepts only all-bearing declarations"),
        }
        hash(domain, &w.into_bytes())
    }

    fn canonical_name_body_bytes(names: &[Name]) -> usize {
        names
            .iter()
            .map(|name| {
                let mut w = CanonWriter::new();
                name.write_body(&mut w);
                w.into_bytes().len()
            })
            .sum()
    }

    fn descriptor(name: &str) -> ExtensionDescriptor {
        ExtensionDescriptor {
            name: n(name),
            merge: MergeSemantics::AppendOrdered,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance: PayloadProvenance::Understood,
        }
    }

    #[test]
    fn add_find_and_the_one_name_one_constant_law() {
        let env = Environment::new().add_decl(axiom("a")).expect("adds");
        assert_eq!(env.len(), 1);
        assert_eq!(env.find(&n("a")).expect("found").kind_name(), "axiom");
        assert!(env.find(&n("b")).is_none());
        let dup = env.add_decl(axiom("a")).expect_err("duplicate refused");
        assert_eq!(dup, EnvError::DuplicateDeclaration { name: n("a") });
    }

    #[test]
    fn snapshots_are_isolated_forks() {
        let base = Environment::new().add_decl(axiom("a")).expect("adds");
        let fork = base.clone(); // O(1) snapshot
        let extended = base.add_decl(axiom("b")).expect("adds");
        assert_eq!(
            fork.len(),
            1,
            "mutation after fork is invisible to the fork"
        );
        assert_eq!(extended.len(), 2);
        assert!(fork.find(&n("b")).is_none());
        // And the fork can diverge independently.
        let fork2 = fork.add_decl(axiom("c")).expect("adds");
        assert!(extended.find(&n("c")).is_none());
        assert!(fork2.find(&n("b")).is_none());
    }

    #[test]
    fn logical_roots_are_insertion_order_independent_and_semantic() {
        let forward = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|e| e.add_decl(axiom("b")))
            .and_then(|e| e.add_decl(axiom("c")))
            .expect("builds");
        let reverse = Environment::new()
            .add_decl(axiom("c"))
            .and_then(|e| e.add_decl(axiom("b")))
            .and_then(|e| e.add_decl(axiom("a")))
            .expect("builds");
        let opts = KVMap::new();
        assert_eq!(forward.logical_root(&opts), reverse.logical_root(&opts));

        // Different content ⇒ different root.
        let other = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|e| e.add_decl(axiom("b")))
            .expect("builds");
        assert_ne!(forward.logical_root(&opts), other.logical_root(&opts));

        // Options are part of the logical root.
        let mut opts2 = KVMap::new();
        opts2.insert(n("maxHeartbeats"), DataValue::OfNat(400_000));
        assert_ne!(forward.logical_root(&opts), forward.logical_root(&opts2));
    }

    #[test]
    fn extension_entries_enter_the_logical_root_in_order() {
        let opts = KVMap::new();
        let env = Environment::new()
            .register_extension(descriptor("simpExt"))
            .expect("registers");
        let one = env
            .push_extension_entry(&n("simpExt"), &b"e1"[..])
            .expect("pushes");
        let two = one
            .push_extension_entry(&n("simpExt"), &b"e2"[..])
            .expect("pushes");
        assert_ne!(env.logical_root(&opts), one.logical_root(&opts));
        assert_ne!(one.logical_root(&opts), two.logical_root(&opts));
        // Replay order is preserved exactly.
        let entries: Vec<&[u8]> = two
            .extension(&n("simpExt"))
            .expect("registered")
            .entries()
            .map(|e| &*e.payload)
            .collect();
        assert_eq!(entries, vec![b"e1".as_slice(), b"e2"]);
        // Unknown extension is a typed refusal.
        assert_eq!(
            env.push_extension_entry(&n("ghost"), &b"x"[..]),
            Err(EnvError::UnknownExtension { name: n("ghost") })
        );
    }

    #[test]
    fn environment_checkpoint_apply_preserves_exact_roots_and_unrelated_state() {
        let limits = CheckpointLimits::new(100, 10_000);
        let base = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|env| env.register_extension(descriptor("simpExt")))
            .and_then(|env| env.register_extension(descriptor("otherExt")))
            .and_then(|env| env.push_extension_entry(&n("simpExt"), &b"base"[..]))
            .and_then(|env| env.push_extension_entry(&n("otherExt"), &b"other"[..]))
            .expect("base environment builds");
        let target = base
            .push_extension_entry(&n("simpExt"), &b"suffix-a"[..])
            .and_then(|env| env.push_extension_entry(&n("simpExt"), &b"suffix-b"[..]))
            .expect("target environment builds");
        let checkpoint = target
            .checkpoint_extension(&n("simpExt"), Some(&base), limits)
            .expect("environment suffix captures");
        let restored = base
            .apply_extension_checkpoint(&checkpoint, limits)
            .expect("environment suffix applies");

        assert_eq!(restored, target);
        assert_eq!(
            restored.logical_root(&KVMap::new()),
            target.logical_root(&KVMap::new())
        );
        assert_eq!(restored.find(&n("a")), target.find(&n("a")));
        assert_eq!(
            restored.extension(&n("otherExt")),
            target.extension(&n("otherExt"))
        );

        let divergent = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|env| env.register_extension(descriptor("simpExt")))
            .and_then(|env| env.register_extension(descriptor("otherExt")))
            .and_then(|env| env.push_extension_entry(&n("simpExt"), &b"wrong"[..]))
            .and_then(|env| env.push_extension_entry(&n("otherExt"), &b"other"[..]))
            .expect("same-length divergent branch builds");
        assert!(matches!(
            divergent.apply_extension_checkpoint(&checkpoint, limits),
            Err(EnvError::Checkpoint(
                CheckpointError::BaseHistoryMismatch { .. }
            ))
        ));
        assert_eq!(
            divergent
                .extension(&n("simpExt"))
                .expect("still registered")
                .entries()
                .last()
                .expect("one entry")
                .payload
                .as_ref(),
            b"wrong"
        );
    }

    #[test]
    fn environment_full_checkpoint_replaces_only_the_registered_journal() {
        let limits = CheckpointLimits::new(100, 10_000);
        let full_descriptor = ExtensionDescriptor {
            checkpoint: CheckpointSemantics::FullJournal,
            ..descriptor("fullExt")
        };
        let destination = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|env| env.register_extension(full_descriptor))
            .expect("destination builds");
        let source = destination
            .push_extension_entry(&n("fullExt"), &b"one"[..])
            .and_then(|env| env.push_extension_entry(&n("fullExt"), &b"two"[..]))
            .expect("source builds");
        let checkpoint = source
            .checkpoint_extension(&n("fullExt"), None, limits)
            .expect("full environment checkpoint captures");
        let restored = destination
            .apply_extension_checkpoint(&checkpoint, limits)
            .expect("full checkpoint applies without a semantic base");
        assert_eq!(restored, source);
        assert_eq!(
            restored.logical_root(&KVMap::new()),
            source.logical_root(&KVMap::new())
        );
        assert!(matches!(
            source.checkpoint_extension(&n("ghost"), None, limits),
            Err(EnvError::UnknownExtension { .. })
        ));
    }

    #[test]
    fn extension_contracts_enter_the_logical_root() {
        let root = |merge, checkpoint, provenance| {
            let descriptor = ExtensionDescriptor {
                name: n("contractExt"),
                merge,
                checkpoint,
                provenance,
            };
            Environment::new()
                .register_extension(descriptor)
                .and_then(|env| env.push_extension_entry(&n("contractExt"), &b"entry"[..]))
                .expect("extension environment builds")
                .logical_root(&KVMap::new())
        };

        let append = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        let append_again = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        assert_eq!(
            append, append_again,
            "identical extension contracts and journals have stable identity"
        );

        let set_union = root(
            MergeSemantics::SetUnion,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        let review = root(
            MergeSemantics::ConflictsRequireReview,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Understood,
        );
        assert_ne!(append, set_union, "merge semantics enter the root");
        assert_ne!(append, review, "merge semantics enter the root");
        assert_ne!(
            set_union, review,
            "every merge variant has distinct identity"
        );

        let full_journal = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::FullJournal,
            PayloadProvenance::Understood,
        );
        assert_ne!(append, full_journal, "checkpoint semantics enter the root");

        let opaque = root(
            MergeSemantics::AppendOrdered,
            CheckpointSemantics::JournalSuffix,
            PayloadProvenance::Opaque,
        );
        assert_ne!(append, opaque, "payload provenance enters the root");
    }

    #[test]
    fn add_decl_preserves_extension_state() {
        // The mutant this kills: add_decl rebuilding the environment with empty
        // extensions (state silently dropped) — found surviving by the
        // env_snapshots E2E mutation lane, then pinned here forever.
        let env = Environment::new()
            .register_extension(descriptor("simpExt"))
            .expect("registers")
            .push_extension_entry(&n("simpExt"), &b"e1"[..])
            .expect("pushes");
        let with_decl = env.add_decl(axiom("a")).expect("adds");
        let state = with_decl
            .extension(&n("simpExt"))
            .expect("extension state survives add_decl");
        assert_eq!(state.len(), 1);
        // And the delta still reaches the logical root after the decl lands.
        let opts = KVMap::new();
        let bare = Environment::new()
            .add_decl(axiom("a"))
            .and_then(|e| e.register_extension(descriptor("simpExt")))
            .expect("builds");
        assert_ne!(with_decl.logical_root(&opts), bare.logical_root(&opts));
    }

    #[test]
    fn operational_metadata_never_touches_the_logical_root() {
        let env = Environment::new().add_decl(axiom("a")).expect("adds");
        let opts = KVMap::new();
        let root = env.logical_root(&opts);

        let mut host_a = KVMap::new();
        host_a.insert(n("host"), DataValue::OfString("machine-a".into()));
        let mut host_b = KVMap::new();
        host_b.insert(n("host"), DataValue::OfString("machine-b".into()));

        // Same trusted environment, different hosts: same logical root, different
        // operational roots.
        assert_eq!(root, env.logical_root(&opts));
        assert_ne!(
            Environment::operational_root(&host_a),
            Environment::operational_root(&host_b)
        );
    }

    #[test]
    fn declaration_identity_enum_tags_are_explicit_and_distinct() {
        use crate::constants::{DefinitionVal, QuotVal};

        assert_eq!(definition_safety_tag(DefinitionSafety::Unsafe), 0);
        assert_eq!(definition_safety_tag(DefinitionSafety::Safe), 1);
        assert_eq!(definition_safety_tag(DefinitionSafety::Partial), 2);
        assert_eq!(quot_kind_tag(QuotKind::Type), 0);
        assert_eq!(quot_kind_tag(QuotKind::Ctor), 1);
        assert_eq!(quot_kind_tag(QuotKind::Lift), 2);
        assert_eq!(quot_kind_tag(QuotKind::Ind), 3);

        let base = || ConstantVal {
            name: n("tagged"),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        };
        let definition = |safety| {
            ConstantInfo::Defn(DefinitionVal {
                base: base(),
                value: Expr::sort(Level::zero()),
                hints: ReducibilityHints::Opaque,
                safety,
                all: vec![n("tagged")],
            })
        };
        let quotient = |kind| ConstantInfo::Quot(QuotVal { base: base(), kind });
        let assert_pairwise_distinct = |infos: Vec<ConstantInfo>| {
            let digests: Vec<Digest> = infos.iter().map(Environment::decl_content_digest).collect();
            for (index, lhs) in digests.iter().enumerate() {
                for rhs in &digests[index + 1..] {
                    assert_ne!(lhs, rhs, "distinct schema tags must change identity");
                }
            }
        };
        assert_pairwise_distinct(vec![
            definition(DefinitionSafety::Unsafe),
            definition(DefinitionSafety::Safe),
            definition(DefinitionSafety::Partial),
        ]);
        assert_pairwise_distinct(vec![
            quotient(QuotKind::Type),
            quotient(QuotKind::Ctor),
            quotient(QuotKind::Lift),
            quotient(QuotKind::Ind),
        ]);

        let options = KVMap::new();
        let root = Environment::new()
            .add_decl(definition(DefinitionSafety::Safe))
            .expect("tagged definition is valid")
            .logical_root(&options);
        let repeated = Environment::new()
            .add_decl(definition(DefinitionSafety::Safe))
            .expect("same tagged definition is valid")
            .logical_root(&options);
        assert_eq!(root, repeated, "explicit tags are stable across rebuilds");
    }

    #[test]
    fn mutual_block_membership_changes_the_content_digest() {
        const LARGE_MEMBER_COUNT: usize = 4_096;
        let large_members: Vec<Name> = (0..LARGE_MEMBER_COUNT)
            .map(|index| Name::num(n("member"), index as u64))
            .collect();
        let boundary_cases = vec![
            ("empty", Vec::new()),
            ("singleton", vec![n("d")]),
            ("repeated", vec![n("d"), n("d")]),
            ("ordered", vec![n("d"), n("e")]),
            ("reordered", vec![n("e"), n("d")]),
            ("renamed", vec![n("d"), n("f")]),
            ("declared_large", large_members),
        ];
        let options = KVMap::new();

        for kind in AllBearingKind::ALL {
            let mut digests = Vec::with_capacity(boundary_cases.len());
            for (case, members) in &boundary_cases {
                let info = all_bearing_decl(kind, members.clone());
                let actual = Environment::decl_content_digest(&info);
                let expected = modeled_all_bearing_digest(
                    &info,
                    MembershipModel::Canonical,
                    Domain::DeclContent,
                );
                assert_eq!(
                    actual,
                    expected,
                    "{} {case} membership diverged from the independent canonical model",
                    kind.label()
                );

                let rebuilt = all_bearing_decl(kind, members.clone());
                assert_eq!(
                    actual,
                    Environment::decl_content_digest(&rebuilt),
                    "{} {case} membership was not repeatable",
                    kind.label()
                );

                let environment = Environment::new()
                    .add_decl(info)
                    .expect("fixture declaration is valid");
                let actual_root = environment.logical_root(&options);
                let mut expected_root = LogicalRootBuilder::new();
                expected_root.add_decl(rebuilt.name(), actual);
                expected_root.set_options(&options);
                assert_eq!(
                    actual_root,
                    expected_root.finalize(),
                    "{} {case} digest did not propagate exactly into the logical root",
                    kind.label()
                );
                let repeated_root = Environment::new()
                    .add_decl(rebuilt)
                    .expect("repeated fixture declaration is valid")
                    .logical_root(&options);
                assert_eq!(
                    actual_root,
                    repeated_root,
                    "{} {case} logical root was not repeatable",
                    kind.label()
                );
                digests.push(actual);
            }

            assert_ne!(
                digests[0],
                digests[1],
                "{} must distinguish empty and singleton membership",
                kind.label()
            );
            assert_ne!(
                digests[1],
                digests[2],
                "{} must preserve repeated membership",
                kind.label()
            );
            assert_ne!(
                digests[1],
                digests[3],
                "{} must distinguish solo and grouped membership",
                kind.label()
            );
            assert_ne!(
                digests[2],
                digests[3],
                "{} must distinguish multiplicity and member identity",
                kind.label()
            );
            assert_ne!(
                digests[3],
                digests[4],
                "{} must preserve membership order",
                kind.label()
            );
            assert_ne!(
                digests[3],
                digests[5],
                "{} must preserve member names",
                kind.label()
            );
            assert_ne!(
                digests[5],
                digests[6],
                "{} must cover the declared large-member boundary",
                kind.label()
            );
            eprintln!(
                "{{\"schema\":\"fln.unit.mutual-membership-boundaries\",\"version\":1,\
                 \"bead\":\"fln-amv.1\",\"claim_type\":\"bounded_model\",\
                 \"kind\":\"{}\",\"case_count\":7,\"large_member_count\":4096,\
                 \"empty_digest\":\"{}\",\"solo_digest\":\"{}\",\
                 \"grouped_digest\":\"{}\",\"reordered_digest\":\"{}\",\
                 \"large_digest\":\"{}\",\"root_propagation\":\"exact\",\
                 \"repeatability\":\"pass\",\"status\":\"pass\"}}",
                kind.label(),
                digests[0],
                digests[1],
                digests[3],
                digests[4],
                digests[6]
            );
        }

        let opaque_solo = Environment::decl_content_digest(&all_bearing_decl(
            AllBearingKind::Opaque,
            vec![n("d")],
        ));
        let opaque_grouped = Environment::decl_content_digest(&all_bearing_decl(
            AllBearingKind::Opaque,
            vec![n("d"), n("e")],
        ));
        assert_ne!(
            opaque_solo, opaque_grouped,
            "OpaqueVal.all must distinguish the original solo-versus-grouped regression"
        );
    }

    #[test]
    fn mutual_block_membership_named_mutants_are_discriminated() {
        let witness = vec![n("e"), n("d"), n("e"), n("f")];
        let options = KVMap::new();

        for kind in AllBearingKind::ALL {
            let info = all_bearing_decl(kind, witness.clone());
            let canonical = Environment::decl_content_digest(&info);
            for (mutation, model) in [
                ("drop_membership", MembershipModel::DropList),
                ("omit_member_count", MembershipModel::OmitCount),
                ("reorder_membership", MembershipModel::SortMembers),
            ] {
                let mutated = modeled_all_bearing_digest(&info, model, Domain::DeclContent);
                assert_ne!(
                    canonical,
                    mutated,
                    "{mutation} mutant survived for {}",
                    kind.label()
                );
            }

            let wrong_domain =
                modeled_all_bearing_digest(&info, MembershipModel::Canonical, Domain::LogicalRoot);
            assert_ne!(
                canonical,
                wrong_domain,
                "wrong_digest_domain mutant survived for {}",
                kind.label()
            );

            let actual_root = Environment::new()
                .add_decl(info.clone())
                .expect("fixture declaration is valid")
                .logical_root(&options);
            let dropped_digest =
                modeled_all_bearing_digest(&info, MembershipModel::DropList, Domain::DeclContent);
            let mut dropped_root = LogicalRootBuilder::new();
            dropped_root.add_decl(info.name(), dropped_digest);
            dropped_root.set_options(&options);
            assert_ne!(
                actual_root,
                dropped_root.finalize(),
                "fail_to_propagate_membership mutant survived for {}",
                kind.label()
            );
            eprintln!(
                "{{\"schema\":\"fln.unit.mutual-membership-mutants\",\"version\":1,\
                 \"bead\":\"fln-amv.1\",\"claim_type\":\"bounded_model\",\
                 \"kind\":\"{}\",\"witness_member_count\":4,\
                 \"canonical_digest\":\"{canonical}\",\"logical_root\":\"{actual_root}\",\
                 \"mutations\":[\"drop_membership\",\"omit_member_count\",\
                 \"reorder_membership\",\"wrong_digest_domain\",\
                 \"fail_to_propagate_membership\"],\"killed\":5,\
                 \"status\":\"pass\"}}",
                kind.label()
            );
        }
    }

    #[test]
    fn mutual_block_membership_matches_model_for_generated_cases() {
        const GENERATED_CASES: usize = 96;
        const MAX_GENERATED_MEMBERS: usize = 48;
        let mut assertions = 0usize;

        for case_index in 0..GENERATED_CASES {
            let member_count = (case_index * 17) % (MAX_GENERATED_MEMBERS + 1);
            let mut members: Vec<Name> = (0..member_count)
                .map(|member_index| {
                    let root = if (case_index + member_index) % 2 == 0 {
                        n("left")
                    } else {
                        n("right")
                    };
                    let numbered =
                        Name::num(root, ((case_index * 13 + member_index * 7) % 11) as u64);
                    if (case_index + member_index) % 3 == 0 {
                        Name::str(numbered, "leaf")
                    } else {
                        numbered
                    }
                })
                .collect();

            if members.len() > 1 && case_index % 3 == 0 {
                let repeated = members[0].clone();
                let last = members.len() - 1;
                members[last] = repeated;
            }
            if !members.is_empty() {
                match case_index % 4 {
                    1 => members.reverse(),
                    2 => {
                        let shift = case_index % members.len();
                        members.rotate_left(shift);
                    }
                    3 => {
                        let shift = (case_index * 3) % members.len();
                        members.rotate_right(shift);
                    }
                    _ => {}
                }
            }

            for kind in AllBearingKind::ALL {
                let info = all_bearing_decl(kind, members.clone());
                let actual = Environment::decl_content_digest(&info);
                let expected = modeled_all_bearing_digest(
                    &info,
                    MembershipModel::Canonical,
                    Domain::DeclContent,
                );
                assert_eq!(
                    actual,
                    expected,
                    "generated case {case_index} diverged for {}",
                    kind.label()
                );
                assert_eq!(
                    actual,
                    Environment::decl_content_digest(&all_bearing_decl(kind, members.clone())),
                    "generated case {case_index} was not repeatable for {}",
                    kind.label()
                );
                assertions += 2;
            }
        }

        eprintln!(
            "{{\"schema\":\"fln.unit.mutual-membership-generated\",\"version\":1,\
             \"bead\":\"fln-amv.1\",\"claim_type\":\"bounded_model\",\
             \"generated_cases\":{GENERATED_CASES},\"variant_count\":5,\
             \"max_member_count\":{MAX_GENERATED_MEMBERS},\
             \"assertions\":{assertions},\"name_depth_max\":3,\
             \"features\":[\"duplicates\",\"string_components\",\"numeric_components\",\
             \"reversal\",\"rotation\"],\"status\":\"pass\"}}"
        );
    }

    #[test]
    fn mutual_membership_writer_has_canonical_stream_shape() {
        for member_count in [0usize, 1, 32, 4_096] {
            let members: Vec<Name> = (0..member_count)
                .map(|index| Name::num(n("member"), index as u64))
                .collect();
            let canonical_member_bytes = canonical_name_body_bytes(&members);

            let mut actual = CanonWriter::new();
            write_mutual_membership(&mut actual, &members);
            let actual = actual.into_bytes();

            let mut expected = CanonWriter::new();
            write_membership_model(&mut expected, &members, MembershipModel::Canonical);
            let expected = expected.into_bytes();

            assert_eq!(
                actual, expected,
                "membership writer must be exactly count plus one ordered body per member"
            );
            assert_eq!(
                actual.len(),
                8 + canonical_member_bytes,
                "membership stream work must grow with count-prefix plus canonical member bytes"
            );
            eprintln!(
                "{{\"schema\":\"fln.unit.mutual-membership-work\",\"version\":1,\
                 \"bead\":\"fln-amv.1\",\"claim_type\":\"bounded_model\",\
                 \"evidence\":\"canonical_stream_shape\",\
                 \"member_count\":{member_count},\
                 \"canonical_member_bytes\":{canonical_member_bytes},\
                 \"expected_stream_bytes\":{},\"observed_stream_bytes\":{},\
                 \"status\":\"pass\"}}",
                8 + canonical_member_bytes,
                actual.len()
            );
        }
    }

    #[test]
    fn logical_root_is_schedule_independent_across_threads() {
        let names: Vec<String> = (0..64).map(|i| format!("decl{i}")).collect();
        let sequential = {
            let mut env = Environment::new();
            for name in &names {
                env = env.add_decl(axiom(name)).expect("adds");
            }
            env.logical_root(&KVMap::new())
        };
        for threads in [2usize, 8] {
            let chunks: Vec<Vec<String>> = names
                .chunks(names.len().div_ceil(threads))
                .map(<[String]>::to_vec)
                .collect();
            let root = std::thread::scope(|scope| {
                let handles: Vec<_> = chunks
                    .iter()
                    .map(|chunk| scope.spawn(move || chunk.clone()))
                    .collect();
                let mut env = Environment::new();
                for handle in handles {
                    for name in handle.join().expect("worker") {
                        env = env.add_decl(axiom(&name)).expect("adds");
                    }
                }
                env.logical_root(&KVMap::new())
            });
            assert_eq!(root, sequential, "{threads}-thread interleaving diverged");
        }
    }
}
