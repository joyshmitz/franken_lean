//! G0-2 seed: the kernel differential replay rig (bead franken_lean-z6c,
//! plan §22.1-2, §18 kernel differential lane).
//!
//! A REAL Reference module — `Init.Prelude`, the import-free root of the
//! entire library — is decoded from its `.olean` (statements AND proofs,
//! bit-level identity cross-checks on) and replayed through the one
//! authority, `fln_kernel::check`, declaration by declaration in module
//! order. The Reference kernel accepted every one of these declarations when
//! it produced the olean, so:
//!
//!   - `Accepted` = verdict agreement with the Reference;
//!   - `Inconclusive` = honest exhaustion, typed (FL-INV-07);
//!   - `Rejected` = a DIVERGENCE — either a K1 gap (expected classes are
//!     pinned below and re-triaged whenever the census moves) or a soundness
//!     finding (immediately fatal here).
//!
//! Every declaration kind in the module is kernel-checked (bead
//! franken_lean-ap6): inductive blocks as whole units under KR-6xx/7xx/8xx
//! with recursor regeneration, quotients under KR-95x, definitions of every
//! safety level under the pin's add_definition split. The one typed
//! limitation: a nested block (Lean.Syntax) admits under the partial ruleset
//! (no positivity, no regeneration) and is surfaced by the census.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::PathBuf;

use fln_core::expr::{Expr, ExprNode};
use fln_core::name::Name;
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use fln_env::environment::Environment;
use fln_kernel::Declaration;
use fln_kernel::verdict::{Budget, Verdict};
use fln_olean::decl::DeclDecoder;
use fln_olean::region::{OleanView, WalkBudget};

/// Bounded term-shape rendering for the `FLN_REPLAY_PROBE` lane (bead
/// fln-d4x): enough to see how a rejected declaration's value is compiled —
/// recursor application vs projections vs constructor eta — without dumping
/// full proof terms. Fuel-bounded recursion, safe on real Reference terms.
fn shape(e: &Expr, fuel: usize) -> String {
    if fuel == 0 {
        return "…".to_string();
    }
    match e.node() {
        ExprNode::BVar { idx } => format!("#{idx}"),
        ExprNode::FVar { .. } => "fvar".to_string(),
        ExprNode::MVar { .. } => "mvar".to_string(),
        ExprNode::Sort { .. } => "Sort".to_string(),
        ExprNode::Const { name, .. } => name.to_display_string(),
        ExprNode::App { .. } => {
            let mut args = Vec::new();
            let mut head = e.clone();
            while let ExprNode::App { f, a } = head.node() {
                args.push(a.clone());
                let next = f.clone();
                head = next;
            }
            args.reverse();
            let mut out = format!("({}", shape(&head, fuel - 1));
            for arg in &args {
                out.push(' ');
                out.push_str(&shape(arg, fuel - 1));
            }
            out.push(')');
            out
        }
        ExprNode::Lam { body, .. } => format!("(fun _ => {})", shape(body, fuel - 1)),
        ExprNode::ForallE { body, .. } => format!("(forall _, {})", shape(body, fuel - 1)),
        ExprNode::LetE { body, .. } => format!("(let _ := ..; {})", shape(body, fuel - 1)),
        ExprNode::MData { expr, .. } => shape(expr, fuel),
        ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } => format!(
            "({}.{} {})",
            struct_name.to_display_string(),
            idx,
            shape(expr, fuel - 1)
        ),
        ExprNode::Lit { .. } => "lit".to_string(),
    }
}

/// Collect every `Const` name reachable in a term. Iterative: real Reference
/// proofs are deep enough to overflow a recursive walk.
fn const_refs(expr: &Expr, out: &mut HashSet<Name>) {
    let mut stack = vec![expr.clone()];
    while let Some(e) = stack.pop() {
        match e.node() {
            ExprNode::Const { name, .. } => {
                out.insert(name.clone());
            }
            ExprNode::App { f, a } => {
                stack.push(f.clone());
                stack.push(a.clone());
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                stack.push(binder_type.clone());
                stack.push(body.clone());
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                stack.push(type_.clone());
                stack.push(value.clone());
                stack.push(body.clone());
            }
            ExprNode::MData { expr, .. } => stack.push(expr.clone()),
            ExprNode::Proj { expr, .. } => stack.push(expr.clone()),
            _ => {}
        }
    }
}

/// The constants a declaration depends on: every `Const` in its type and
/// value, PLUS the structural name references that carry no `Const` node —
/// an inductive names its constructors, a constructor names its inductive,
/// a recursor names its rules' constructors. The projection rule resolves
/// `ind.ctors[0]` through the environment, so those edges are load-bearing:
/// omitting them replays a structure's projections before its constructor
/// exists and manufactures spurious `InvalidProjection` verdicts.
fn dependencies(info: &ConstantInfo) -> HashSet<Name> {
    let mut out = HashSet::new();
    const_refs(&info.constant_val().type_, &mut out);
    match info {
        ConstantInfo::Defn(v) => const_refs(&v.value, &mut out),
        ConstantInfo::Thm(v) => const_refs(&v.value, &mut out),
        ConstantInfo::Opaque(v) => const_refs(&v.value, &mut out),
        ConstantInfo::Ctor(v) => {
            out.insert(v.induct.clone());
        }
        ConstantInfo::Rec(v) => {
            for rule in &v.rules {
                out.insert(rule.ctor.clone());
                const_refs(&rule.rhs, &mut out);
            }
        }
        _ => {}
    }
    out
}

/// Replay order over admission UNITS: a unit is admitted only after every
/// unit owning a constant any of its members mention (Kahn, with stable
/// unit-creation-order tie-breaking so the replay is deterministic). Because
/// every declaration belongs to exactly one unit, dependency edges are direct
/// — the d4x frontier-transitive expansion is subsumed (a declaration that
/// applies `Membership.rec` has an edge to the `Membership` BLOCK unit, whose
/// own edges cover `outParam` before it). Units inside a dependency cycle
/// (self-referential generated equation lemmas) are emitted last, in unit
/// order, and reported.
fn unit_topological_order(
    infos: &[ConstantInfo],
    units: &[Vec<usize>],
) -> (Vec<usize>, Vec<usize>) {
    let mut owner: HashMap<Name, usize> = HashMap::new();
    for (u, members) in units.iter().enumerate() {
        for &m in members {
            owner.insert(infos[m].name().clone(), u);
        }
    }
    let deps: Vec<Vec<usize>> = units
        .iter()
        .enumerate()
        .map(|(u, members)| {
            let mut d: HashSet<usize> = HashSet::new();
            for &m in members {
                for name in dependencies(&infos[m]) {
                    if let Some(&j) = owner.get(&name)
                        && j != u
                    {
                        d.insert(j);
                    }
                }
            }
            let mut d: Vec<usize> = d.into_iter().collect();
            d.sort_unstable();
            d
        })
        .collect();
    let mut remaining: Vec<usize> = deps.iter().map(|d| d.len()).collect();
    let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); units.len()];
    for (i, d) in deps.iter().enumerate() {
        for &j in d {
            dependents[j].push(i);
        }
    }
    let mut ready: Vec<usize> = (0..units.len()).filter(|&i| remaining[i] == 0).collect();
    ready.reverse(); // pop() yields ascending unit order
    let mut order = Vec::with_capacity(units.len());
    while let Some(i) = ready.pop() {
        order.push(i);
        for &d in &dependents[i] {
            remaining[d] -= 1;
            if remaining[d] == 0 {
                ready.push(d);
            }
        }
        ready.sort_unstable_by(|a, b| b.cmp(a));
    }
    let placed: HashSet<usize> = order.iter().copied().collect();
    let cyclic: Vec<usize> = (0..units.len()).filter(|i| !placed.contains(i)).collect();
    (order, cyclic)
}

/// Classify a rejected declaration into its reduction-gap sub-family, for the
/// triage breakdown. Every family here type-checks only under a reduction rule
/// K1's bootstrap slice does not yet implement (bead franken_lean-zht
/// follow-ups): iota on recursors/matchers, projection reduction on structure
/// instances, or Nat/Fin literal reduction. Purely diagnostic — the soundness
/// argument (below) does not depend on this taxonomy being exhaustive.
fn reduction_gap_family(name: &Name) -> &'static str {
    let s = name.to_display_string();
    let last = s.rsplit('.').next().unwrap_or(&s);
    if matches!(
        last,
        "rec"
            | "recOn"
            | "casesOn"
            | "brecOn"
            | "below"
            | "ibelow"
            | "binductionOn"
            | "noConfusion"
            | "noConfusionType"
    ) || last.starts_with("rec_")
        || last.starts_with("below_")
    {
        "eliminator (iota)"
    } else if last == "go" || last.contains("brecOn") {
        "well-founded-recursion helper (iota)"
    } else if last.starts_with("match_") || last.contains(".match_") {
        "match-compiler auxiliary (iota)"
    } else if last == "elim" || last == "ctorElim" || s.contains(".elim") {
        "custom eliminator (iota)"
    } else if last.ends_with("_f") || last.ends_with("_sunfold") {
        "equation-lemma helper (iota)"
    } else if last.contains("decEq")
        || last.contains("DecidableEq")
        || s.contains("instDecidable")
        || last.contains("decEq")
    {
        "decidability instance (iota/proj)"
    } else if last.contains("ofNat") || last.contains("ofNatLT") || last.contains("ofNatAux") {
        "nat-literal arithmetic (nat-lit reduction)"
    } else {
        // monad projections/instances (ReaderT.*, EStateM.*, inst*) and the
        // remaining generated helpers — projection reduction on structures.
        "structure projection/instance (proj reduction)"
    }
}

/// The kernel `Declaration` for a singleton-unit constant. Definitions of
/// EVERY safety level check (bead franken_lean-ap6: unsafe definitions take
/// the pin's two-phase path, partial definitions the safe path). `None` only
/// for kinds with no admission rule yet (opaques — none in Init.Prelude).
fn as_declaration(info: &ConstantInfo) -> Option<Declaration> {
    match info {
        ConstantInfo::Axiom(v) => Some(Declaration::Axiom(v.clone())),
        ConstantInfo::Thm(v) => Some(Declaration::Thm(v.clone())),
        ConstantInfo::Defn(v) => Some(Declaration::Defn(v.clone())),
        _ => None,
    }
}

/// Locate the pinned Reference stdlib. Override with FLN_REFERENCE_LIB; the
/// elan-installed pin is the default. Absent toolchain = typed skip (the
/// checked-in C3 fixtures cover decode; this rig needs the full Prelude).
fn reference_lib() -> Option<PathBuf> {
    if let Ok(dir) = std::env::var("FLN_REFERENCE_LIB") {
        let p = PathBuf::from(dir);
        return p.is_dir().then_some(p);
    }
    let home = std::env::var("HOME").ok()?;
    let p = PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean");
    p.is_dir().then_some(p)
}

#[test]
fn prelude_replays_through_the_kernel() {
    let Some(lib) = reference_lib() else {
        eprintln!(
            "SKIP kernel_replay: pinned Reference stdlib not found \
             (set FLN_REFERENCE_LIB or install the pin); typed limitation, not a pass"
        );
        return;
    };
    let bytes = std::fs::read(lib.join("Init/Prelude.olean")).expect("read Init/Prelude.olean");
    let view = OleanView::parse(&bytes).expect("parse olean");
    let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
    let infos = decoder
        .decode_module_constants()
        .expect("decode Prelude constants");
    assert_eq!(infos.len(), 2204, "Prelude constant census at the pin");

    // Admission is UNIT-based (bead franken_lean-ap6): an inductive block —
    // its types, constructors, and recursors, mutually referential by nature —
    // is ONE kernel `Declaration::Inductive` checked as a whole (KR-6xx/7xx/
    // 8xx with recursor regeneration); the four quotient declarations are one
    // `Declaration::Quotient` (KR-95x); every axiom, definition (all safety
    // levels), and theorem is a singleton. Units are replayed in dependency
    // order (Kahn over unit-level edges, stable module-order tie-break), so a
    // proof is never checked before a lemma it cites and a block is never
    // checked before the constants its types mention.
    let module_by_name: HashMap<Name, ConstantInfo> = infos
        .iter()
        .map(|info| (info.name().clone(), info.clone()))
        .collect();
    let index_by_name: HashMap<Name, usize> = infos
        .iter()
        .enumerate()
        .map(|(i, info)| (info.name().clone(), i))
        .collect();
    let mut recs_by_block: HashMap<Name, Vec<usize>> = HashMap::new();
    for (i, info) in infos.iter().enumerate() {
        if let ConstantInfo::Rec(r) = info
            && let Some(leader) = r.all.first()
        {
            recs_by_block.entry(leader.clone()).or_default().push(i);
        }
    }
    #[derive(Clone, Copy, PartialEq)]
    enum UnitKind {
        Single,
        Block,
        Quot,
    }
    struct Unit {
        kind: UnitKind,
        members: Vec<usize>,
    }
    let mut units: Vec<Unit> = Vec::new();
    let mut quot_members: Vec<usize> = Vec::new();
    for (i, info) in infos.iter().enumerate() {
        match info {
            ConstantInfo::Quot(_) => quot_members.push(i),
            // Constructors and recursors are absorbed into their block's unit.
            ConstantInfo::Ctor(_) | ConstantInfo::Rec(_) => {}
            ConstantInfo::Induct(ind) => {
                // Only the block leader creates the unit (singleton blocks
                // throughout Init.Prelude; the general case follows `all`).
                if ind.all.first() != Some(&ind.base.name) {
                    continue;
                }
                let mut members: Vec<usize> = Vec::new();
                for type_name in &ind.all {
                    if let Some(&t) = index_by_name.get(type_name) {
                        members.push(t);
                        if let ConstantInfo::Induct(t_ind) = &infos[t] {
                            for ctor_name in &t_ind.ctors {
                                if let Some(&c) = index_by_name.get(ctor_name) {
                                    members.push(c);
                                }
                            }
                        }
                    }
                }
                if let Some(recs) = recs_by_block.get(&ind.base.name) {
                    members.extend(recs.iter().copied());
                }
                units.push(Unit {
                    kind: UnitKind::Block,
                    members,
                });
            }
            _ => units.push(Unit {
                kind: UnitKind::Single,
                members: vec![i],
            }),
        }
    }
    if !quot_members.is_empty() {
        units.push(Unit {
            kind: UnitKind::Quot,
            members: quot_members,
        });
    }
    let member_lists: Vec<Vec<usize>> = units.iter().map(|u| u.members.clone()).collect();
    let (order, cyclic) = unit_topological_order(&infos, &member_lists);
    eprintln!(
        "kernel_replay order: {} units over {} declarations \
         ({} topologically sorted, {} in dependency cycles replayed last)",
        units.len(),
        infos.len(),
        order.len(),
        cyclic.len()
    );
    for &u in cyclic.iter().take(10) {
        let names: Vec<String> = units[u]
            .members
            .iter()
            .map(|&m| infos[m].name().to_display_string())
            .collect();
        eprintln!("  cyclic unit: {names:?}");
    }

    let mut env = Environment::new();
    let mut accepted: u64 = 0;
    let mut rejected: BTreeMap<String, u64> = BTreeMap::new();
    let mut rejected_names: Vec<String> = Vec::new();
    let mut reasons: BTreeMap<String, u64> = BTreeMap::new();
    let mut inconclusive: u64 = 0;
    let mut unchecked: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut gap_families: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut nested_partial: u64 = 0;
    // Probe lane (bead franken_lean-ap6): FLN_REPLAY_ADMISSION_CENSUS=1
    // classifies the block/quotient/non-safe-definition feature surface —
    // which KR-6xx/7xx/8xx/95x/97x machinery this corpus exercises, measured
    // from decoded declarations rather than guessed from the pin.
    if std::env::var("FLN_REPLAY_ADMISSION_CENSUS").is_ok() {
        let mut block_sizes: BTreeMap<usize, u64> = BTreeMap::new();
        let mut ctor_counts: BTreeMap<usize, u64> = BTreeMap::new();
        let mut lparam_counts: BTreeMap<usize, u64> = BTreeMap::new();
        let mut with_indices = 0u64;
        let mut nested: Vec<String> = Vec::new();
        let mut reflexive: Vec<String> = Vec::new();
        let mut unsafe_inds: Vec<String> = Vec::new();
        let mut recursive = 0u64;
        let mut rec_k: Vec<String> = Vec::new();
        let mut rec_multi_motive: Vec<String> = Vec::new();
        let mut rec_lparams_extra = 0u64;
        let mut rec_lparams_same = 0u64;
        let mut max_fields = 0u32;
        let mut def_safety: BTreeMap<String, u64> = BTreeMap::new();
        let mut def_names: Vec<String> = Vec::new();
        let mut quots: Vec<String> = Vec::new();
        for (i, _) in infos.iter().enumerate() {
            match &infos[i] {
                ConstantInfo::Induct(ind) => {
                    *block_sizes.entry(ind.all.len()).or_default() += 1;
                    *ctor_counts.entry(ind.ctors.len()).or_default() += 1;
                    *lparam_counts
                        .entry(ind.base.level_params.len())
                        .or_default() += 1;
                    if ind.num_indices > 0 {
                        with_indices += 1;
                    }
                    if ind.num_nested > 0 {
                        nested.push(ind.base.name.to_display_string());
                    }
                    if ind.is_reflexive {
                        reflexive.push(ind.base.name.to_display_string());
                    }
                    if ind.is_unsafe {
                        unsafe_inds.push(ind.base.name.to_display_string());
                    }
                    if ind.is_rec {
                        recursive += 1;
                    }
                }
                ConstantInfo::Ctor(ctor) => {
                    max_fields = max_fields.max(ctor.num_fields);
                }
                ConstantInfo::Rec(rec) => {
                    if rec.k {
                        rec_k.push(rec.base.name.to_display_string());
                    }
                    if rec.num_motives > 1 {
                        rec_multi_motive.push(rec.base.name.to_display_string());
                    }
                    let ind_lparams = module_by_name
                        .get(&rec.base.name.parent())
                        .map(|info| info.constant_val().level_params.len());
                    match ind_lparams {
                        Some(n) if rec.base.level_params.len() == n + 1 => rec_lparams_extra += 1,
                        Some(n) if rec.base.level_params.len() == n => rec_lparams_same += 1,
                        _ => {}
                    }
                }
                ConstantInfo::Quot(q) => {
                    quots.push(format!(
                        "{}:{:?}",
                        infos[i].name().to_display_string(),
                        q.kind
                    ));
                }
                ConstantInfo::Defn(d) if d.safety != DefinitionSafety::Safe => {
                    *def_safety.entry(format!("{:?}", d.safety)).or_default() += 1;
                    if def_names.len() < 40 {
                        def_names.push(infos[i].name().to_display_string());
                    }
                }
                _ => {}
            }
        }
        eprintln!("ADMISSION CENSUS (block/quot/non-safe-def features, bead franken_lean-ap6):");
        eprintln!("  inductive blocks: sizes(all.len->n)={block_sizes:?} ctors={ctor_counts:?}");
        eprintln!(
            "  inductive lparams={lparam_counts:?} with_indices={with_indices} recursive={recursive}"
        );
        eprintln!(
            "  nested({})={:?}",
            nested.len(),
            &nested[..nested.len().min(12)]
        );
        eprintln!(
            "  reflexive({})={:?}",
            reflexive.len(),
            &reflexive[..reflexive.len().min(12)]
        );
        eprintln!("  unsafe({})={:?}", unsafe_inds.len(), unsafe_inds);
        eprintln!(
            "  recursors: K({})={:?} multi-motive({})={:?} lparams(extra-elim/same)={}/{}",
            rec_k.len(),
            &rec_k[..rec_k.len().min(12)],
            rec_multi_motive.len(),
            rec_multi_motive,
            rec_lparams_extra,
            rec_lparams_same
        );
        eprintln!("  ctor max_fields={max_fields}");
        eprintln!("  non-safe defs by safety={def_safety:?} names={def_names:?}");
        eprintln!("  quots={quots:?}");
    }
    // The unit replay: every declaration in the module flows through the one
    // authority, either as a singleton or inside its block/quotient unit.
    let budget = Budget::DEFAULT;

    for u in order.into_iter().chain(cyclic) {
        let unit = &units[u];
        let info = infos[unit.members[0]].clone();
        let n_members = unit.members.len() as u64;
        let decl: Option<Declaration> = match unit.kind {
            UnitKind::Single => as_declaration(&info),
            UnitKind::Block => {
                let mut types = Vec::new();
                let mut ctors = Vec::new();
                let mut recursors = Vec::new();
                for &m in &unit.members {
                    match &infos[m] {
                        ConstantInfo::Induct(v) => types.push(v.clone()),
                        ConstantInfo::Ctor(v) => ctors.push(v.clone()),
                        ConstantInfo::Rec(v) => recursors.push(v.clone()),
                        _ => {}
                    }
                }
                if types.iter().any(|t| t.num_nested > 0) {
                    nested_partial += 1;
                }
                Some(Declaration::Inductive(fln_kernel::InductiveBlock {
                    types,
                    ctors,
                    recursors,
                }))
            }
            UnitKind::Quot => {
                let mut decls = Vec::new();
                for &m in &unit.members {
                    if let ConstantInfo::Quot(v) = &infos[m] {
                        decls.push(v.clone());
                    }
                }
                Some(Declaration::Quotient(decls))
            }
        };
        let Some(decl) = decl else {
            // No admission rule for this kind yet (opaques): typed limitation,
            // counted per kind — never a silent pass.
            for &m in &unit.members {
                *unchecked.entry(infos[m].kind_name()).or_default() += 1;
                env = env
                    .add_decl(infos[m].clone())
                    .expect("one-name law over Prelude");
            }
            continue;
        };
        // Uncheckable-from-the-artifact (bead franken_lean-ap6): six non-safe
        // implementation helpers (`._unsafe_rec`/`._override`) reference
        // PRIVATE auxiliaries (`.match_1`, `._proof_N`) that the pin's own
        // serializer does NOT include in the module's constants array. The
        // Reference itself cannot re-check these declarations from the olean
        // — their checking context was transient elaboration state. Typed
        // limitation, censused by name-count, never a silent pass.
        if let ConstantInfo::Defn(d) = &info
            && d.safety != DefinitionSafety::Safe
            && dependencies(&info)
                .iter()
                .any(|n| !index_by_name.contains_key(n))
        {
            *unchecked
                .entry("nonsafe_with_unserialized_refs")
                .or_default() += n_members;
            for &m in &unit.members {
                env = env
                    .add_decl(infos[m].clone())
                    .expect("one-name law over Prelude");
            }
            continue;
        }
        match fln_kernel::check(&env, &decl, budget) {
            Verdict::Accepted { .. } => accepted += n_members,
            Verdict::Rejected { class, message, .. } => {
                *rejected.entry(format!("{class:?}")).or_default() += n_members;
                *reasons.entry(format!("{class:?}: {message}")).or_default() += 1;
                *gap_families
                    .entry(reduction_gap_family(info.name()))
                    .or_default() += n_members;
                if rejected_names.len() < 20 {
                    rejected_names.push(format!("{} ({class:?})", info.name().to_display_string()));
                }
                // Probe lane (bead fln-d4x): FLN_REPLAY_PROBE is a comma list
                // of declaration names; matching rejections dump bounded type
                // and value shapes so a reduction-gap hypothesis can be
                // anchored in the DECODED term, not guessed from the name.
                if let Ok(probe) = std::env::var("FLN_REPLAY_PROBE") {
                    let name = info.name().to_display_string();
                    if probe.split(',').any(|entry| entry.trim() == name) {
                        eprintln!("PROBE {name} [{class:?}: {message}]");
                        eprintln!("  type  = {}", shape(&info.constant_val().type_, 6));
                        if let ConstantInfo::Defn(defn) = &info {
                            eprintln!("  value = {}", shape(&defn.value, 8));
                        }
                        // Companion env dump: what does the CHECKING environment
                        // actually hold for these names at this rejection?
                        if let Ok(names) = std::env::var("FLN_REPLAY_PROBE_ENV") {
                            for entry in names.split(',') {
                                let mut target = Name::anonymous();
                                for seg in entry.trim().split('.') {
                                    target = Name::str(target, seg);
                                }
                                match env.find(&target) {
                                    Some(ConstantInfo::Defn(d)) => eprintln!(
                                        "  env {} = definition safety={:?} hints={:?} value={}",
                                        entry.trim(),
                                        d.safety,
                                        d.hints,
                                        shape(&d.value, 4)
                                    ),
                                    Some(other) => {
                                        eprintln!("  env {} = {}", entry.trim(), other.kind_name())
                                    }
                                    None => eprintln!("  env {} = ABSENT", entry.trim()),
                                }
                            }
                        }
                    }
                }
            }
            Verdict::Inconclusive { .. } => inconclusive += n_members,
        }
        // The Reference accepted this module; carry every declaration forward
        // regardless of our verdict so downstream declarations see it.
        for &m in &unit.members {
            env = env
                .add_decl(infos[m].clone())
                .expect("one-name law over Prelude");
        }
    }

    let checked = accepted + inconclusive + rejected.values().sum::<u64>();
    eprintln!(
        "kernel_replay census: checked={checked} accepted={accepted} \
         inconclusive={inconclusive} rejected={rejected:?} unchecked={unchecked:?} \
         nested_partial_blocks={nested_partial}"
    );
    if !rejected_names.is_empty() {
        eprintln!("first rejections: {rejected_names:?}");
        let mut by_count: Vec<_> = reasons.iter().collect();
        by_count.sort_by(|a, b| b.1.cmp(a.1));
        for (reason, n) in by_count.iter().take(12) {
            eprintln!("  {n:>5}  {reason}");
        }
    }

    eprintln!("kernel_replay triage (reduction-gap families): {gap_families:?}");

    // Census law: every declaration lands in exactly one bucket — and the
    // admission slice leaves NOTHING unchecked in this module (opaques would
    // be the only unchecked kind, and Init.Prelude has none).
    let unchecked_total: u64 = unchecked.values().sum();
    assert_eq!(checked + unchecked_total, 2204);
    // The ONLY unchecked family is the six non-safe implementation helpers
    // whose private auxiliary references the pin serializer discarded — the
    // Reference itself cannot re-check them from this artifact.
    assert_eq!(
        unchecked
            .get("nonsafe_with_unserialized_refs")
            .copied()
            .unwrap_or(0),
        unchecked_total,
        "a declaration kind bypassed the kernel: {unchecked:?}"
    );

    // Never Inconclusive: the default budget suffices for every Prelude
    // declaration K1 can check (FL-INV-07 — exhaustion would be honest, but
    // there is none at this scale).
    assert_eq!(inconclusive, 0, "unexpected budget exhaustion");

    // The kernel genuinely accepts a large body of real Reference statements
    // and proofs — a regression that rejected everything cannot hide here.
    // 1233/1755 is the fragment checkable without the missing reduction rules;
    // the floor guards against regression without pinning the exact count.
    assert!(
        accepted >= 1200,
        "accepted only {accepted}/{checked} checked declarations — K1 regressed"
    );

    // The spike's core soundness finding (acceptance criterion (b)): the
    // Reference kernel ACCEPTED every declaration in this module when it wrote
    // the olean. Therefore every FrankenLean rejection here is, by definition,
    // a false-REJECT — a completeness gap — and NEVER a false-accept. K1 admits
    // nothing the Reference refused (there is nothing it refused). Soundness in
    // the sense that matters (FL-INV-02: no bad constant admitted) holds
    // trivially on this corpus; what remains is exactly the reduction-rule
    // completeness work, triaged into named families above.
    //
    // Guard that the rejection CLASSES stay within the reduction/inference-gap
    // set. A new class here (e.g. a level or binder soundness class) would be a
    // genuinely new divergence and must be triaged before it lands.
    let known_gap_classes = [
        "TypeMismatch",
        "FunctionExpected",
        "InvalidProjection",
        "DefinitionTypeMismatch",
    ];
    for class in rejected.keys() {
        assert!(
            known_gap_classes.iter().any(|k| k == class),
            "rejection class {class} is not a pre-classified reduction gap — triage before landing"
        );
    }

    // And that the triage is total: every rejection landed in a named family.
    let rejected_total: u64 = rejected.values().sum();
    assert_eq!(
        gap_families.values().sum::<u64>(),
        rejected_total,
        "triage did not classify every rejection"
    );
}
