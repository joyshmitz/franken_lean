//! Declaration-block admission: inductive families (KR-600..608), elimination
//! universes (KR-700..702), recursor generation (KR-800..803), and quotient
//! initialization (KR-950..954) — bead franken_lean-ap6, transcribed from the
//! pin's `kernel/inductive.cpp` (`add_inductive_fn`) and `kernel/quot.cpp`.
//!
//! The decoded block rows (`InductiveVal`, `ConstructorVal`, `RecursorVal`,
//! `QuotVal`) are UNTRUSTED input: the kernel re-derives every observable —
//! flags, counts, elimination level, K-target, and the full recursor types and
//! iota rules — from the declaration alone and compares against the decoded
//! rows. Any mismatch is a typed [`RejectClass::BlockMismatch`], never a
//! silent trust. One deliberate, documented exception: a block containing
//! NESTED inductives (`num_nested > 0`; exactly `Lean.Syntax` in Init.Prelude)
//! is admitted under a PARTIAL ruleset — well-typedness of every type,
//! constructor, and recursor, parameter/arity cross-checks, but neither
//! strict positivity nor recursor regeneration, because both are defined on
//! the pin's `_nested.*` auxiliary translation (inductive.cpp:800-1100),
//! which operates on the pre-elaboration declaration the olean does not
//! carry. That translation is a named follow-up slice; until it lands the
//! partial family is surfaced by the replay census, not hidden.
//!
//! Traversal discipline matches tc.rs: every helper that recurses carries an
//! explicit depth converted to typed exhaustion, and all typing/reduction work
//! runs through budget-metered [`TypeChecker`] instances.

use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId};
use fln_core::level::Level;
use fln_core::name::{LeafView, Name};
use fln_env::constants::{
    ConstantInfo, ConstructorVal, InductiveVal, QuotKind, QuotVal, RecursorRule, RecursorVal,
};
use fln_env::environment::Environment;

use crate::tc::{Stop, TypeChecker};
use crate::verdict::{Budget, Consumption, ExhaustionReason, RejectClass};

type KResult<T> = Result<T, Stop>;

fn reject<T>(class: RejectClass, message: impl Into<String>) -> KResult<T> {
    Err(Stop::Reject(class, message.into()))
}

/// The decoded, untrusted rows of one inductive block, assembled by the caller
/// (module order preserved within each list).
#[derive(Debug, Clone, PartialEq)]
pub struct InductiveBlock {
    pub types: Vec<InductiveVal>,
    pub ctors: Vec<ConstructorVal>,
    pub recursors: Vec<RecursorVal>,
}

/// A telescope entry: the admission engine's own locals, adopted into every
/// [`TypeChecker`] it spawns. `name`/`info` feed faithful reconstruction when
/// the telescope is re-bound (`mk_pi_locals`/`mk_lam_locals`).
#[derive(Debug, Clone)]
struct Local {
    id: FVarId,
    name: Name,
    info: BinderInfo,
    type_: Expr,
}

impl Local {
    fn fvar(&self) -> Expr {
        Expr::fvar(self.id.clone())
    }
}

/// Depth guard for the engine's own structural walks (abstraction, loose-bvar
/// scans, implicit inference). Declaration types are shallow; this converts a
/// hostile deep term into typed exhaustion, never a stack fault.
const WALK_DEPTH: u32 = 2_048;

fn depth_guard(depth: u32) -> KResult<()> {
    if depth > WALK_DEPTH {
        return Err(Stop::Exhausted(ExhaustionReason::Depth));
    }
    Ok(())
}

/// Replace `fvar id` by `bvar k` (k bumped under binders) — the inverse of
/// instantiation, used to re-bind engine telescopes.
fn abstract_fvar(e: &Expr, id: &FVarId, k: u32, depth: u32) -> KResult<Expr> {
    depth_guard(depth)?;
    if !e.has_fvar() {
        return Ok(e.clone());
    }
    Ok(match e.node() {
        ExprNode::FVar { id: found } => {
            if found == id {
                Expr::bvar(k).map_err(|_| Stop::Exhausted(ExhaustionReason::Depth))?
            } else {
                e.clone()
            }
        }
        ExprNode::App { f, a } => Expr::app(
            abstract_fvar(f, id, k, depth + 1)?,
            abstract_fvar(a, id, k, depth + 1)?,
        ),
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::lam(
            binder_name.clone(),
            abstract_fvar(binder_type, id, k, depth + 1)?,
            abstract_fvar(body, id, k + 1, depth + 1)?,
            *binder_info,
        ),
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::forall_e(
            binder_name.clone(),
            abstract_fvar(binder_type, id, k, depth + 1)?,
            abstract_fvar(body, id, k + 1, depth + 1)?,
            *binder_info,
        ),
        ExprNode::LetE {
            decl_name,
            type_,
            value,
            body,
            non_dep,
        } => Expr::let_e(
            decl_name.clone(),
            abstract_fvar(type_, id, k, depth + 1)?,
            abstract_fvar(value, id, k, depth + 1)?,
            abstract_fvar(body, id, k + 1, depth + 1)?,
            *non_dep,
        ),
        ExprNode::MData { data, expr } => {
            Expr::mdata(data.clone(), abstract_fvar(expr, id, k, depth + 1)?)
        }
        ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } => Expr::proj(
            struct_name.clone(),
            *idx,
            abstract_fvar(expr, id, k, depth + 1)?,
        ),
        _ => e.clone(),
    })
}

/// `Π locals, body` — right fold with abstraction (pin `local_ctx::mk_pi`).
fn mk_pi_locals(locals: &[Local], body: Expr) -> KResult<Expr> {
    let mut acc = body;
    for local in locals.iter().rev() {
        let abstracted = abstract_fvar(&acc, &local.id, 0, 0)?;
        acc = Expr::forall_e(
            local.name.clone(),
            local.type_.clone(),
            abstracted,
            local.info,
        );
    }
    Ok(acc)
}

/// `λ locals, body` — right fold with abstraction (pin `local_ctx::mk_lambda`).
fn mk_lam_locals(locals: &[Local], body: Expr) -> KResult<Expr> {
    let mut acc = body;
    for local in locals.iter().rev() {
        let abstracted = abstract_fvar(&acc, &local.id, 0, 0)?;
        acc = Expr::lam(
            local.name.clone(),
            local.type_.clone(),
            abstracted,
            local.info,
        );
    }
    Ok(acc)
}

/// Does `bvar idx` occur loose in `e`? Range-pruned.
fn has_loose_bvar(e: &Expr, idx: u32, depth: u32) -> KResult<bool> {
    depth_guard(depth)?;
    if e.loose_bvar_range() <= idx {
        return Ok(false);
    }
    Ok(match e.node() {
        ExprNode::BVar { idx: found } => *found == idx,
        ExprNode::App { f, a } => {
            has_loose_bvar(f, idx, depth + 1)? || has_loose_bvar(a, idx, depth + 1)?
        }
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => {
            has_loose_bvar(binder_type, idx, depth + 1)?
                || has_loose_bvar(body, idx + 1, depth + 1)?
        }
        ExprNode::LetE {
            type_, value, body, ..
        } => {
            has_loose_bvar(type_, idx, depth + 1)?
                || has_loose_bvar(value, idx, depth + 1)?
                || has_loose_bvar(body, idx + 1, depth + 1)?
        }
        ExprNode::MData { expr, .. } => has_loose_bvar(expr, idx, depth + 1)?,
        ExprNode::Proj { expr, .. } => has_loose_bvar(expr, idx, depth + 1)?,
        _ => false,
    })
}

/// `has_loose_bvars_in_domain` (pin expr.cpp:370): does `bvar vidx` occur in a
/// (transitively relevant) Π domain of `b`?
fn has_loose_bvars_in_domain(b: &Expr, vidx: u32, strict: bool, depth: u32) -> KResult<bool> {
    depth_guard(depth)?;
    if let ExprNode::ForallE {
        binder_type,
        body,
        binder_info,
        ..
    } = b.node()
    {
        if has_loose_bvar(binder_type, vidx, depth + 1)?
            && (*binder_info == BinderInfo::Default
                || has_loose_bvars_in_domain(body, 0, strict, depth + 1)?)
        {
            return Ok(true);
        }
        has_loose_bvars_in_domain(body, vidx + 1, strict, depth + 1)
    } else if !strict {
        has_loose_bvar(b, vidx, depth)
    } else {
        Ok(false)
    }
}

/// `infer_implicit` (pin expr.cpp:480, strict): mark leading Π binders
/// implicit when a later domain (transitively) needs them.
fn infer_implicit_strict(t: &Expr, depth: u32) -> KResult<Expr> {
    depth_guard(depth)?;
    let ExprNode::ForallE {
        binder_name,
        binder_type,
        body,
        binder_info,
    } = t.node()
    else {
        return Ok(t.clone());
    };
    let new_body = infer_implicit_strict(body, depth + 1)?;
    let info = if *binder_info != BinderInfo::Default {
        *binder_info
    } else if has_loose_bvars_in_domain(&new_body, 0, true, depth + 1)? {
        BinderInfo::Implicit
    } else {
        BinderInfo::Default
    };
    Ok(Expr::forall_e(
        binder_name.clone(),
        binder_type.clone(),
        new_body,
        info,
    ))
}

/// `mk_rec_name` (inductive.cpp:22).
fn mk_rec_name(ind: &Name) -> Name {
    Name::str(ind.clone(), "rec")
}

/// `consumeTypeAnnotations` (vendor Lean/Expr.lean:1741, applied by the pin's
/// `mk_local_decl` to every telescope local): strip head applications of the
/// type-annotation gadgets — `outParam`/`semiOutParam` at arity 1 keep their
/// argument, `optParam`/`autoParam` at arity 2 keep their FIRST argument.
/// Nested annotations are not removed, exactly as at the pin.
fn consume_type_annotations(e: &Expr) -> Expr {
    fn gadget(e: &Expr) -> Option<Expr> {
        let mut args: Vec<&Expr> = Vec::new();
        let mut head = e;
        while let ExprNode::App { f, a } = head.node() {
            args.push(a);
            head = f;
        }
        args.reverse();
        let ExprNode::Const { name, .. } = head.node() else {
            return None;
        };
        if !name.parent().is_anonymous() {
            return None;
        }
        match name.leaf_view() {
            LeafView::Str(s) if (s == "outParam" || s == "semiOutParam") && args.len() == 1 => {
                Some(args[0].clone())
            }
            LeafView::Str(s) if (s == "optParam" || s == "autoParam") && args.len() == 2 => {
                Some(args[0].clone())
            }
            _ => None,
        }
    }
    let mut current = e.clone();
    while let Some(inner) = gadget(&current) {
        current = inner;
    }
    current
}

/// `Name.hasMacroScopes` (vendor Init/Meta/Defs.lean hygiene encoding): the
/// leaf-side walk skips numeric scope components; the first string component
/// must be the `_hyg` marker.
fn has_macro_scopes(n: &Name) -> bool {
    let mut cur = n.clone();
    loop {
        match cur.leaf_view() {
            LeafView::Num(_) => cur = cur.parent(),
            LeafView::Str(s) => return s == "_hyg",
            LeafView::Anonymous => return false,
        }
    }
}

/// `Name.appendAfter` (vendor Init/Meta/Defs.lean:317): macro-scope aware —
/// the suffix lands on the BASE name (the part before the `_@` scope marker),
/// and the scope components are re-attached verbatim. On the base: a string
/// leaf is extended in place; anything else gains a new string component.
fn append_after(n: &Name, suffix: &str) -> Name {
    #[derive(Clone)]
    enum Comp {
        Str(String),
        Num(u64),
    }
    fn split(n: &Name) -> Vec<Comp> {
        let mut out = Vec::new();
        let mut cur = n.clone();
        loop {
            match cur.leaf_view() {
                LeafView::Str(s) => out.push(Comp::Str(s.to_string())),
                LeafView::Num(v) => out.push(Comp::Num(v)),
                LeafView::Anonymous => break,
            }
            cur = cur.parent();
        }
        out.reverse();
        out
    }
    fn rebuild(comps: &[Comp], onto: Name) -> Name {
        let mut cur = onto;
        for c in comps {
            cur = match c {
                Comp::Str(s) => Name::str(cur, s.clone()),
                Comp::Num(v) => Name::num(cur, *v),
            };
        }
        cur
    }
    fn append_base(n: &Name, suffix: &str) -> Name {
        match n.leaf_view() {
            LeafView::Str(s) => Name::str(n.parent(), format!("{s}{suffix}")),
            _ => Name::str(n.clone(), suffix.to_string()),
        }
    }
    if !has_macro_scopes(n) {
        return append_base(n, suffix);
    }
    let comps = split(n);
    let Some(marker) = comps
        .iter()
        .position(|c| matches!(c, Comp::Str(s) if s == "_@"))
    else {
        return append_base(n, suffix);
    };
    let base = rebuild(&comps[..marker], Name::anonymous());
    let appended = append_base(&base, suffix);
    rebuild(&comps[marker..], appended)
}

/// `name::replace_prefix(prefix, anonymous)` for the minor-premise names
/// (inductive.cpp:670): strip `prefix` off the front when it matches.
fn strip_prefix(n: &Name, prefix: &Name) -> Name {
    fn components(n: &Name) -> Vec<Name> {
        let mut out = Vec::new();
        let mut cur = n.clone();
        while !cur.is_anonymous() {
            out.push(cur.clone());
            cur = cur.parent();
        }
        out.reverse();
        out
    }
    let n_parts = components(n);
    let p_parts = components(prefix);
    if p_parts.len() > n_parts.len() || n_parts[p_parts.len() - 1] != *prefix {
        return n.clone();
    }
    let mut rebuilt = Name::anonymous();
    for part in &n_parts[p_parts.len()..] {
        rebuilt = match part.leaf_view() {
            LeafView::Str(s) => Name::str(rebuilt, s.to_string()),
            LeafView::Num(v) => Name::num(rebuilt, v),
            LeafView::Anonymous => rebuilt,
        };
    }
    rebuilt
}

/// The block-admission engine (pin `add_inductive_fn`). Owns the evolving
/// scratch environment, the telescope, and the budget meter.
struct Engine<'a> {
    env: Environment,
    block: &'a InductiveBlock,
    lparams: Vec<Name>,
    levels: Vec<Level>,
    nparams: usize,
    is_unsafe: bool,
    budget: Budget,
    used: Consumption,
    locals: Vec<Local>,
    fresh: u64,
    // Filled by the phases:
    params: Vec<Local>,
    nindices: Vec<usize>,
    ind_consts: Vec<Expr>,
    result_level: Level,
    result_is_not_zero: bool,
    elim_level: Level,
    k_target: bool,
}

/// Per-datatype recursor scaffolding (pin `rec_info`).
struct RecInfo {
    motive: Local,
    minors: Vec<Local>,
    indices: Vec<Local>,
    major: Local,
}

impl<'a> Engine<'a> {
    fn new(env: &Environment, block: &'a InductiveBlock, budget: Budget) -> KResult<Engine<'a>> {
        let first = block.types.first().ok_or_else(|| {
            Stop::Reject(RejectClass::BlockMismatch, "empty inductive block".into())
        })?;
        let lparams = first.base.level_params.clone();
        let levels: Vec<Level> = lparams.iter().cloned().map(Level::param).collect();
        Ok(Engine {
            env: env.clone(),
            block,
            lparams,
            levels,
            nparams: first.num_params as usize,
            is_unsafe: first.is_unsafe,
            budget,
            used: Consumption::default(),
            locals: Vec::new(),
            fresh: 0,
            params: Vec::new(),
            nindices: Vec::new(),
            ind_consts: Vec::new(),
            result_level: Level::zero(),
            result_is_not_zero: false,
            elim_level: Level::zero(),
            k_target: false,
        })
    }

    fn remaining(&self) -> Budget {
        Budget {
            steps: self.budget.steps.saturating_sub(self.used.steps_used),
            depth: self.budget.depth,
        }
    }

    fn charge(&mut self, c: Consumption) -> KResult<()> {
        self.used.steps_used = self.used.steps_used.saturating_add(c.steps_used);
        self.used.max_depth = self.used.max_depth.max(c.max_depth);
        if self.used.steps_used > self.budget.steps {
            return Err(Stop::Exhausted(ExhaustionReason::Steps));
        }
        Ok(())
    }

    /// Spawn a metered checker over the CURRENT scratch env with the full
    /// telescope adopted, run `f`, absorb consumption.
    fn with_tc<T>(&mut self, f: impl FnOnce(&mut TypeChecker<'_>) -> KResult<T>) -> KResult<T> {
        let remaining = self.remaining();
        let safety = if self.is_unsafe {
            fln_env::constants::DefinitionSafety::Unsafe
        } else {
            fln_env::constants::DefinitionSafety::Safe
        };
        let mut tc = TypeChecker::new_with_safety(&self.env, &self.lparams, remaining, safety);
        for local in &self.locals {
            tc.adopt_local(local.id.clone(), local.type_.clone());
        }
        let result = f(&mut tc);
        let consumption = tc.consumption();
        drop(tc);
        self.charge(consumption)?;
        result
    }

    fn mk_local(&mut self, name: Name, type_: Expr, info: BinderInfo) -> Local {
        self.fresh += 1;
        let local = Local {
            id: FVarId(Name::num(Name::str(Name::anonymous(), "_adm"), self.fresh)),
            name,
            info,
            // Pin mk_local_decl (inductive.cpp:178): every telescope local's
            // type sheds its annotation gadgets — this is why generated
            // recursor binders read `Type w`, not `outParam (Type w)`.
            type_: consume_type_annotations(&type_),
        };
        self.locals.push(local.clone());
        local
    }

    /// `mk_local_decl_for`: a local from the head binder of a Π.
    fn mk_local_for(&mut self, pi: &Expr) -> KResult<Local> {
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            binder_info,
            ..
        } = pi.node()
        else {
            return reject(RejectClass::BlockMismatch, "expected a Π type");
        };
        Ok(self.mk_local(binder_name.clone(), binder_type.clone(), *binder_info))
    }

    /// Instantiate a Π body with a local's fvar.
    fn open_pi(&mut self, pi: &Expr, local: &Local) -> KResult<Expr> {
        let ExprNode::ForallE { body, .. } = pi.node() else {
            return reject(RejectClass::BlockMismatch, "expected a Π type");
        };
        let body = body.clone();
        let fvar = local.fvar();
        self.with_tc(|tc| tc.instantiate(&body, 0, &fvar, 0))
    }

    // ---- KR-600..602: the types ------------------------------------------------------

    fn check_inductive_types(&mut self) -> KResult<()> {
        let types = self.block.types.to_vec();
        let mut first = true;
        for ind in &types {
            let name = &ind.base.name;
            // KR-600: freshness of the type name and its recursor name; the
            // decoded row's block facts must be self-consistent.
            if self.env.contains(name) {
                return reject(
                    RejectClass::AlreadyDeclared,
                    format!("`{}` is already declared", name.to_display_string()),
                );
            }
            if self.env.contains(&mk_rec_name(name)) {
                return reject(
                    RejectClass::AlreadyDeclared,
                    format!(
                        "recursor name `{}` is already declared",
                        mk_rec_name(name).to_display_string()
                    ),
                );
            }
            if ind.base.level_params != self.lparams {
                return reject(
                    RejectClass::BlockMismatch,
                    "block members must share level parameters",
                );
            }
            if ind.num_params as usize != self.nparams {
                return reject(
                    RejectClass::BlockMismatch,
                    "block members must share the parameter count",
                );
            }
            if ind.is_unsafe != self.is_unsafe {
                return reject(
                    RejectClass::BlockMismatch,
                    "block members must share the safety flag",
                );
            }
            let type_ = ind.base.type_.clone();
            if type_.has_fvar() || type_.has_expr_mvar() || type_.loose_bvar_range() > 0 {
                return reject(
                    RejectClass::MVarInKernel,
                    "inductive type must be closed (no mvars/fvars)",
                );
            }
            // Well-typedness of the type itself.
            self.with_tc(|tc| tc.infer(&type_, 0))?;

            // Telescope walk: shared params (KR-601), per-type indices.
            let mut indices = 0usize;
            let mut t = self.with_tc(|tc| tc.whnf_public(&type_, 0))?;
            let mut i = 0usize;
            while let ExprNode::ForallE { binder_type, .. } = t.node() {
                let binder_type = binder_type.clone();
                if i < self.nparams {
                    if first {
                        let param = self.mk_local_for(&t)?;
                        t = self.open_pi(&t, &param)?;
                        self.params.push(param);
                    } else {
                        let expected = self.params[i].type_.clone();
                        let matches =
                            self.with_tc(|tc| tc.def_eq_public(&binder_type, &expected, 0))?;
                        if !matches {
                            return reject(
                                RejectClass::BlockMismatch,
                                "parameters of all inductive datatypes must match",
                            );
                        }
                        let param = self.params[i].clone();
                        t = self.open_pi(&t, &param)?;
                    }
                } else {
                    let index = self.mk_local_for(&t)?;
                    t = self.open_pi(&t, &index)?;
                    indices += 1;
                }
                i += 1;
                t = self.with_tc(|tc| tc.whnf_public(&t, 0))?;
            }
            if i < self.nparams {
                return reject(
                    RejectClass::BlockMismatch,
                    "number of parameters mismatch in inductive datatype declaration",
                );
            }
            // KR-602: the residual must be a sort; one universe per block.
            let ExprNode::Sort { level } = t.node() else {
                return reject(
                    RejectClass::SortExpected,
                    "inductive type must end in a sort",
                );
            };
            if first {
                self.result_level = level.clone();
                self.result_is_not_zero = level.is_not_zero();
            } else if !level.is_equiv(&self.result_level) {
                return reject(
                    RejectClass::BlockMismatch,
                    "mutually inductive types must live in the same universe",
                );
            }
            // Decoded-row cross-check: num_indices.
            if ind.num_indices as usize != indices {
                return reject(
                    RejectClass::BlockMismatch,
                    format!(
                        "`{}`: decoded num_indices={} but the type has {}",
                        name.to_display_string(),
                        ind.num_indices,
                        indices
                    ),
                );
            }
            self.nindices.push(indices);
            self.ind_consts
                .push(Expr::const_(name.clone(), self.levels.clone()));
            first = false;
        }
        Ok(())
    }

    // ---- KR-607: flags -----------------------------------------------------------------

    fn block_names(&self) -> Vec<Name> {
        self.block
            .types
            .iter()
            .map(|t| t.base.name.clone())
            .collect()
    }

    fn mentions_block(&self, e: &Expr) -> bool {
        let names = self.block_names();
        fn walk(e: &Expr, names: &[Name]) -> bool {
            match e.node() {
                ExprNode::Const { name, .. } => names.contains(name),
                ExprNode::App { f, a } => walk(f, names) || walk(a, names),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => walk(binder_type, names) || walk(body, names),
                ExprNode::LetE {
                    type_, value, body, ..
                } => walk(type_, names) || walk(value, names) || walk(body, names),
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => walk(expr, names),
                _ => false,
            }
        }
        walk(e, &names)
    }

    /// KR-607: recursive iff some constructor field domain mentions the block.
    fn compute_is_rec(&mut self) -> KResult<bool> {
        for ctor in &self.block.ctors {
            let mut t = ctor.base.type_.clone();
            while let ExprNode::ForallE {
                binder_type, body, ..
            } = t.node()
            {
                if self.mentions_block(binder_type) {
                    return Ok(true);
                }
                let next = body.clone();
                t = next;
            }
        }
        Ok(false)
    }

    /// KR-607: reflexive iff some field is a function type whose body mentions
    /// a block member. (Pin walks with locals; occurrence checking is
    /// substitution-invariant, so the raw bvar walk is equivalent.)
    fn compute_is_reflexive(&mut self) -> KResult<bool> {
        for ctor in &self.block.ctors {
            let mut t = ctor.base.type_.clone();
            while let ExprNode::ForallE {
                binder_type, body, ..
            } = t.node()
            {
                if matches!(binder_type.node(), ExprNode::ForallE { .. })
                    && self.mentions_block(binder_type)
                {
                    return Ok(true);
                }
                let next = body.clone();
                t = next;
            }
        }
        Ok(false)
    }

    // ---- KR-603..606: constructors ----------------------------------------------------

    /// KR-605 (`is_valid_ind_app`): `I_i params indices`, param positions
    /// syntactically the declared params, and no index argument mentions the
    /// block.
    fn is_valid_ind_app_at(&self, t: &Expr, i: usize) -> bool {
        let mut args: Vec<&Expr> = Vec::new();
        let mut head = t;
        while let ExprNode::App { f, a } = head.node() {
            args.push(a);
            head = f;
        }
        args.reverse();
        if *head != self.ind_consts[i] || args.len() != self.nparams + self.nindices[i] {
            return false;
        }
        for (j, param) in self.params.iter().enumerate() {
            if *args[j] != param.fvar() {
                return false;
            }
        }
        for arg in &args[self.nparams..] {
            if self.mentions_block(arg) {
                return false;
            }
        }
        true
    }

    fn valid_ind_app_index(&self, t: &Expr) -> Option<usize> {
        (0..self.block.types.len()).find(|&i| self.is_valid_ind_app_at(t, i))
    }

    /// Is `t` (a field type) a recursive argument: `Π xs, I_i params indices`?
    fn is_rec_argument(&mut self, t: &Expr) -> KResult<Option<usize>> {
        let mut t = self.with_tc(|tc| tc.whnf_public(t, 0))?;
        while matches!(t.node(), ExprNode::ForallE { .. }) {
            let local = self.mk_local_for(&t)?;
            let body = self.open_pi(&t, &local)?;
            t = self.with_tc(|tc| tc.whnf_public(&body, 0))?;
        }
        Ok(self.valid_ind_app_index(&t))
    }

    /// KR-606 strict positivity.
    fn check_positivity(
        &mut self,
        t: &Expr,
        ctor: &Name,
        arg_idx: usize,
        depth: u32,
    ) -> KResult<()> {
        depth_guard(depth)?;
        let t = self.with_tc(|tc| tc.whnf_public(t, 0))?;
        if !self.mentions_block(&t) {
            return Ok(()); // non-recursive argument
        }
        if matches!(t.node(), ExprNode::ForallE { .. }) {
            let ExprNode::ForallE { binder_type, .. } = t.node() else {
                unreachable!("matched above");
            };
            if self.mentions_block(binder_type) {
                return reject(
                    RejectClass::BlockMismatch,
                    format!(
                        "arg #{} of `{}` has a non positive occurrence of the datatypes being declared",
                        arg_idx + 1,
                        ctor.to_display_string()
                    ),
                );
            }
            let local = self.mk_local_for(&t)?;
            let body = self.open_pi(&t, &local)?;
            return self.check_positivity(&body, ctor, arg_idx, depth + 1);
        }
        if self.valid_ind_app_index(&t).is_some() {
            return Ok(()); // recursive argument
        }
        reject(
            RejectClass::BlockMismatch,
            format!(
                "arg #{} of `{}` contains a non valid occurrence of the datatypes being declared",
                arg_idx + 1,
                ctor.to_display_string()
            ),
        )
    }

    /// KR-603/604/605/606 + decoded-row cross-checks, for every constructor.
    /// `check_valid_app`/`check_positive` are switched off on the nested
    /// partial path.
    fn check_constructors(&mut self, full: bool) -> KResult<()> {
        for (idx, ind) in self.block.types.iter().enumerate() {
            let declared: Vec<&ConstructorVal> = self
                .block
                .ctors
                .iter()
                .filter(|c| c.induct == ind.base.name)
                .collect();
            // The decoded parent lists ctors in cidx order; verify the match.
            if ind.ctors.len() != declared.len() {
                return reject(
                    RejectClass::BlockMismatch,
                    "decoded ctor list does not match the block's constructors",
                );
            }
            for (cidx, ctor) in declared.iter().enumerate() {
                let name = &ctor.base.name;
                if ind.ctors.get(cidx) != Some(name) {
                    return reject(
                        RejectClass::BlockMismatch,
                        format!(
                            "decoded ctor order mismatch at `{}`",
                            name.to_display_string()
                        ),
                    );
                }
                if self.env.contains(name) {
                    return reject(
                        RejectClass::AlreadyDeclared,
                        format!("`{}` is already declared", name.to_display_string()),
                    );
                }
                if ctor.base.level_params != self.lparams
                    || ctor.cidx as usize != cidx
                    || ctor.num_params as usize != self.nparams
                    || ctor.is_unsafe != self.is_unsafe
                {
                    return reject(
                        RejectClass::BlockMismatch,
                        format!(
                            "decoded constructor observables mismatch at `{}`",
                            name.to_display_string()
                        ),
                    );
                }
                let t0 = ctor.base.type_.clone();
                if t0.has_fvar() || t0.has_expr_mvar() || t0.loose_bvar_range() > 0 {
                    return reject(
                        RejectClass::MVarInKernel,
                        "constructor type must be closed (no mvars/fvars)",
                    );
                }
                self.with_tc(|tc| tc.infer(&t0, 0))?;
                let mut t = t0;
                let mut i = 0usize;
                let mut fields = 0usize;
                while matches!(t.node(), ExprNode::ForallE { .. }) {
                    let ExprNode::ForallE { binder_type, .. } = t.node() else {
                        unreachable!("matched above");
                    };
                    let binder_type = binder_type.clone();
                    if i < self.nparams {
                        let expected = self.params[i].type_.clone();
                        let matches =
                            self.with_tc(|tc| tc.def_eq_public(&binder_type, &expected, 0))?;
                        if !matches {
                            return reject(
                                RejectClass::BlockMismatch,
                                format!(
                                    "arg #{} of `{}` does not match inductive datatypes parameters",
                                    i + 1,
                                    name.to_display_string()
                                ),
                            );
                        }
                        let param = self.params[i].clone();
                        t = self.open_pi(&t, &param)?;
                    } else {
                        // KR-604: the field's universe fits the datatype (or Prop).
                        let field_sort = self.with_tc(|tc| {
                            let s = tc.infer(&binder_type, 0)?;
                            tc.whnf_public(&s, 0)
                        })?;
                        let ExprNode::Sort { level } = field_sort.node() else {
                            return reject(
                                RejectClass::SortExpected,
                                format!(
                                    "arg #{} of `{}` is not a type",
                                    i + 1,
                                    name.to_display_string()
                                ),
                            );
                        };
                        if !(self.result_level.is_geq(level) || self.result_level.is_zero()) {
                            return reject(
                                RejectClass::BlockMismatch,
                                format!(
                                    "universe level of type_of(arg #{}) of `{}` is too big for the corresponding inductive datatype",
                                    i + 1,
                                    name.to_display_string()
                                ),
                            );
                        }
                        if full && !self.is_unsafe {
                            self.check_positivity(&binder_type, name, i, 0)?;
                        }
                        let local = self.mk_local_for(&t)?;
                        t = self.open_pi(&t, &local)?;
                        fields += 1;
                    }
                    i += 1;
                }
                if full && self.valid_ind_app_index(&t) != Some(idx) {
                    return reject(
                        RejectClass::BlockMismatch,
                        format!("invalid return type for `{}`", name.to_display_string()),
                    );
                }
                if ctor.num_fields as usize != fields {
                    return reject(
                        RejectClass::BlockMismatch,
                        format!(
                            "decoded num_fields mismatch at `{}`",
                            name.to_display_string()
                        ),
                    );
                }
            }
        }
        Ok(())
    }

    // ---- KR-700..702: elimination universe --------------------------------------------

    /// KR-700/701 (`elim_only_at_universe_zero`).
    fn elim_only_at_universe_zero(&mut self) -> KResult<bool> {
        if self.result_is_not_zero {
            return Ok(false);
        }
        if self.block.types.len() > 1 {
            return Ok(true);
        }
        let ctors: Vec<ConstructorVal> = self
            .block
            .ctors
            .iter()
            .filter(|c| c.induct == self.block.types[0].base.name)
            .cloned()
            .collect();
        if ctors.len() > 1 {
            return Ok(true);
        }
        let Some(ctor) = ctors.first() else {
            return Ok(false); // empty inductive predicate eliminates large
        };
        // KR-701: single constructor — every non-param field is a Prop or
        // occurs among the result's arguments.
        let mut t = ctor.base.type_.clone();
        let mut i = 0usize;
        let mut to_check: Vec<Local> = Vec::new();
        while matches!(t.node(), ExprNode::ForallE { .. }) {
            let local = if i < self.nparams {
                self.params[i].clone()
            } else {
                let l = self.mk_local_for(&t)?;
                let field_sort = self.with_tc(|tc| {
                    let s = tc.infer(&l.type_.clone(), 0)?;
                    tc.whnf_public(&s, 0)
                })?;
                if !matches!(field_sort.node(), ExprNode::Sort { level } if level.is_zero()) {
                    to_check.push(l.clone());
                }
                l
            };
            t = self.open_pi(&t, &local)?;
            i += 1;
        }
        let mut result_args: Vec<Expr> = Vec::new();
        let mut head = t.clone();
        while let ExprNode::App { f, a } = head.node() {
            result_args.push(a.clone());
            let next = f.clone();
            head = next;
        }
        for local in &to_check {
            if !result_args.iter().any(|arg| *arg == local.fvar()) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// KR-702: the elimination level — `0`, or a fresh `u`-family parameter.
    fn init_elim_level(&mut self) -> KResult<()> {
        if self.elim_only_at_universe_zero()? {
            self.elim_level = Level::zero();
        } else {
            let mut u = Name::str(Name::anonymous(), "u");
            let mut i = 1u64;
            while self.lparams.contains(&u) {
                u = append_after(&Name::str(Name::anonymous(), "u"), &format!("_{i}"));
                i += 1;
            }
            self.elim_level = Level::param(u);
        }
        Ok(())
    }

    /// K-target (pin `init_K_target`): single type, Prop, one ctor, no fields.
    fn init_k_target(&mut self) {
        self.k_target = self.block.types.len() == 1
            && self.result_level.is_zero()
            && self.block.types[0].ctors.len() == 1
            && self
                .block
                .ctors
                .iter()
                .filter(|c| c.induct == self.block.types[0].base.name)
                .all(|c| c.num_fields == 0);
    }

    // ---- KR-800..803: recursor generation ---------------------------------------------

    fn rec_levels(&self) -> Vec<Level> {
        if matches!(self.elim_level.view(), fln_core::level::LevelView::Param(_)) {
            let mut out = vec![self.elim_level.clone()];
            out.extend(self.levels.iter().cloned());
            out
        } else {
            self.levels.clone()
        }
    }

    fn rec_lparams(&self) -> Vec<Name> {
        if let fln_core::level::LevelView::Param(u) = self.elim_level.view() {
            let mut out = vec![u.clone()];
            out.extend(self.lparams.iter().cloned());
            out
        } else {
            self.lparams.clone()
        }
    }

    /// Split a ctor type telescope into (field locals, rec-arg locals, result).
    fn open_ctor_fields(
        &mut self,
        ctor: &ConstructorVal,
    ) -> KResult<(Vec<Local>, Vec<Local>, Expr)> {
        let mut b_u = Vec::new();
        let mut u = Vec::new();
        let mut t = ctor.base.type_.clone();
        let mut i = 0usize;
        while matches!(t.node(), ExprNode::ForallE { .. }) {
            if i < self.nparams {
                let param = self.params[i].clone();
                t = self.open_pi(&t, &param)?;
            } else {
                let ExprNode::ForallE { binder_type, .. } = t.node() else {
                    unreachable!("matched above");
                };
                let binder_type = binder_type.clone();
                let local = self.mk_local_for(&t)?;
                b_u.push(local.clone());
                if self.is_rec_argument(&binder_type)?.is_some() {
                    u.push(local.clone());
                }
                t = self.open_pi(&t, &local)?;
            }
            i += 1;
        }
        Ok((b_u, u, t))
    }

    /// `I As is` → (datatype index, indices).
    fn get_ind_indices(&self, t: &Expr) -> KResult<(usize, Vec<Expr>)> {
        let Some(idx) = self.valid_ind_app_index(t) else {
            return reject(
                RejectClass::BlockMismatch,
                "constructor result is not a valid inductive application",
            );
        };
        let mut args: Vec<Expr> = Vec::new();
        let mut head = t.clone();
        while let ExprNode::App { f, a } = head.node() {
            args.push(a.clone());
            let next = f.clone();
            head = next;
        }
        args.reverse();
        Ok((idx, args[self.nparams..].to_vec()))
    }

    /// KR-800/801: motives, indices, majors, and minor premises.
    fn mk_rec_infos(&mut self) -> KResult<Vec<RecInfo>> {
        let mut infos: Vec<RecInfo> = Vec::new();
        // Motives, indices, majors.
        for (d_idx, ind) in self.block.types.iter().enumerate() {
            let mut t = self.with_tc(|tc| tc.whnf_public(&ind.base.type_.clone(), 0))?;
            let mut i = 0usize;
            let mut indices: Vec<Local> = Vec::new();
            while matches!(t.node(), ExprNode::ForallE { .. }) {
                if i < self.nparams {
                    let param = self.params[i].clone();
                    t = self.open_pi(&t, &param)?;
                } else {
                    let index = self.mk_local_for(&t)?;
                    t = self.open_pi(&t, &index)?;
                    indices.push(index);
                }
                i += 1;
                t = self.with_tc(|tc| tc.whnf_public(&t, 0))?;
            }
            let mut major_type = self.ind_consts[d_idx].clone();
            for param in &self.params {
                major_type = Expr::app(major_type, param.fvar());
            }
            for index in &indices {
                major_type = Expr::app(major_type, index.fvar());
            }
            let major = self.mk_local(
                Name::str(Name::anonymous(), "t"),
                major_type,
                BinderInfo::Default,
            );
            let mut motive_ty = Expr::sort(self.elim_level.clone());
            motive_ty = mk_pi_locals(std::slice::from_ref(&major), motive_ty)?;
            motive_ty = mk_pi_locals(&indices, motive_ty)?;
            let motive_name = if self.block.types.len() > 1 {
                append_after(
                    &Name::str(Name::anonymous(), "motive"),
                    &format!("_{}", d_idx + 1),
                )
            } else {
                Name::str(Name::anonymous(), "motive")
            };
            let motive = self.mk_local(motive_name, motive_ty, BinderInfo::Default);
            infos.push(RecInfo {
                motive,
                minors: Vec::new(),
                indices,
                major,
            });
        }
        // Minor premises (KR-801).
        for (d_idx, ind) in self.block.types.iter().enumerate() {
            let declared: Vec<ConstructorVal> = self
                .block
                .ctors
                .iter()
                .filter(|c| c.induct == ind.base.name)
                .cloned()
                .collect();
            for ctor in &declared {
                let (b_u, u, result) = self.open_ctor_fields(ctor)?;
                let (it_idx, it_indices) = self.get_ind_indices(&result)?;
                let mut c_app = infos[it_idx].motive.fvar();
                for index in &it_indices {
                    c_app = Expr::app(c_app, index.clone());
                }
                let mut intro_app = Expr::const_(ctor.base.name.clone(), self.levels.clone());
                for param in &self.params {
                    intro_app = Expr::app(intro_app, param.fvar());
                }
                for field in &b_u {
                    intro_app = Expr::app(intro_app, field.fvar());
                }
                c_app = Expr::app(c_app, intro_app);
                // Induction hypotheses.
                let mut v: Vec<Local> = Vec::new();
                for u_i in &u {
                    let mut u_i_ty = self.with_tc(|tc| tc.whnf_public(&u_i.type_.clone(), 0))?;
                    let mut xs: Vec<Local> = Vec::new();
                    while matches!(u_i_ty.node(), ExprNode::ForallE { .. }) {
                        let x = self.mk_local_for(&u_i_ty)?;
                        let body = self.open_pi(&u_i_ty, &x)?;
                        xs.push(x);
                        u_i_ty = self.with_tc(|tc| tc.whnf_public(&body, 0))?;
                    }
                    let (rec_idx, rec_indices) = self.get_ind_indices(&u_i_ty)?;
                    let mut ih_c = infos[rec_idx].motive.fvar();
                    for index in &rec_indices {
                        ih_c = Expr::app(ih_c, index.clone());
                    }
                    let mut u_app = u_i.fvar();
                    for x in &xs {
                        u_app = Expr::app(u_app, x.fvar());
                    }
                    ih_c = Expr::app(ih_c, u_app);
                    let ih_ty = mk_pi_locals(&xs, ih_c)?;
                    let ih =
                        self.mk_local(append_after(&u_i.name, "_ih"), ih_ty, BinderInfo::Default);
                    v.push(ih);
                }
                let minor_ty = mk_pi_locals(&b_u, mk_pi_locals(&v, c_app)?)?;
                let minor_name = strip_prefix(&ctor.base.name, &ind.base.name);
                let minor = self.mk_local(minor_name, minor_ty, BinderInfo::Default);
                infos[d_idx].minors.push(minor);
            }
        }
        Ok(infos)
    }

    /// KR-803: the iota right-hand sides for datatype `d_idx`.
    fn mk_rec_rules(
        &mut self,
        infos: &[RecInfo],
        cs: &[Local],
        minors: &[Local],
        d_idx: usize,
        minor_idx: &mut usize,
    ) -> KResult<Vec<RecursorRule>> {
        let ind = &self.block.types[d_idx].clone();
        let rec_levels = self.rec_levels();
        let declared: Vec<ConstructorVal> = self
            .block
            .ctors
            .iter()
            .filter(|c| c.induct == ind.base.name)
            .cloned()
            .collect();
        let mut rules = Vec::new();
        for ctor in &declared {
            let (b_u, u, _result) = self.open_ctor_fields(ctor)?;
            let mut v: Vec<Expr> = Vec::new();
            for u_i in &u {
                let mut u_i_ty = self.with_tc(|tc| tc.whnf_public(&u_i.type_.clone(), 0))?;
                let mut xs: Vec<Local> = Vec::new();
                while matches!(u_i_ty.node(), ExprNode::ForallE { .. }) {
                    let x = self.mk_local_for(&u_i_ty)?;
                    let body = self.open_pi(&u_i_ty, &x)?;
                    xs.push(x);
                    u_i_ty = self.with_tc(|tc| tc.whnf_public(&body, 0))?;
                }
                let (rec_idx, rec_indices) = self.get_ind_indices(&u_i_ty)?;
                let rec_name = mk_rec_name(&self.block.types[rec_idx].base.name);
                let mut rec_app = Expr::const_(rec_name, rec_levels.clone());
                for param in &self.params {
                    rec_app = Expr::app(rec_app, param.fvar());
                }
                for c in cs {
                    rec_app = Expr::app(rec_app, c.fvar());
                }
                for minor in minors {
                    rec_app = Expr::app(rec_app, minor.fvar());
                }
                for index in &rec_indices {
                    rec_app = Expr::app(rec_app, index.clone());
                }
                let mut u_app = u_i.fvar();
                for x in &xs {
                    u_app = Expr::app(u_app, x.fvar());
                }
                rec_app = Expr::app(rec_app, u_app);
                v.push(mk_lam_locals(&xs, rec_app)?);
            }
            let mut e_app = minors[*minor_idx].fvar();
            for field in &b_u {
                e_app = Expr::app(e_app, field.fvar());
            }
            for ih in &v {
                e_app = Expr::app(e_app, ih.clone());
            }
            let comp_rhs = mk_lam_locals(
                &self.params.clone(),
                mk_lam_locals(cs, mk_lam_locals(minors, mk_lam_locals(&b_u, e_app)?)?)?,
            )?;
            rules.push(RecursorRule {
                ctor: ctor.base.name.clone(),
                nfields: b_u.len() as u32,
                rhs: comp_rhs,
            });
            *minor_idx += 1;
        }
        let _ = infos;
        Ok(rules)
    }

    /// KR-802: regenerate every recursor of the block from its declaration
    /// alone — the block's decoded recursor rows are never consulted. One
    /// `RecursorVal` per datatype, in block order.
    fn generate_recursors(&mut self) -> KResult<Vec<RecursorVal>> {
        let infos = self.mk_rec_infos()?;
        let cs: Vec<Local> = infos.iter().map(|i| i.motive.clone()).collect();
        let minors: Vec<Local> = infos.iter().flat_map(|i| i.minors.clone()).collect();
        let nminors = minors.len() as u32;
        let nmotives = cs.len() as u32;
        let all = self.block_names();
        let mut minor_idx = 0usize;
        let mut generated = Vec::with_capacity(infos.len());
        for (d_idx, info) in infos.iter().enumerate() {
            let mut c_app = info.motive.fvar();
            for index in &info.indices {
                c_app = Expr::app(c_app, index.fvar());
            }
            c_app = Expr::app(c_app, info.major.fvar());
            let mut rec_ty = mk_pi_locals(std::slice::from_ref(&info.major), c_app)?;
            rec_ty = mk_pi_locals(&info.indices, rec_ty)?;
            rec_ty = mk_pi_locals(&minors, rec_ty)?;
            rec_ty = mk_pi_locals(&cs, rec_ty)?;
            rec_ty = mk_pi_locals(&self.params.clone(), rec_ty)?;
            rec_ty = infer_implicit_strict(&rec_ty, 0)?;
            let rules = self.mk_rec_rules(&infos, &cs, &minors, d_idx, &mut minor_idx)?;
            let rec_name = mk_rec_name(&self.block.types[d_idx].base.name);
            generated.push(RecursorVal {
                base: fln_env::constants::ConstantVal {
                    name: rec_name.clone(),
                    level_params: self.rec_lparams(),
                    type_: rec_ty,
                },
                all: all.clone(),
                num_params: self.nparams as u32,
                num_indices: self.nindices[d_idx] as u32,
                num_motives: nmotives,
                num_minors: nminors,
                rules,
                k: self.k_target,
                is_unsafe: self.is_unsafe,
            });
        }
        Ok(generated)
    }

    /// KR-802 + the ap6 cross-check: regenerate every recursor and compare it
    /// field-by-field against the DECODED rows.
    fn check_recursors(&mut self) -> KResult<()> {
        if self.block.recursors.len() != self.block.types.len() {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "block declares {} recursors, expected {}",
                    self.block.recursors.len(),
                    self.block.types.len()
                ),
            );
        }
        let generated = self.generate_recursors()?;
        for (d_idx, generated) in generated.iter().enumerate() {
            let decoded = &self.block.recursors[d_idx];
            compare_recursors(generated, decoded)?;
        }
        Ok(())
    }

    // ---- driver ------------------------------------------------------------------------

    fn run(&mut self) -> KResult<()> {
        // KR-971 on the block's level parameters.
        for (i, p) in self.lparams.iter().enumerate() {
            if self.lparams[..i].contains(p) {
                return reject(
                    RejectClass::DuplicateLevelParams,
                    format!(
                        "duplicate universe level parameter `{}`",
                        p.to_display_string()
                    ),
                );
            }
        }
        let nested = self.block.types.iter().any(|t| t.num_nested > 0);
        self.check_inductive_types()?;
        // KR-607 flags + block observables, cross-checked against every row.
        let is_rec = self.compute_is_rec()?;
        let is_reflexive = self.compute_is_reflexive()?;
        let all = self.block_names();
        for ind in &self.block.types {
            if ind.all != all {
                return reject(
                    RejectClass::BlockMismatch,
                    format!(
                        "decoded `all` list mismatch at `{}`",
                        ind.base.name.to_display_string()
                    ),
                );
            }
            if !nested && (ind.is_rec != is_rec || ind.is_reflexive != is_reflexive) {
                return reject(
                    RejectClass::BlockMismatch,
                    format!(
                        "decoded recursivity flags mismatch at `{}` (is_rec {} vs {}, is_reflexive {} vs {})",
                        ind.base.name.to_display_string(),
                        ind.is_rec,
                        is_rec,
                        ind.is_reflexive,
                        is_reflexive
                    ),
                );
            }
        }
        // Declare the types (pin declare_inductive_types), then check ctors
        // against the extended scratch env.
        for ind in &self.block.types {
            self.env = self
                .env
                .add_decl(ConstantInfo::Induct(ind.clone()))
                .map_err(|_| {
                    Stop::Reject(
                        RejectClass::AlreadyDeclared,
                        format!(
                            "`{}` is already declared",
                            ind.base.name.to_display_string()
                        ),
                    )
                })?;
        }
        self.check_constructors(!nested)?;
        for ctor in &self.block.ctors {
            self.env = self
                .env
                .add_decl(ConstantInfo::Ctor(ctor.clone()))
                .map_err(|_| {
                    Stop::Reject(
                        RejectClass::AlreadyDeclared,
                        format!(
                            "`{}` is already declared",
                            ctor.base.name.to_display_string()
                        ),
                    )
                })?;
        }
        if nested {
            return self.check_nested_partial();
        }
        self.init_elim_level()?;
        self.init_k_target();
        self.check_recursors()
    }

    /// The documented nested-partial ruleset: recursor types and rule
    /// right-hand sides must TYPECHECK against the block (with the decoded
    /// recursors admitted for the mutual references), but neither positivity
    /// nor regeneration runs — both live behind the pin's `_nested.*`
    /// translation (follow-up slice; see the module doc).
    fn check_nested_partial(&mut self) -> KResult<()> {
        for rec in &self.block.recursors {
            self.env = self
                .env
                .add_decl(ConstantInfo::Rec(rec.clone()))
                .map_err(|_| {
                    Stop::Reject(
                        RejectClass::AlreadyDeclared,
                        format!(
                            "`{}` is already declared",
                            rec.base.name.to_display_string()
                        ),
                    )
                })?;
        }
        for rec in &self.block.recursors.to_vec() {
            let lparams = rec.base.level_params.clone();
            let type_ = rec.base.type_.clone();
            let remaining = self.remaining();
            let mut tc = TypeChecker::new(&self.env, &lparams, remaining);
            let outcome = tc.infer(&type_, 0);
            let consumption = tc.consumption();
            drop(tc);
            self.charge(consumption)?;
            outcome?;
            for rule in &rec.rules {
                let rhs = rule.rhs.clone();
                let remaining = self.remaining();
                let mut tc = TypeChecker::new(&self.env, &lparams, remaining);
                let outcome = tc.infer(&rhs, 0);
                let consumption = tc.consumption();
                drop(tc);
                self.charge(consumption)?;
                outcome?;
            }
        }
        Ok(())
    }
}

/// Field-by-field comparison of a regenerated recursor against the decoded
/// row. Types and rule right-hand sides compare STRUCTURALLY (the decoded rows
/// were produced by this same algorithm at the pin, so faithful regeneration
/// is byte-identical); the divergence locator pinpoints any drift.
fn compare_recursors(generated: &RecursorVal, decoded: &RecursorVal) -> KResult<()> {
    let name = decoded.base.name.to_display_string();
    if generated.base.name != decoded.base.name {
        return reject(
            RejectClass::BlockMismatch,
            format!(
                "recursor name mismatch: generated `{}`, decoded `{name}`",
                generated.base.name.to_display_string()
            ),
        );
    }
    if generated.base.level_params != decoded.base.level_params {
        return reject(
            RejectClass::BlockMismatch,
            format!("`{name}`: recursor level parameters diverge from regeneration"),
        );
    }
    if generated.all != decoded.all
        || generated.num_params != decoded.num_params
        || generated.num_indices != decoded.num_indices
        || generated.num_motives != decoded.num_motives
        || generated.num_minors != decoded.num_minors
        || generated.k != decoded.k
        || generated.is_unsafe != decoded.is_unsafe
    {
        return reject(
            RejectClass::BlockMismatch,
            format!(
                "`{name}`: recursor observables diverge from regeneration \
                 (params {}/{}, indices {}/{}, motives {}/{}, minors {}/{}, k {}/{})",
                generated.num_params,
                decoded.num_params,
                generated.num_indices,
                decoded.num_indices,
                generated.num_motives,
                decoded.num_motives,
                generated.num_minors,
                decoded.num_minors,
                generated.k,
                decoded.k
            ),
        );
    }
    if generated.base.type_ != decoded.base.type_ {
        return reject(
            RejectClass::BlockMismatch,
            format!(
                "`{name}`: recursor type diverges from regeneration{}",
                divergence_note(&generated.base.type_, &decoded.base.type_)
            ),
        );
    }
    if generated.rules.len() != decoded.rules.len() {
        return reject(
            RejectClass::BlockMismatch,
            format!("`{name}`: rule count diverges from regeneration"),
        );
    }
    for (g, d) in generated.rules.iter().zip(&decoded.rules) {
        if g.ctor != d.ctor || g.nfields != d.nfields {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "`{name}`: rule for `{}` diverges (nfields {}/{})",
                    d.ctor.to_display_string(),
                    g.nfields,
                    d.nfields
                ),
            );
        }
        if g.rhs != d.rhs {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "`{name}`: iota rhs for `{}` diverges from regeneration{}",
                    d.ctor.to_display_string(),
                    divergence_note(&g.rhs, &d.rhs)
                ),
            );
        }
    }
    Ok(())
}

fn divergence_note(generated: &Expr, decoded: &Expr) -> String {
    match crate::tc::first_divergence_public(generated, decoded) {
        Some(d) => format!(" (first divergence: {d})"),
        None => String::new(),
    }
}

/// The pin's expression equality (`expr_eq_fn<false>`, kernel/expr_eq_fn.cpp):
/// structural, with binder NAMES and binder INFOS ignored. This is the
/// comparison quot.cpp's `!=` checks actually perform — the decoded `Eq` type
/// carries hygienic binder names that alpha-vary from the pin's constructed
/// expected form.
fn pin_expr_eq(a: &Expr, b: &Expr) -> bool {
    if a == b {
        return true;
    }
    match (a.node(), b.node()) {
        (ExprNode::BVar { idx: i1 }, ExprNode::BVar { idx: i2 }) => i1 == i2,
        (ExprNode::FVar { id: id1 }, ExprNode::FVar { id: id2 }) => id1 == id2,
        (ExprNode::Sort { level: l1 }, ExprNode::Sort { level: l2 }) => l1 == l2,
        (
            ExprNode::Const {
                name: n1,
                levels: l1,
            },
            ExprNode::Const {
                name: n2,
                levels: l2,
            },
        ) => n1 == n2 && l1 == l2,
        (ExprNode::App { f: f1, a: a1 }, ExprNode::App { f: f2, a: a2 }) => {
            pin_expr_eq(f1, f2) && pin_expr_eq(a1, a2)
        }
        (
            ExprNode::Lam {
                binder_type: t1,
                body: b1,
                ..
            },
            ExprNode::Lam {
                binder_type: t2,
                body: b2,
                ..
            },
        )
        | (
            ExprNode::ForallE {
                binder_type: t1,
                body: b1,
                ..
            },
            ExprNode::ForallE {
                binder_type: t2,
                body: b2,
                ..
            },
        ) => pin_expr_eq(t1, t2) && pin_expr_eq(b1, b2),
        (
            ExprNode::LetE {
                type_: t1,
                value: v1,
                body: b1,
                ..
            },
            ExprNode::LetE {
                type_: t2,
                value: v2,
                body: b2,
                ..
            },
        ) => pin_expr_eq(t1, t2) && pin_expr_eq(v1, v2) && pin_expr_eq(b1, b2),
        (ExprNode::Lit { literal: l1 }, ExprNode::Lit { literal: l2 }) => l1 == l2,
        (ExprNode::MData { expr: e1, .. }, ExprNode::MData { expr: e2, .. }) => pin_expr_eq(e1, e2),
        (
            ExprNode::Proj {
                struct_name: n1,
                idx: i1,
                expr: e1,
            },
            ExprNode::Proj {
                struct_name: n2,
                idx: i2,
                expr: e2,
            },
        ) => n1 == n2 && i1 == i2 && pin_expr_eq(e1, e2),
        _ => false,
    }
}

/// Entry: check one inductive block (types + ctors + recursors, decoded and
/// untrusted) against `env` under `budget`.
pub(crate) fn check_inductive_block(
    env: &Environment,
    block: &InductiveBlock,
    budget: Budget,
) -> (KResult<()>, Consumption) {
    match Engine::new(env, block, budget) {
        Ok(mut engine) => {
            let out = engine.run();
            (out, engine.used)
        }
        Err(stop) => (Err(stop), Consumption::default()),
    }
}

// ---- Quotients (KR-950..954) ---------------------------------------------------------

fn arrow(a: Expr, b: Expr) -> Expr {
    // pin `mk_arrow` (expr.cpp:181): binder named `a`, default info.
    Expr::forall_e(Name::str(Name::anonymous(), "a"), a, b, BinderInfo::Default)
}

fn pi(name: &str, info: BinderInfo, type_: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::str(Name::anonymous(), name), type_, body, info)
}

/// KR-950: the environment's `Eq` must be the expected one-parameter,
/// one-constructor equality (types compared structurally, as at the pin).
fn check_eq_type(env: &Environment) -> KResult<()> {
    let eq_name = Name::str(Name::anonymous(), "Eq");
    let Some(ConstantInfo::Induct(eq)) = env.find(&eq_name) else {
        return reject(
            RejectClass::BlockMismatch,
            "failed to initialize quot module, environment does not have 'Eq' type",
        );
    };
    if eq.base.level_params.len() != 1 || eq.ctors.len() != 1 {
        return reject(
            RejectClass::BlockMismatch,
            "failed to initialize quot module, unexpected 'Eq' shape",
        );
    }
    let u = Level::param(eq.base.level_params[0].clone());
    // ∀ {α : Sort u}, α → α → Prop  (bvars: α at the binder)
    let alpha = Expr::bvar(0).expect("packs");
    let alpha1 = Expr::bvar(1).expect("packs");
    let expected = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        arrow(alpha.clone(), {
            // inner arrow shifts α to bvar 1
            arrow(alpha1.clone(), Expr::sort(Level::zero()))
        }),
    );
    if !pin_expr_eq(&eq.base.type_, &expected) {
        return reject(
            RejectClass::BlockMismatch,
            format!(
                "failed to initialize quot module, 'Eq' has an unexpected type{}",
                divergence_note(&expected, &eq.base.type_)
            ),
        );
    }
    let refl_name = eq.ctors[0].clone();
    let Some(ConstantInfo::Ctor(refl)) = env.find(&refl_name) else {
        return reject(
            RejectClass::BlockMismatch,
            "failed to initialize quot module, 'Eq' constructor is missing",
        );
    };
    if refl.base.level_params.len() != 1 {
        return reject(
            RejectClass::BlockMismatch,
            "failed to initialize quot module, unexpected 'Eq' constructor shape",
        );
    }
    let u = Level::param(refl.base.level_params[0].clone());
    // ∀ {α : Sort u} (a : α), Eq.{u} α a a
    let expected_refl = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        pi(
            "a",
            BinderInfo::Default,
            Expr::bvar(0).expect("packs"),
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(eq_name, vec![u]),
                        Expr::bvar(1).expect("packs"),
                    ),
                    Expr::bvar(0).expect("packs"),
                ),
                Expr::bvar(0).expect("packs"),
            ),
        ),
    );
    if !pin_expr_eq(&refl.base.type_, &expected_refl) {
        return reject(
            RejectClass::BlockMismatch,
            format!(
                "failed to initialize quot module, unexpected type for 'Eq' type constructor{}",
                divergence_note(&expected_refl, &refl.base.type_)
            ),
        );
    }
    Ok(())
}

/// KR-951..954: the four quotient declarations, types built exactly as the
/// pin builds them (quot.cpp:59-97) and compared structurally against the
/// decoded rows.
pub(crate) fn check_quotient_init(
    env: &Environment,
    decls: &[QuotVal],
    _budget: Budget,
) -> (KResult<()>, Consumption) {
    let out = check_quotient_inner(env, decls);
    (out, Consumption::default())
}

fn check_quotient_inner(env: &Environment, decls: &[QuotVal]) -> KResult<()> {
    check_eq_type(env)?;
    let quot = Name::str(Name::anonymous(), "Quot");
    let u_name = Name::str(Name::anonymous(), "u");
    let v_name = Name::str(Name::anonymous(), "v");
    let u = Level::param(u_name.clone());
    let v = Level::param(v_name.clone());
    let prop = || Expr::sort(Level::zero());
    let bv = |i: u32| Expr::bvar(i).expect("packs");
    // Quot.{u} : ∀ {α : Sort u}, (α → α → Prop) → Sort u
    let quot_ty = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        arrow(arrow(bv(0), arrow(bv(1), prop())), Expr::sort(u.clone())),
    );
    // Quot.mk.{u} : ∀ {α : Sort u} (r : α → α → Prop) (a : α), @Quot.{u} α r
    let quot_app = |alpha: Expr, r: Expr| {
        Expr::app(
            Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), alpha),
            r,
        )
    };
    let quot_mk_ty = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        pi(
            "r",
            BinderInfo::Default,
            arrow(bv(0), arrow(bv(1), prop())),
            pi("a", BinderInfo::Default, bv(1), quot_app(bv(2), bv(1))),
        ),
    );
    // Quot.lift.{u,v} :
    //   ∀ {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β),
    //     (∀ (a b : α), r a b → f a = f b) → @Quot.{u} α r → β
    let eq_name = Name::str(Name::anonymous(), "Eq");
    // Binders (outer→inner): α(0 shifts as we descend), r, β, f, then the
    // sanity premise Π a Π b, (arrow) — bvar arithmetic done per position.
    let sanity = pi(
        "a",
        BinderInfo::Default,
        bv(3), // α from under f: binders α r β f → a sees α at 3
        pi(
            "b",
            BinderInfo::Default,
            bv(4),
            arrow(
                Expr::app(Expr::app(bv(4), bv(1)), bv(0)), // r a b (r at 4 under a,b,+arrow-domain? see note)
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::const_(eq_name, vec![v.clone()]), bv(4)), // β
                        Expr::app(bv(3), bv(2)),                                  // f a
                    ),
                    Expr::app(bv(3), bv(1)), // f b
                ),
            ),
        ),
    );
    let quot_lift_ty = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        pi(
            "r",
            BinderInfo::Implicit,
            arrow(bv(0), arrow(bv(1), prop())),
            pi(
                "β",
                BinderInfo::Implicit,
                Expr::sort(v.clone()),
                pi(
                    "f",
                    BinderInfo::Default,
                    arrow(bv(2), bv(1)),
                    arrow(
                        sanity,
                        arrow(
                            {
                                // @Quot.{u} α r with α at 4, r at 3 (under f + sanity-arrow)
                                Expr::app(
                                    Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), bv(4)),
                                    bv(3),
                                )
                            },
                            bv(3), // β
                        ),
                    ),
                ),
            ),
        ),
    );
    // Quot.ind.{u} :
    //   ∀ {α : Sort u} {r : α → α → Prop} {β : @Quot.{u} α r → Prop},
    //     (∀ (a : α), β (@Quot.mk.{u} α r a)) → ∀ (q : @Quot.{u} α r), β q
    let quot_mk = Name::str(quot.clone(), "mk");
    let quot_ind_ty = pi(
        "α",
        BinderInfo::Implicit,
        Expr::sort(u.clone()),
        pi(
            "r",
            BinderInfo::Implicit,
            arrow(bv(0), arrow(bv(1), prop())),
            pi(
                "β",
                BinderInfo::Implicit,
                arrow(
                    Expr::app(
                        Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), bv(1)),
                        bv(0),
                    ),
                    prop(),
                ),
                pi(
                    "mk",
                    BinderInfo::Default,
                    pi(
                        "a",
                        BinderInfo::Default,
                        bv(2), // α
                        Expr::app(
                            bv(1), // β
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::const_(quot_mk.clone(), vec![u.clone()]),
                                        bv(3), // α
                                    ),
                                    bv(2), // r
                                ),
                                bv(0), // a
                            ),
                        ),
                    ),
                    pi(
                        "q",
                        BinderInfo::Default,
                        Expr::app(
                            Expr::app(Expr::const_(quot.clone(), vec![u.clone()]), bv(3)),
                            bv(2),
                        ),
                        Expr::app(bv(2), bv(0)), // β q
                    ),
                ),
            ),
        ),
    );
    let expected: Vec<(Name, Vec<Name>, Expr, QuotKind)> = vec![
        (quot.clone(), vec![u_name.clone()], quot_ty, QuotKind::Type),
        (
            Name::str(quot.clone(), "mk"),
            vec![u_name.clone()],
            quot_mk_ty,
            QuotKind::Ctor,
        ),
        (
            Name::str(quot.clone(), "lift"),
            vec![u_name.clone(), v_name],
            quot_lift_ty,
            QuotKind::Lift,
        ),
        (
            Name::str(quot.clone(), "ind"),
            vec![u_name],
            quot_ind_ty,
            QuotKind::Ind,
        ),
    ];
    if decls.len() != expected.len() {
        return reject(
            RejectClass::BlockMismatch,
            format!(
                "quotient initialization needs 4 declarations, got {}",
                decls.len()
            ),
        );
    }
    for (name, lparams, type_, kind) in &expected {
        let Some(decoded) = decls.iter().find(|d| &d.base.name == name) else {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "quotient declaration `{}` missing",
                    name.to_display_string()
                ),
            );
        };
        if env.contains(name) {
            return reject(
                RejectClass::AlreadyDeclared,
                format!("`{}` is already declared", name.to_display_string()),
            );
        }
        if decoded.kind != *kind || decoded.base.level_params != *lparams {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "quotient declaration `{}` has unexpected kind or level parameters",
                    name.to_display_string()
                ),
            );
        }
        if !pin_expr_eq(&decoded.base.type_, type_) {
            return reject(
                RejectClass::BlockMismatch,
                format!(
                    "quotient declaration `{}` type diverges from the pin's construction{}",
                    name.to_display_string(),
                    divergence_note(type_, &decoded.base.type_)
                ),
            );
        }
    }
    Ok(())
}
