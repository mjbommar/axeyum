//! Kernel-checked Tseitin CNF-introduction reconstruction.

use std::collections::BTreeMap;

use axeyum_cnf::{AletheLit, AletheTerm};
use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, ExprNode, ReducibilityHint};

use super::{
    GatePropAlias, ReconstructCtx, ReconstructError, bit_of_operand_resolves, bv_bit, check_against,
    ex_falso, fresh_fvar_id, normalize_lit_polarity, or_inl, or_inr,
};

// ===========================================================================
// Tseitin CNF-introduction rules (P3.7 slice 4) — the Boolean-gate layer.
//
// These are the premise-free Alethe rules `and_pos`/`and_neg`/`or_pos`/`or_neg`,
// `equiv_pos1`/`equiv_pos2`/`equiv_neg1`/`equiv_neg2`, and
// `xor_pos1`/`xor_pos2`/`xor_neg1`/`xor_neg2`. Each concludes a propositional
// **tautology** clause over the structured logical gate (`And`/`Or`/`Iff`/`Not`)
// of its operand atoms — the clauses a Tseitin encoding emits to connect a
// Boolean gate to its defining clauses. axeyum's QF_BV proofs use these to link
// the bit-blasted gate layer to the clausal (resolution) layer.
//
// ## The gate encoding
//
// Unlike the opaque clausal `atom_to_prop`, these rules are *about* gate
// structure, so a gate literal is translated **structurally**:
//
// - `(and t…)` ⇒ `And ⟦t0⟧ (And ⟦t1⟧ …)` (right-nested for n-ary);
// - `(or t…)`  ⇒ `Or  ⟦t0⟧ (Or  ⟦t1⟧ …)` (right-nested);
// - `(not t)`  ⇒ `Not ⟦t⟧`;
// - `(= a b)`  ⇒ `Iff ⟦a⟧ ⟦b⟧` (a Boolean equality, i.e. an iff — the gate
//   operands in the Tseitin layer are bits);
// - `(xor a b)` ⇒ `Not (Iff ⟦a⟧ ⟦b⟧)` — **the xor modeling choice** (xor is the
//   negation of iff). This is consistent across all four `xor_*` rules.
// - anything else (a bare symbol, or a compound axeyum keys opaquely, e.g.
//   `((_ @bit_of i) x)`) ⇒ an opaque propositional atom (via `prop_atoms`).
//
// ## How each tautology is proved
//
// Every conclusion clause is a propositional tautology over its operand atoms.
// We prove it **uniformly**: case-split (classically, via `em`) on every
// distinct operand atom of the clause, and in each of the resulting truth
// assignments find a clause literal that is satisfied and inject its proof into
// the right-nested `Or` encoding. The per-literal proof is a structural
// truth/falsity evaluator over the gate (`prove_term_true`/`prove_term_false`):
// e.g. `And A B` is true by `And.intro` when both hold, and false by
// `fun h => hnA (And.rec … h)` when an operand is false.
//
// ## Soundness
//
// The kernel is the gate: the assembled proof term is `infer`-checked and
// `def_eq`-compared against the clause's `Or`-encoding (`gate_clause_to_prop`).
// A wrong conclusion (a mis-selected conjunct, a swapped polarity) makes the
// satisfied-literal search fail in some leaf, or the final `infer`/`def_eq`
// reject — never a wrong "checked". `em` (already in the context) is the only
// classical addition.
// ===========================================================================

impl ReconstructCtx {
    /// Build the Lean proposition `And a b` (the prelude's `And`, in `Prop`).
    pub(super) fn mk_and(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let and = self.kernel.const_(self.prelude.and, vec![]);
        let e = self.kernel.app(and, a);
        self.kernel.app(e, b)
    }

    /// Build the Lean proposition `Iff a b` (the prelude's `Iff`, in `Prop`).
    pub(super) fn mk_iff(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let iff = self.kernel.const_(self.prelude.iff, vec![]);
        let e = self.kernel.app(iff, a);
        self.kernel.app(e, b)
    }

    /// Translate a **gate** term into its *structured* Lean `Prop`. Boolean
    /// connectives map to the prelude connectives applied to the translated
    /// operands; everything else is an opaque propositional atom (shared with the
    /// clausal layer's `prop_atoms`).
    ///
    /// `(and …)`/`(or …)` are right-nested for n-ary arity; `(= a b)` is `Iff`;
    /// `(xor a b)` is `Not (Iff a b)`.
    ///
    /// In **bit mode** an atom whose s-expression key is a registered bit-vector
    /// predicate is first rewritten to its bit-level Boolean form `B` (via the
    /// `bridge` map) and then translated structurally — so the predicate `Prop`
    /// *is* its bit form. The substitution fires before the structural match, so
    /// e.g. `(= (bvand a b) a)` becomes `B`'s `And`/`Iff` tree, not an `Iff` over
    /// the opaque bit-vector terms.
    pub(super) fn begin_gate_prop_aliases(&mut self) {
        assert!(
            self.gate_prop_aliases.is_none(),
            "gate proposition alias scope must not be nested"
        );
        self.gate_memo.clear();
        self.gate_prop_aliases = Some(Vec::new());
    }

    pub(super) fn finish_gate_prop_aliases(&mut self, mut proof: ExprId) -> ExprId {
        let aliases = self
            .gate_prop_aliases
            .take()
            .expect("gate proposition alias scope must be active");
        self.gate_memo.clear();
        let fvars = aliases.iter().map(|alias| alias.fvar).collect::<Vec<_>>();
        proof = self.kernel.abstract_fvars(proof, &fvars);
        let prop = self.kernel.sort_zero();
        for index in (0..aliases.len()).rev() {
            let alias = &aliases[index];
            let value = self
                .kernel
                .abstract_fvars(alias.value, &fvars[..index]);
            proof = self.kernel.let_(alias.name, prop, value, proof);
        }
        proof
    }

    pub(super) fn begin_global_gate_prop_aliases(&mut self) {
        assert!(
            self.gate_prop_aliases.is_none() && !self.closed_aliases.gate_props,
            "gate proposition alias scopes must not be nested"
        );
        self.gate_memo.clear();
        self.global_gate_prop_alias_error = None;
        self.closed_aliases.gate_props = true;
    }

    pub(super) fn finish_global_gate_prop_aliases(&mut self) -> Result<(), ReconstructError> {
        self.closed_aliases.gate_props = false;
        self.gate_memo.clear();
        match self.global_gate_prop_alias_error.take() {
            Some(detail) => Err(ReconstructError::KernelRejected {
                rule: "global_gate_prop_alias".to_owned(),
                detail,
            }),
            None => Ok(()),
        }
    }

    pub(super) fn gate_term_to_prop(&mut self, term: &AletheTerm) -> ExprId {
        let key = term.key();
        if let Some(&cached) = self.gate_memo.get(&key) {
            return cached;
        }
        let mut result = self.gate_term_to_prop_inner(term);
        let should_alias = self.gate_prop_aliases.is_some()
            && matches!(
                self.kernel.expr_node(result),
                ExprNode::App(..) | ExprNode::Lam(..) | ExprNode::Pi(..) | ExprNode::Let(..)
            );
        if should_alias {
            let fvar = fresh_fvar_id(self);
            let name = self.fresh_name("gate_prop");
            self.gate_prop_aliases
                .as_mut()
                .expect("gate proposition alias scope is active")
                .push(GatePropAlias {
                    fvar,
                    name,
                    value: result,
                });
            result = self.kernel.fvar(fvar);
        } else if self.closed_aliases.gate_props
            && matches!(
                self.kernel.expr_node(result),
                ExprNode::App(..) | ExprNode::Lam(..) | ExprNode::Pi(..) | ExprNode::Let(..)
            )
        {
            let name = self.fresh_name("gate_prop");
            let prop = self.kernel.sort_zero();
            let declaration = Declaration::Definition {
                name,
                uparams: vec![],
                ty: prop,
                value: result,
                hint: ReducibilityHint::Abbrev,
            };
            match self.kernel.add_declaration(declaration) {
                Ok(()) => {
                    result = self.kernel.const_(name, vec![]);
                }
                Err(error) => {
                    self.global_gate_prop_alias_error
                        .get_or_insert_with(|| format!("definition admission failed: {error:?}"));
                }
            }
        }
        self.gate_memo.insert(key, result);
        result
    }

    fn gate_term_to_prop_inner(&mut self, term: &AletheTerm) -> ExprId {
        if let Some(bridge) = &self.bridge
            && let Some(b_form) = bridge.get(&term.key())
        {
            let b_form = b_form.clone();
            return self.gate_term_to_prop(&b_form);
        }
        match term {
            AletheTerm::Const(symbol) if self.gate_bound_bools.contains_key(symbol) => {
                let value = self.gate_bound_bools[symbol];
                self.typed_bool_value_prop(value)
            }
            AletheTerm::App(head, args) if head == "not" && args.len() == 1 => {
                let inner = self.gate_term_to_prop(&args[0]);
                self.mk_not(inner)
            }
            AletheTerm::App(head, args) if head == "and" && !args.is_empty() => {
                self.fold_right(args, ReconstructCtx::mk_and)
            }
            AletheTerm::App(head, args) if head == "or" && !args.is_empty() => {
                self.fold_right(args, ReconstructCtx::mk_or)
            }
            AletheTerm::App(head, args) if head == "=" && args.len() == 2 => {
                let a = self.gate_term_to_prop(&args[0]);
                let b = self.gate_term_to_prop(&args[1]);
                self.mk_iff(a, b)
            }
            AletheTerm::App(head, args) if head == "xor" && args.len() == 2 => {
                let a = self.gate_term_to_prop(&args[0]);
                let b = self.gate_term_to_prop(&args[1]);
                let iff = self.mk_iff(a, b);
                self.mk_not(iff)
            }
            // The Boolean literals map to the prelude `True`/`False` (agreeing with
            // `gadget_bit_to_prop`), so a constant operand's bit — `true`/`false` from
            // `operand_bit_term` — renders identically whether it reaches here
            // directly or embedded in a gate.
            AletheTerm::Const(s) if s == "true" => self.kernel.const_(self.prelude.true_, vec![]),
            AletheTerm::Const(s) if s == "false" => self.kernel.const_(self.prelude.false_, vec![]),
            AletheTerm::Indexed { op, indices, args }
                if self.typed_bv_gates
                    && op == "@bit_of"
                    && indices.len() == 1
                    && args.len() == 1 =>
            {
                if let Ok(index) = usize::try_from(indices[0])
                    && let Some(prop) = self.typed_bv_projection(&args[0], index)
                {
                    return prop;
                }
                let name = self.prop_atom_const(&term.key());
                self.kernel.const_(name, vec![])
            }
            // A bit projection `((_ @bit_of i) operand)`. When `operand` is a COMPOUND
            // bit-vector term (the projection-based emission's gadget bits, e.g.
            // `((_ @bit_of i) (bvor a b))`), resolve it through the faithful bit model
            // `bv_bit` so it agrees structurally with the LHS expansion — this is the
            // reconstruction half of Carcara's projection (`build_term_vec`) scheme. A
            // bare-symbol / `#b…`-literal operand keeps the opaque/`True`/`False` leaf
            // (matching `bv_bit`'s own leaf handling), so the two sides still coincide.
            AletheTerm::Indexed { op, indices, args }
                if op == "@bit_of"
                    && indices.len() == 1
                    && args.len() == 1
                    && bit_of_operand_resolves(&args[0]) =>
            {
                if let Ok(i) = usize::try_from(indices[0]) {
                    // Reuse the `bv_bit` faithful model — for a compound operand it
                    // expands structurally; for a `#b…` literal operand it yields the
                    // constant `True`/`False` bit. (The emitter's `build_term_vec`
                    // projects `((_ @bit_of i) #b…)` for a constant concat operand.)
                    // Any failure (out-of-range bit, unsupported op) falls through to
                    // the opaque atom below.
                    if let Ok(prop) = bv_bit(self, &args[0], i) {
                        return prop;
                    }
                }
                let name = self.prop_atom_const(&term.key());
                self.kernel.const_(name, vec![])
            }
            // A bare symbol or any opaque compound: an uninterpreted Prop atom.
            other => {
                let name = self.prop_atom_const(&other.key());
                self.kernel.const_(name, vec![])
            }
        }
    }

    /// Right-fold a non-empty operand slice with a binary connective builder:
    /// `[t0, t1, …, tn]` ⇒ `op(⟦t0⟧, op(⟦t1⟧, … ⟦tn⟧))`.
    fn fold_right(
        &mut self,
        args: &[AletheTerm],
        op: fn(&mut ReconstructCtx, ExprId, ExprId) -> ExprId,
    ) -> ExprId {
        let (last, rest) = args
            .split_last()
            .expect("fold_right requires a non-empty operand slice");
        let mut acc = self.gate_term_to_prop(last);
        for t in rest.iter().rev() {
            let head = self.gate_term_to_prop(t);
            acc = op(self, head, acc);
        }
        acc
    }

    /// Translate a gate **literal** into its Lean `Prop`: a positive literal `t`
    /// ⇒ `⟦t⟧`; a negated `(not t)` ⇒ `Not ⟦t⟧`.
    fn gate_lit_to_prop(&mut self, lit: &AletheLit) -> ExprId {
        let atom = self.gate_term_to_prop(&lit.atom);
        if lit.negated { self.mk_not(atom) } else { atom }
    }

    /// Translate a whole gate **clause** into its right-nested `Or` encoding —
    /// the same shape as `clause_to_prop`, but with gate literals translated
    /// structurally (`gate_lit_to_prop`) rather than opaquely. The empty clause ⇒
    /// `False`; a unit clause ⇒ its single literal's Prop.
    pub(super) fn gate_clause_to_prop(&mut self, clause: &[AletheLit]) -> ExprId {
        let Some((last, rest)) = clause.split_last() else {
            return self.kernel.const_(self.prelude.false_, vec![]);
        };
        let mut acc = self.gate_lit_to_prop(last);
        for lit in rest.iter().rev() {
            let head = self.gate_lit_to_prop(lit);
            acc = self.mk_or(head, acc);
        }
        acc
    }
}

/// A truth assignment over operand atoms: each atom's s-expression key maps to
/// its structured `Prop` and a witness — either a proof of the Prop (`true`) or a
/// proof of its `Not` (`false`).
pub(super) struct Assignment {
    /// atom key → (its `Prop`, witness proof, whether the witness proves the Prop
    /// (`true`) or its negation (`false`)).
    map: BTreeMap<String, (ExprId, ExprId, bool)>,
}

impl Assignment {
    pub(super) fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }
}

/// The right-nested `And` `Prop` of `props` (non-empty), matching how
/// [`ReconstructCtx::gate_term_to_prop`] renders `(and φ…)` via `fold_right`.
pub(super) fn and_chain_prop_of(ctx: &mut ReconstructCtx, props: &[ExprId]) -> ExprId {
    let mut it = props.iter().rev().copied();
    let mut acc = it.next().expect("and has at least one operand");
    for p in it {
        acc = ctx.mk_and(p, acc);
    }
    acc
}

/// Project the `i`-th conjunct from `h : ⟦and φ_0 … φ_{k-1}⟧` (the right-nested
/// `And` of `props`), proving `props[i]`, via `i` `And.right` peels then (unless it
/// is the last operand) one `And.left`. `O(k)` — the polynomial replacement for
/// the `2^atoms` truth-table on `and_pos`. Reuses [`and_project`] (the `And.left`/
/// `And.right` primitive).
fn project_nth_conjunct(ctx: &mut ReconstructCtx, h: ExprId, props: &[ExprId], i: usize) -> ExprId {
    let mut cur = h;
    for j in 0..i {
        let a = props[j];
        let b = and_chain_prop_of(ctx, &props[j + 1..]);
        cur = and_project(ctx, a, b, cur, false); // take the right component
    }
    if i == props.len() - 1 {
        cur // the last operand is the innermost right component — no further proj
    } else {
        let a = props[i];
        let b = and_chain_prop_of(ctx, &props[i + 1..]);
        and_project(ctx, a, b, cur, true) // take the left component
    }
}

/// Rule-specific `O(k)` reconstruction of `and_pos`: `(cl (not (and φ…)) φ_i)`.
/// `em ⟦and φ…⟧`; on the positive branch project `⟦φ_i⟧` out of the conjunction and
/// `Or.inr`, on the negative branch `Or.inl`. Returns `Ok(None)` if the clause is
/// not this shape (caller falls back to the truth-table). The result is
/// `check_against`-gated, so a wrong term is rejected, never accepted.
fn try_and_pos(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
) -> Result<Option<ExprId>, ReconstructError> {
    let [l0, l1] = conclusion else {
        return Ok(None);
    };
    if !l0.negated || l1.negated {
        return Ok(None);
    }
    let AletheTerm::App(head, operands) = &l0.atom else {
        return Ok(None);
    };
    if head != "and" || operands.is_empty() {
        return Ok(None);
    }
    let phi_key = l1.atom.key();
    let Some(i) = operands.iter().position(|op| op.key() == phi_key) else {
        return Ok(None);
    };

    let _ = ctx.em_axiom();
    let operands = operands.clone();
    let operand_props: Vec<ExprId> = operands
        .iter()
        .map(|op| ctx.gate_term_to_prop(op))
        .collect();
    let g_prop = and_chain_prop_of(ctx, &operand_props);
    let phi_prop = operand_props[i];
    let not_g = ctx.mk_not(g_prop);
    let target = ctx.mk_or(not_g, phi_prop);

    let anon = ctx.kernel.anon();

    // minor_inl := fun (hG : ⟦G⟧) => Or.inr not_g phi_prop (project_i hG).
    let fvar_g = fresh_fvar_id(ctx);
    let hg = ctx.kernel.fvar(fvar_g);
    let proj = project_nth_conjunct(ctx, hg, &operand_props, i);
    let inl_body = or_inr(ctx, not_g, phi_prop, proj);
    let inl_body = ctx.kernel.abstract_fvars(inl_body, &[fvar_g]);
    let minor_inl = ctx.kernel.lam(anon, g_prop, inl_body, BinderInfo::Default);

    // minor_inr := fun (hnG : Not ⟦G⟧) => Or.inl not_g phi_prop hnG.
    let fvar_ng = fresh_fvar_id(ctx);
    let hng = ctx.kernel.fvar(fvar_ng);
    let inr_body = or_inl(ctx, not_g, phi_prop, hng);
    let inr_body = ctx.kernel.abstract_fvars(inr_body, &[fvar_ng]);
    let minor_inr = ctx.kernel.lam(anon, not_g, inr_body, BinderInfo::Default);

    // Or.rec ⟦G⟧ (Not ⟦G⟧) (fun _ => target) minor_inl minor_inr (em ⟦G⟧).
    let or_g = ctx.mk_or(g_prop, not_g);
    let motive = ctx.kernel.lam(anon, or_g, target, BinderInfo::Default);
    let em_name = ctx.em_axiom();
    let em = ctx.kernel.const_(em_name, vec![]);
    let em_g = ctx.kernel.app(em, g_prop);
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![]);
    let e = ctx.kernel.app(rec, g_prop);
    let e = ctx.kernel.app(e, not_g);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor_inl);
    let e = ctx.kernel.app(e, minor_inr);
    let proof = ctx.kernel.app(e, em_g);

    Ok(Some(check_against(ctx, "and_pos", proof, target)?))
}

/// Right-nested `And.intro` of `witnesses` (proofs of `props[i]`) into a proof of
/// `⟦and props⟧` — the inverse of [`project_nth_conjunct`].
pub(super) fn and_intro_fold(
    ctx: &mut ReconstructCtx,
    props: &[ExprId],
    witnesses: &[ExprId],
) -> ExprId {
    let n = props.len();
    let mut acc = witnesses[n - 1];
    for i in (0..n - 1).rev() {
        let a = props[i];
        let b = and_chain_prop_of(ctx, &props[i + 1..]);
        acc = and_intro(ctx, a, b, witnesses[i], acc);
    }
    acc
}

/// Recursive core of [`try_and_neg`]: case-split `em ⟦φ_j⟧` for each operand; on
/// the first false operand inject its negated literal, and when all hold build
/// `⟦and φ…⟧` by [`and_intro_fold`] and inject it at position 0. `target` is the
/// fixed clause `Prop`; `witnesses` accumulates the positive-operand fvars.
fn build_and_neg(
    ctx: &mut ReconstructCtx,
    clause: &[AletheLit],
    props: &[ExprId],
    j: usize,
    target: ExprId,
    witnesses: &mut Vec<ExprId>,
) -> ExprId {
    if j == props.len() {
        let g = and_intro_fold(ctx, props, witnesses);
        return inject_gate_lit(ctx, clause, 0, g);
    }
    let anon = ctx.kernel.anon();
    let p = props[j];
    let not_p = ctx.mk_not(p);

    // inl: φ_j holds — record the witness and recurse.
    let fv = fresh_fvar_id(ctx);
    let h = ctx.kernel.fvar(fv);
    witnesses.push(h);
    let body_inl = build_and_neg(ctx, clause, props, j + 1, target, witnesses);
    witnesses.pop();
    let body_inl = ctx.kernel.abstract_fvars(body_inl, &[fv]);
    let minor_inl = ctx.kernel.lam(anon, p, body_inl, BinderInfo::Default);

    // inr: ¬φ_j — inject the negated operand at clause position j+1.
    let fv2 = fresh_fvar_id(ctx);
    let hn = ctx.kernel.fvar(fv2);
    let inj = inject_gate_lit(ctx, clause, j + 1, hn);
    let body_inr = ctx.kernel.abstract_fvars(inj, &[fv2]);
    let minor_inr = ctx.kernel.lam(anon, not_p, body_inr, BinderInfo::Default);

    let or_p_notp = ctx.mk_or(p, not_p);
    let motive = ctx.kernel.lam(anon, or_p_notp, target, BinderInfo::Default);
    let em_name = ctx.em_axiom();
    let em = ctx.kernel.const_(em_name, vec![]);
    let em_p = ctx.kernel.app(em, p);
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![]);
    let e = ctx.kernel.app(rec, p);
    let e = ctx.kernel.app(e, not_p);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor_inl);
    let e = ctx.kernel.app(e, minor_inr);
    ctx.kernel.app(e, em_p)
}

/// Rule-specific `O(k)` reconstruction of `and_neg`:
/// `(cl (and φ…) (not φ_0) … (not φ_{k-1}))`. Nested `em` over the operands; the
/// first false operand discharges its negated literal, all-true builds the
/// conjunction. Returns `Ok(None)` for an unexpected shape (caller falls back).
fn try_and_neg(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
) -> Result<Option<ExprId>, ReconstructError> {
    let Some((l0, rest)) = conclusion.split_first() else {
        return Ok(None);
    };
    if l0.negated {
        return Ok(None);
    }
    let AletheTerm::App(head, operands) = &l0.atom else {
        return Ok(None);
    };
    if head != "and" || operands.len() != rest.len() || operands.is_empty() {
        return Ok(None);
    }
    // Each tail literal must be `¬φ_j` for the j-th operand (peel a `(not …)` atom
    // or a `negated` flag; either spelling denotes `Not ⟦φ_j⟧`).
    for (op, lit) in operands.iter().zip(rest) {
        let neg = normalize_lit_polarity(lit);
        if !neg.negated || neg.atom.key() != op.key() {
            return Ok(None);
        }
    }

    let _ = ctx.em_axiom();
    let operands = operands.clone();
    let conclusion = conclusion.to_vec();
    let props: Vec<ExprId> = operands
        .iter()
        .map(|op| ctx.gate_term_to_prop(op))
        .collect();
    let target = ctx.gate_clause_to_prop(&conclusion);
    let mut witnesses: Vec<ExprId> = Vec::new();
    let proof = build_and_neg(ctx, &conclusion, &props, 0, target, &mut witnesses);
    Ok(Some(check_against(ctx, "and_neg", proof, target)?))
}

/// Rule-specific `O(1)` reconstruction of `or_pos`: `(cl (not (or φ…)) φ_0 … φ_{k-1})`.
/// The clause tail `φ_0 ∨ … ∨ φ_{k-1}` is *exactly* `⟦or φ…⟧`, so no projection is
/// needed: `em ⟦G⟧`; on the positive branch the witness already proves the tail
/// (`Or.inr`), on the negative branch `Or.inl`. Returns `Ok(None)` for an
/// unexpected shape (caller falls back).
fn try_or_pos(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
) -> Result<Option<ExprId>, ReconstructError> {
    let Some((l0, tail)) = conclusion.split_first() else {
        return Ok(None);
    };
    if !l0.negated || tail.is_empty() {
        return Ok(None);
    }
    let AletheTerm::App(head, operands) = &l0.atom else {
        return Ok(None);
    };
    if head != "or" || operands.len() != tail.len() {
        return Ok(None);
    }
    // The tail must be the operands as positive literals, in order.
    for (op, lit) in operands.iter().zip(tail) {
        if lit.negated || lit.atom.key() != op.key() {
            return Ok(None);
        }
    }

    let _ = ctx.em_axiom();
    let conclusion = conclusion.to_vec();
    let tail_prop = ctx.gate_clause_to_prop(&conclusion[1..]); // ⟦G⟧ (= the or-chain)
    let not_g = ctx.mk_not(tail_prop);
    let target = ctx.gate_clause_to_prop(&conclusion); // Or(not_g, tail_prop)

    let anon = ctx.kernel.anon();
    // minor_inl := fun (hG : tail_prop) => Or.inr not_g tail_prop hG.
    let fv = fresh_fvar_id(ctx);
    let hg = ctx.kernel.fvar(fv);
    let inl_body = or_inr(ctx, not_g, tail_prop, hg);
    let inl_body = ctx.kernel.abstract_fvars(inl_body, &[fv]);
    let minor_inl = ctx
        .kernel
        .lam(anon, tail_prop, inl_body, BinderInfo::Default);
    // minor_inr := fun (hnG : Not tail_prop) => Or.inl not_g tail_prop hnG.
    let fv2 = fresh_fvar_id(ctx);
    let hng = ctx.kernel.fvar(fv2);
    let inr_body = or_inl(ctx, not_g, tail_prop, hng);
    let inr_body = ctx.kernel.abstract_fvars(inr_body, &[fv2]);
    let minor_inr = ctx.kernel.lam(anon, not_g, inr_body, BinderInfo::Default);

    let or_g = ctx.mk_or(tail_prop, not_g);
    let motive = ctx.kernel.lam(anon, or_g, target, BinderInfo::Default);
    let em_name = ctx.em_axiom();
    let em = ctx.kernel.const_(em_name, vec![]);
    let em_g = ctx.kernel.app(em, tail_prop);
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![]);
    let e = ctx.kernel.app(rec, tail_prop);
    let e = ctx.kernel.app(e, not_g);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor_inl);
    let e = ctx.kernel.app(e, minor_inr);
    let proof = ctx.kernel.app(e, em_g);

    Ok(Some(check_against(ctx, "or_pos", proof, target)?))
}

/// Rule-specific `O(k)` reconstruction of `or_neg`: `(cl (or φ…) (not φ_i))`.
/// `em ⟦φ_i⟧`; on the positive branch inject the witness into the or-chain `⟦G⟧`
/// at position `i` (`inject_gate_lit` over the operands-as-clause) and `Or.inl`, on
/// the negative branch `Or.inr`. Returns `Ok(None)` for an unexpected shape.
fn try_or_neg(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
) -> Result<Option<ExprId>, ReconstructError> {
    let [l0, l1] = conclusion else {
        return Ok(None);
    };
    if l0.negated {
        return Ok(None);
    }
    let neg = normalize_lit_polarity(l1);
    if !neg.negated {
        return Ok(None);
    }
    let AletheTerm::App(head, operands) = &l0.atom else {
        return Ok(None);
    };
    if head != "or" || operands.is_empty() {
        return Ok(None);
    }
    let Some(i) = operands.iter().position(|op| op.key() == neg.atom.key()) else {
        return Ok(None);
    };

    let _ = ctx.em_axiom();
    let operands = operands.clone();
    let conclusion = conclusion.to_vec();
    // The operands as a positive clause: its encoding is `⟦G⟧` (the or-chain).
    let operand_clause: Vec<AletheLit> = operands
        .iter()
        .map(|op| AletheLit {
            atom: op.clone(),
            negated: false,
        })
        .collect();
    let g_prop = ctx.gate_clause_to_prop(&operand_clause);
    let phi_prop = ctx.gate_term_to_prop(&operands[i]);
    let not_phi = ctx.mk_not(phi_prop);
    let target = ctx.gate_clause_to_prop(&conclusion); // Or(⟦G⟧, Not ⟦φ_i⟧)

    let anon = ctx.kernel.anon();
    // minor_inl := fun (h : ⟦φ_i⟧) => Or.inl ⟦G⟧ not_phi (inject_i h).
    let fv = fresh_fvar_id(ctx);
    let h = ctx.kernel.fvar(fv);
    let g_proof = inject_gate_lit(ctx, &operand_clause, i, h);
    let inl_body = or_inl(ctx, g_prop, not_phi, g_proof);
    let inl_body = ctx.kernel.abstract_fvars(inl_body, &[fv]);
    let minor_inl = ctx
        .kernel
        .lam(anon, phi_prop, inl_body, BinderInfo::Default);
    // minor_inr := fun (hn : Not ⟦φ_i⟧) => Or.inr ⟦G⟧ not_phi hn.
    let fv2 = fresh_fvar_id(ctx);
    let hn = ctx.kernel.fvar(fv2);
    let inr_body = or_inr(ctx, g_prop, not_phi, hn);
    let inr_body = ctx.kernel.abstract_fvars(inr_body, &[fv2]);
    let minor_inr = ctx.kernel.lam(anon, not_phi, inr_body, BinderInfo::Default);

    let or_phi = ctx.mk_or(phi_prop, not_phi);
    let motive = ctx.kernel.lam(anon, or_phi, target, BinderInfo::Default);
    let em_name = ctx.em_axiom();
    let em = ctx.kernel.const_(em_name, vec![]);
    let em_phi = ctx.kernel.app(em, phi_prop);
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![]);
    let e = ctx.kernel.app(rec, phi_prop);
    let e = ctx.kernel.app(e, not_phi);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor_inl);
    let e = ctx.kernel.app(e, minor_inr);
    let proof = ctx.kernel.app(e, em_phi);

    Ok(Some(check_against(ctx, "or_neg", proof, target)?))
}

/// Rule-specific `O(1)` reconstruction of the `equiv_*` / `xor_*` rules, whose gate
/// `(= a b)` (or `(xor a b) = Not Iff`) has exactly **two** operands `a, b`. Instead
/// of the `2^leaves` truth-table over the operands' bit leaves, case-split only over
/// `{a, b}` (the four `em ⟦a⟧ × em ⟦b⟧` cases) via the shared `prove_clause_by_cases`
/// engine — `prove_term_true/false` now treats `a, b` as opaque atoms. Polynomial
/// regardless of how large the operand gates are. Returns `Ok(None)` if no `=`/`xor`
/// gate literal is present (caller falls back).
fn try_equiv_xor(
    ctx: &mut ReconstructCtx,
    rule_name: &str,
    conclusion: &[AletheLit],
) -> Result<Option<ExprId>, ReconstructError> {
    let mut operands: Option<(AletheTerm, AletheTerm)> = None;
    for lit in conclusion {
        if let AletheTerm::App(head, args) = &lit.atom
            && (head == "=" || head == "xor")
            && args.len() == 2
        {
            operands = Some((args[0].clone(), args[1].clone()));
            break;
        }
    }
    let Some((a, b)) = operands else {
        return Ok(None);
    };

    let _ = ctx.em_axiom();
    // Case-split atoms: the two operands, deduplicated by key. A **constant-valued**
    // operand (one with no free atoms, e.g. `false` or `(not false)` — common in
    // bit-blasted adders over constant operands) is NOT case-split: it is a fixed
    // truth value, so `prove_term` evaluates it at the leaf. Case-splitting it would
    // explore impossible worlds and falsely reject a valid clause.
    let mut atoms: Vec<(String, AletheTerm)> = Vec::new();
    for op in [a, b] {
        let mut leaves = Vec::new();
        collect_atoms(&op, &mut leaves);
        if leaves.is_empty() {
            continue; // constant-valued operand
        }
        let key = op.key();
        if !atoms.iter().any(|(k, _)| k == &key) {
            atoms.push((key, op));
        }
    }
    let target = ctx.gate_clause_to_prop(conclusion);
    let conclusion = conclusion.to_vec();
    let mut assignment = Assignment::new();
    let proof = prove_clause_by_cases(ctx, &atoms, 0, &mut assignment, &conclusion, target)?;
    Ok(Some(check_against(ctx, rule_name, proof, target)?))
}

/// Reconstruct a Tseitin **CNF-introduction** rule into a kernel-checked Lean
/// proof term of its conclusion clause's `Prop` encoding.
///
/// `rule_name` is the Alethe rule (`and_pos`/`and_neg`/`or_pos`/`or_neg`,
/// `equiv_pos1`/`equiv_pos2`/`equiv_neg1`/`equiv_neg2`,
/// `xor_pos1`/`xor_pos2`/`xor_neg1`/`xor_neg2`); `conclusion` is the rule's
/// conclusion clause. Each such clause is a propositional **tautology** over the
/// structured gate (`And`/`Or`/`Iff`/`Not`, with `xor` modeled as `Not Iff`) of
/// its operand atoms. The returned proof term is `infer`-checked and
/// [`axeyum_lean_kernel::Kernel::def_eq`]-compared to the clause's
/// `gate_clause_to_prop`
/// encoding — the kernel is the gate.
///
/// Rules with a direct polynomial proof (`and_pos`) are handled rule-specifically;
/// the rest fall back to a classical case-split (via the context's `em`) over every
/// distinct operand atom, injecting the satisfied literal into the conclusion's
/// `Or` encoding in each leaf. A wrong conclusion makes the satisfied-literal
/// search fail or the kernel reject — never a wrong "checked".
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedRule`] for a rule outside the
/// CNF-introduction set, [`ReconstructError::MalformedStep`] for a clause that is
/// not a tautology under the gate model (some truth assignment satisfies no
/// literal), and [`ReconstructError::KernelRejected`] when the kernel's `infer`
/// fails or the inferred proposition is not `def_eq` to the conclusion. It never
/// panics on malformed or out-of-scope input.
pub fn reconstruct_cnf_intro_rule(
    ctx: &mut ReconstructCtx,
    rule_name: &str,
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    match rule_name {
        "and_pos" | "and_neg" | "or_pos" | "or_neg" | "equiv_pos1" | "equiv_pos2"
        | "equiv_neg1" | "equiv_neg2" | "xor_pos1" | "xor_pos2" | "xor_neg1" | "xor_neg2" => {}
        other => {
            return Err(ReconstructError::UnsupportedRule {
                rule: other.to_owned(),
            });
        }
    }

    // Rule-specific polynomial proofs (replacing the `2^atoms` truth-table) where
    // available; fall back to `prove_clause_by_cases` for the rest.
    if rule_name == "and_pos"
        && let Some(proof) = try_and_pos(ctx, conclusion)?
    {
        return Ok(proof);
    }
    if rule_name == "and_neg"
        && let Some(proof) = try_and_neg(ctx, conclusion)?
    {
        return Ok(proof);
    }
    if rule_name == "or_pos"
        && let Some(proof) = try_or_pos(ctx, conclusion)?
    {
        return Ok(proof);
    }
    if rule_name == "or_neg"
        && let Some(proof) = try_or_neg(ctx, conclusion)?
    {
        return Ok(proof);
    }
    if matches!(
        rule_name,
        "equiv_pos1"
            | "equiv_pos2"
            | "equiv_neg1"
            | "equiv_neg2"
            | "xor_pos1"
            | "xor_pos2"
            | "xor_neg1"
            | "xor_neg2"
    ) && let Some(proof) = try_equiv_xor(ctx, rule_name, conclusion)?
    {
        return Ok(proof);
    }

    // Ensure `em` is available for the classical case-split.
    let _ = ctx.em_axiom();

    // Private source-instance tails carry short gate names with exact definitions
    // in `bridge`. Expand them before proving the clause tautology; the original
    // target reaches the same propositions through `gate_term_to_prop`.
    let expanded = conclusion
        .iter()
        .enumerate()
        .map(|(index, literal)| AletheLit {
            // Every CNF-introduction rule places its defined gate first. Expand
            // that gate one level, while retaining operand names so the clause
            // is the expected `op(args) ∨ ...args...` tautology.
            atom: if index == 0 {
                ctx.bridge_substitute(&literal.atom)
            } else {
                literal.atom.clone()
            },
            negated: literal.negated,
        })
        .collect::<Vec<_>>();

    // Collect the distinct operand atoms (the case-split variables) in a stable
    // order (s-expression key order via the BTreeSet-like collection below).
    let mut atom_keys: Vec<(String, AletheTerm)> = Vec::new();
    for lit in &expanded {
        collect_atoms(&lit.atom, &mut atom_keys);
    }

    let target = ctx.gate_clause_to_prop(conclusion);

    // Recursively case-split on each atom; at the leaf, inject the satisfied lit.
    let mut assignment = Assignment::new();
    let proof = prove_clause_by_cases(ctx, &atom_keys, 0, &mut assignment, &expanded, target)?;

    check_against(ctx, rule_name, proof, target)
}

/// Collect the distinct **operand atoms** of a gate term — the leaves that are
/// not Boolean connectives — keyed by s-expression, in first-seen order.
fn collect_atoms(term: &AletheTerm, out: &mut Vec<(String, AletheTerm)>) {
    match term {
        AletheTerm::App(head, args)
            if (head == "not" && args.len() == 1)
                || ((head == "and" || head == "or") && !args.is_empty())
                || ((head == "=" || head == "xor") && args.len() == 2) =>
        {
            for a in args {
                collect_atoms(a, out);
            }
        }
        // The Boolean literals are FIXED values, not free atoms — never case-split
        // them (doing so explores impossible worlds, e.g. `(not false) = false`, and
        // a real tautology then looks falsified). `prove_term_true/false` evaluate
        // them directly.
        AletheTerm::Const(s) if s == "true" || s == "false" => {}
        other => {
            let key = other.key();
            if !out.iter().any(|(k, _)| k == &key) {
                out.push((key, other.clone()));
            }
        }
    }
}

/// Case-split on `atoms[idx..]` via `em`, accumulating each atom's truth witness
/// in `assignment`; at the leaf (`idx == atoms.len()`) build the satisfied
/// literal's proof and inject it into the clause's `Or` encoding `target`.
pub(super) fn prove_clause_by_cases(
    ctx: &mut ReconstructCtx,
    atoms: &[(String, AletheTerm)],
    idx: usize,
    assignment: &mut Assignment,
    conclusion: &[AletheLit],
    target: ExprId,
) -> Result<ExprId, ReconstructError> {
    if idx == atoms.len() {
        return prove_clause_leaf(ctx, conclusion, target, assignment);
    }

    let (key, atom_term) = atoms[idx].clone();
    let p = ctx.gate_term_to_prop(&atom_term);

    // `em p : Or p (Not p)`. Case-split with `Or.rec` into `target`.
    let em_name = ctx.em_axiom();
    let em = ctx.kernel.const_(em_name, vec![]);
    let em_p = ctx.kernel.app(em, p);

    let not_p = ctx.mk_not(p);
    let anon = ctx.kernel.anon();

    // minor_inl := fun (hp : p) => <recurse with key ↦ true>.
    let fvar_true = fresh_fvar_id(ctx);
    let hp = ctx.kernel.fvar(fvar_true);
    assignment.map.insert(key.clone(), (p, hp, true));
    let body_true = prove_clause_by_cases(ctx, atoms, idx + 1, assignment, conclusion, target)?;
    assignment.map.remove(&key);
    let body_true = ctx.kernel.abstract_fvars(body_true, &[fvar_true]);
    let minor_inl = ctx.kernel.lam(anon, p, body_true, BinderInfo::Default);

    // minor_inr := fun (hnp : Not p) => <recurse with key ↦ false>.
    let fvar_false = fresh_fvar_id(ctx);
    let hnp = ctx.kernel.fvar(fvar_false);
    assignment.map.insert(key.clone(), (p, hnp, false));
    let body_false = prove_clause_by_cases(ctx, atoms, idx + 1, assignment, conclusion, target)?;
    assignment.map.remove(&key);
    let body_false = ctx.kernel.abstract_fvars(body_false, &[fvar_false]);
    let minor_inr = ctx.kernel.lam(anon, not_p, body_false, BinderInfo::Default);

    // motive := fun (_ : Or p (Not p)) => target.
    let or_p_notp = ctx.mk_or(p, not_p);
    let motive = ctx.kernel.lam(anon, or_p_notp, target, BinderInfo::Default);

    // Or.rec p (Not p) motive minor_inl minor_inr (em p) : target.
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![]);
    let e = ctx.kernel.app(rec, p);
    let e = ctx.kernel.app(e, not_p);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor_inl);
    let e = ctx.kernel.app(e, minor_inr);
    Ok(ctx.kernel.app(e, em_p))
}

/// At a complete truth assignment, find a satisfied clause literal and inject its
/// proof into the right-nested `Or` encoding `target = gate_clause_to_prop(conclusion)`.
fn prove_clause_leaf(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
    target: ExprId,
    assignment: &Assignment,
) -> Result<ExprId, ReconstructError> {
    let _ = target;
    // Find the first literal satisfied under the assignment, with its proof.
    for (idx, lit) in conclusion.iter().enumerate() {
        if let Some(lit_proof) = prove_lit(ctx, lit, assignment)? {
            return Ok(inject_gate_lit(ctx, conclusion, idx, lit_proof));
        }
    }
    // No literal holds in this assignment ⇒ the clause is NOT a tautology.
    let clause_keys: Vec<String> = conclusion
        .iter()
        .map(|l| {
            let neg = if l.negated { "¬" } else { "" };
            format!("{neg}{}", l.atom.key())
        })
        .collect();
    let assign_keys: Vec<String> = assignment
        .map
        .iter()
        .map(|(k, &(_, _, v))| format!("{k}={v}"))
        .collect();
    Err(ReconstructError::MalformedStep {
        rule: "cnf_intro".to_owned(),
        detail: format!(
            "conclusion clause is not a tautology under the gate model; \
             clause = [{}] falsified by {{{}}}",
            clause_keys.join(", "),
            assign_keys.join(", ")
        ),
    })
}

/// Inject a proof `lit_proof : gate_lit_to_prop(conclusion[idx])` into the
/// right-nested `Or` encoding `target` at position `idx` via `Or.inl`/`Or.inr`.
fn inject_gate_lit(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
    idx: usize,
    lit_proof: ExprId,
) -> ExprId {
    let n = conclusion.len();
    debug_assert!(idx < n);
    let mut proof = lit_proof;
    for i in (0..=idx).rev() {
        if i == idx {
            if idx == n - 1 {
                // Last literal: the suffix is just `Enc(lit)`; nothing to wrap.
            } else {
                let a = ctx.gate_lit_to_prop(&conclusion[idx]);
                let b = ctx.gate_clause_to_prop(&conclusion[idx + 1..]);
                proof = or_inl(ctx, a, b, proof);
            }
        } else {
            let a = ctx.gate_lit_to_prop(&conclusion[i]);
            let b = ctx.gate_clause_to_prop(&conclusion[i + 1..]);
            proof = or_inr(ctx, a, b, proof);
        }
    }
    proof
}

/// Build a proof of a gate **literal** under the assignment, or `None` if the
/// literal is not satisfied. A positive literal `t` needs `⟦t⟧` (so `t` evaluates
/// true); a negated `(not t)` needs `Not ⟦t⟧` (so `t` evaluates false).
fn prove_lit(
    ctx: &mut ReconstructCtx,
    lit: &AletheLit,
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    if lit.negated {
        prove_term_false(ctx, &lit.atom, assignment)
    } else {
        prove_term_true(ctx, &lit.atom, assignment)
    }
}

/// Build a proof of `⟦term⟧` (the structured gate Prop) under the assignment, or
/// `None` if `term` evaluates to false there. Recurses structurally over the
/// gate; atoms are looked up in the assignment.
#[allow(clippy::too_many_lines)]
fn prove_term_true(
    ctx: &mut ReconstructCtx,
    term: &AletheTerm,
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    // If `term` itself is a case-split atom, use its witness directly rather than
    // recursing into its gate structure. For the leaf-atom truth-table this never
    // fires on a compound term (only leaves are atoms); it lets a coarser case-split
    // (e.g. over a predicate's two operands) treat those operands as opaque.
    if let Some(&(_, proof, val)) = assignment.map.get(&term.key()) {
        return Ok(val.then_some(proof));
    }
    // The Boolean literals: `true` is provable (`True.intro`), `false` is not.
    if let AletheTerm::Const(s) = term {
        if s == "true" {
            return Ok(Some(ctx.kernel.const_(ctx.prelude.true_intro, vec![])));
        }
        if s == "false" {
            return Ok(None);
        }
    }
    match term {
        // (not t) is true ⇔ t is false ⇒ a `Not ⟦t⟧` proof.
        AletheTerm::App(head, args) if head == "not" && args.len() == 1 => {
            prove_term_false(ctx, &args[0], assignment)
        }
        // (and t…) is true ⇔ every operand is true; fold `And.intro` right-nested.
        AletheTerm::App(head, args) if head == "and" && !args.is_empty() => {
            // Build the proof from the last operand inward. At each step `acc`
            // proves the And of the operands *after* index `i`; `And.intro` of the
            // operand at `i` extends it leftward.
            let n = args.len();
            let Some(mut acc) = prove_term_true(ctx, &args[n - 1], assignment)? else {
                return Ok(None);
            };
            for i in (0..n - 1).rev() {
                let Some(ht) = prove_term_true(ctx, &args[i], assignment)? else {
                    return Ok(None);
                };
                // acc : ⟦args[i+1..]⟧ ; ht : ⟦args[i]⟧ ⇒ And.intro a b ht acc.
                let a = ctx.gate_term_to_prop(&args[i]);
                let b = and_chain_prop(ctx, &args[i + 1..]);
                acc = and_intro(ctx, a, b, ht, acc);
            }
            Ok(Some(acc))
        }
        // (or t…) is true ⇔ some operand is true; inject with Or.inl/Or.inr.
        AletheTerm::App(head, args) if head == "or" && !args.is_empty() => {
            prove_or_true(ctx, args, assignment)
        }
        // (= a b) (boolean iff) is true ⇔ a, b have the SAME truth value.
        AletheTerm::App(head, args) if head == "=" && args.len() == 2 => {
            prove_iff_true(ctx, &args[0], &args[1], assignment)
        }
        // (xor a b) = Not (Iff a b) is true ⇔ a, b DIFFER ⇒ a `Not (Iff a b)` proof.
        AletheTerm::App(head, args) if head == "xor" && args.len() == 2 => {
            prove_iff_false(ctx, &args[0], &args[1], assignment)
        }
        // An atom: look it up.
        other => {
            let key = other.key();
            match assignment.map.get(&key) {
                Some(&(_, proof, true)) => Ok(Some(proof)),
                _ => Ok(None),
            }
        }
    }
}

/// Build a proof of `Not ⟦term⟧` under the assignment, or `None` if `term`
/// evaluates true there. Recurses structurally over the gate.
fn prove_term_false(
    ctx: &mut ReconstructCtx,
    term: &AletheTerm,
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    // Symmetric to `prove_term_true`: a case-split atom uses its `Not`-witness
    // directly (stored for the `false` branch) instead of recursing into the gate.
    if let Some(&(_, proof, val)) = assignment.map.get(&term.key()) {
        return Ok((!val).then_some(proof));
    }
    // The Boolean literals: `false` is refutable (`Not False` = `id : False → False`),
    // `true` is not.
    if let AletheTerm::Const(s) = term {
        if s == "false" {
            let false_ = ctx.kernel.const_(ctx.prelude.false_, vec![]);
            let anon = ctx.kernel.anon();
            let body = ctx.kernel.bvar(0);
            return Ok(Some(ctx.kernel.lam(
                anon,
                false_,
                body,
                BinderInfo::Default,
            )));
        }
        if s == "true" {
            return Ok(None);
        }
    }
    match term {
        // Not (not t) ⇔ t is true. We have a proof `ht : ⟦t⟧`; build a proof of
        // `Not (Not ⟦t⟧)` = `(⟦t⟧ → False) → False` as `fun hnt => hnt ht`.
        AletheTerm::App(head, args) if head == "not" && args.len() == 1 => {
            let Some(ht) = prove_term_true(ctx, &args[0], assignment)? else {
                return Ok(None);
            };
            let inner = ctx.gate_term_to_prop(&args[0]);
            let not_inner = ctx.mk_not(inner);
            // fun (hnt : Not ⟦t⟧) => hnt ht : Not (Not ⟦t⟧).
            let anon = ctx.kernel.anon();
            let fv = fresh_fvar_id(ctx);
            let hnt = ctx.kernel.fvar(fv);
            let body = ctx.kernel.app(hnt, ht);
            let body = ctx.kernel.abstract_fvars(body, &[fv]);
            Ok(Some(ctx.kernel.lam(
                anon,
                not_inner,
                body,
                BinderInfo::Default,
            )))
        }
        // Not (and t…) ⇔ some operand is false. With `hnf : Not ⟦tᵢ⟧`, build
        // `fun (h : ⟦and⟧) => hnf (project tᵢ from h)`.
        AletheTerm::App(head, args) if head == "and" && !args.is_empty() => {
            prove_and_false(ctx, args, assignment)
        }
        // Not (or t…) ⇔ every operand is false. With each `hnf_i : Not ⟦tᵢ⟧`,
        // build `fun (h : ⟦or⟧) => Or.rec … h` discharging each branch.
        AletheTerm::App(head, args) if head == "or" && !args.is_empty() => {
            prove_or_false(ctx, args, assignment)
        }
        // Not (= a b) ⇔ a, b differ.
        AletheTerm::App(head, args) if head == "=" && args.len() == 2 => {
            prove_iff_false(ctx, &args[0], &args[1], assignment)
        }
        // Not (xor a b) = Not (Not (Iff a b)) ⇔ a, b agree ⇒ `Not (Not (Iff))`.
        AletheTerm::App(head, args) if head == "xor" && args.len() == 2 => {
            let Some(iff_proof) = prove_iff_true(ctx, &args[0], &args[1], assignment)? else {
                return Ok(None);
            };
            let a = ctx.gate_term_to_prop(&args[0]);
            let b = ctx.gate_term_to_prop(&args[1]);
            let iff = ctx.mk_iff(a, b);
            let not_iff = ctx.mk_not(iff);
            // fun (hn : Not (Iff a b)) => hn iff_proof : Not (Not (Iff a b)).
            let anon = ctx.kernel.anon();
            let fv = fresh_fvar_id(ctx);
            let hn = ctx.kernel.fvar(fv);
            let body = ctx.kernel.app(hn, iff_proof);
            let body = ctx.kernel.abstract_fvars(body, &[fv]);
            Ok(Some(ctx.kernel.lam(
                anon,
                not_iff,
                body,
                BinderInfo::Default,
            )))
        }
        // An atom: look it up for a `Not`-witness.
        other => {
            let key = other.key();
            match assignment.map.get(&key) {
                Some(&(_, proof, false)) => Ok(Some(proof)),
                _ => Ok(None),
            }
        }
    }
}

/// `And.intro a b ha hb : And a b`.
pub(super) fn and_intro(
    ctx: &mut ReconstructCtx,
    a: ExprId,
    b: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let intro = ctx.kernel.const_(ctx.prelude.and_intro, vec![]);
    let e = ctx.kernel.app(intro, a);
    let e = ctx.kernel.app(e, b);
    let e = ctx.kernel.app(e, ha);
    ctx.kernel.app(e, hb)
}

/// `And.rec`-project: from `h : And a b` produce a proof of the projection at
/// `select` (`true` = left operand `a`, `false` = right operand `b`).
pub(super) fn and_project(
    ctx: &mut ReconstructCtx,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    select_left: bool,
) -> ExprId {
    let anon = ctx.kernel.anon();
    let target = if select_left { a } else { b };
    // motive := fun (_ : And a b) => target.
    let and_ab = ctx.mk_and(a, b);
    let motive = ctx.kernel.lam(anon, and_ab, target, BinderInfo::Default);
    // minor := fun (ha : a) (hb : b) => (ha | hb).
    //   Under binders ha, hb: ha = BVar 1, hb = BVar 0.
    let chosen = if select_left {
        ctx.kernel.bvar(1)
    } else {
        ctx.kernel.bvar(0)
    };
    let inner = ctx.kernel.lam(anon, b, chosen, BinderInfo::Default);
    let minor = ctx.kernel.lam(anon, a, inner, BinderInfo::Default);
    // And.rec.{0} a b motive minor h : target.
    let z = ctx.kernel.level_zero();
    let rec = ctx.kernel.const_(ctx.prelude.and_rec, vec![z]);
    let e = ctx.kernel.app(rec, a);
    let e = ctx.kernel.app(e, b);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor);
    ctx.kernel.app(e, h)
}

/// Build a proof of `Or ⟦t0⟧ (Or … ⟦tn⟧)` when some operand is true.
fn prove_or_true(
    ctx: &mut ReconstructCtx,
    args: &[AletheTerm],
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    // Find the first true operand and inject; the Or is right-nested.
    let n = args.len();
    for (idx, t) in args.iter().enumerate() {
        if let Some(t_proof) = prove_term_true(ctx, t, assignment)? {
            // Inject `t_proof` at position `idx` into the right-nested Or of `args`.
            let mut proof = t_proof;
            for i in (0..=idx).rev() {
                if i == idx {
                    if idx == n - 1 {
                        // last operand: the suffix is `⟦t⟧`; nothing to wrap.
                    } else {
                        let a = ctx.gate_term_to_prop(&args[idx]);
                        let b = or_chain_prop(ctx, &args[idx + 1..]);
                        proof = or_inl(ctx, a, b, proof);
                    }
                } else {
                    let a = ctx.gate_term_to_prop(&args[i]);
                    let b = or_chain_prop(ctx, &args[i + 1..]);
                    proof = or_inr(ctx, a, b, proof);
                }
            }
            return Ok(Some(proof));
        }
    }
    Ok(None)
}

/// The `Prop` of the right-nested `Or` chain of a non-empty operand slice.
fn or_chain_prop(ctx: &mut ReconstructCtx, args: &[AletheTerm]) -> ExprId {
    let (last, rest) = args.split_last().expect("non-empty Or chain");
    let mut acc = ctx.gate_term_to_prop(last);
    for t in rest.iter().rev() {
        let head = ctx.gate_term_to_prop(t);
        acc = ctx.mk_or(head, acc);
    }
    acc
}

/// Build a proof of `Not (Or ⟦t0⟧ …)` when every operand is false. We have
/// `hnf_i : Not ⟦tᵢ⟧` for each; `fun (h : Or …) => Or.rec … h` discharges each
/// branch into `False` by applying the matching `hnf`.
fn prove_or_false(
    ctx: &mut ReconstructCtx,
    args: &[AletheTerm],
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    // Collect a `Not ⟦tᵢ⟧` proof for every operand; bail if any is true.
    let mut neg_proofs: Vec<ExprId> = Vec::with_capacity(args.len());
    for t in args {
        let Some(p) = prove_term_false(ctx, t, assignment)? else {
            return Ok(None);
        };
        neg_proofs.push(p);
    }
    // Build `fun (h : ⟦or⟧) => elim(h) : False`, then it is the `Not ⟦or⟧` proof.
    let or_prop = or_chain_prop(ctx, args);
    let anon = ctx.kernel.anon();
    let fv = fresh_fvar_id(ctx);
    let h = ctx.kernel.fvar(fv);
    let false_const = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    let body = or_chain_to_false(ctx, args, h, &neg_proofs, false_const);
    let body = ctx.kernel.abstract_fvars(body, &[fv]);
    Ok(Some(ctx.kernel.lam(
        anon,
        or_prop,
        body,
        BinderInfo::Default,
    )))
}

/// Eliminate `h : Or ⟦args[0]⟧ (Or … )` into `False`, given a `Not ⟦argsᵢ⟧` proof
/// for each operand. Recurses over the right-nested `Or` via `Or.rec`.
fn or_chain_to_false(
    ctx: &mut ReconstructCtx,
    args: &[AletheTerm],
    h: ExprId,
    neg_proofs: &[ExprId],
    false_const: ExprId,
) -> ExprId {
    match args {
        [_t] => {
            // h : ⟦t⟧; neg_proofs[0] : Not ⟦t⟧ = ⟦t⟧ → False.
            ctx.kernel.app(neg_proofs[0], h)
        }
        [t0, rest @ ..] => {
            let anon = ctx.kernel.anon();
            let a = ctx.gate_term_to_prop(t0);
            let b = or_chain_prop(ctx, rest);
            // motive := fun (_ : Or a b) => False.
            let or_ab = ctx.mk_or(a, b);
            let motive = ctx
                .kernel
                .lam(anon, or_ab, false_const, BinderInfo::Default);
            // minor_inl := fun (h0 : a) => neg_proofs[0] h0.
            let fv0 = fresh_fvar_id(ctx);
            let h0 = ctx.kernel.fvar(fv0);
            let body0 = ctx.kernel.app(neg_proofs[0], h0);
            let body0 = ctx.kernel.abstract_fvars(body0, &[fv0]);
            let minor_inl = ctx.kernel.lam(anon, a, body0, BinderInfo::Default);
            // minor_inr := fun (hr : b) => <recurse on rest>.
            let fvr = fresh_fvar_id(ctx);
            let hr = ctx.kernel.fvar(fvr);
            let body_r = or_chain_to_false(ctx, rest, hr, &neg_proofs[1..], false_const);
            let body_r = ctx.kernel.abstract_fvars(body_r, &[fvr]);
            let minor_inr = ctx.kernel.lam(anon, b, body_r, BinderInfo::Default);
            // Or.rec a b motive minor_inl minor_inr h : False.
            let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![]);
            let e = ctx.kernel.app(rec, a);
            let e = ctx.kernel.app(e, b);
            let e = ctx.kernel.app(e, motive);
            let e = ctx.kernel.app(e, minor_inl);
            let e = ctx.kernel.app(e, minor_inr);
            ctx.kernel.app(e, h)
        }
        [] => false_const,
    }
}

/// Build a proof of `Not (And ⟦args[0]⟧ …)` when some operand is false. With
/// `hnf : Not ⟦tᵢ⟧`, the proof is `fun (h : ⟦and⟧) => hnf (project tᵢ from h)`.
fn prove_and_false(
    ctx: &mut ReconstructCtx,
    args: &[AletheTerm],
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    // Find a false operand; project it out of the And and feed it to its `Not`.
    let n = args.len();
    let mut false_idx = None;
    for (idx, t) in args.iter().enumerate() {
        if prove_term_false(ctx, t, assignment)?.is_some() {
            false_idx = Some(idx);
            break;
        }
    }
    let Some(idx) = false_idx else {
        return Ok(None);
    };
    let hnf = prove_term_false(ctx, &args[idx], assignment)?.expect("operand was just shown false");

    // and_prop = And a0 (And a1 (… an)); project operand `idx` out of `h`.
    let and_prop = and_chain_prop(ctx, args);
    let anon = ctx.kernel.anon();
    let fv = fresh_fvar_id(ctx);
    let h = ctx.kernel.fvar(fv);
    // Walk down the right-nested And to reach operand `idx`: take `.right` `idx`
    // times to reach the And of `args[idx..]`, then `.left` (unless it is the
    // last operand, where the residual IS `args[idx]`).
    let mut cur = h;
    for i in 0..idx {
        let a = ctx.gate_term_to_prop(&args[i]);
        let b = and_chain_prop(ctx, &args[i + 1..]);
        cur = and_project(ctx, a, b, cur, false); // take right
    }
    let proj = if idx == n - 1 {
        cur
    } else {
        let a = ctx.gate_term_to_prop(&args[idx]);
        let b = and_chain_prop(ctx, &args[idx + 1..]);
        and_project(ctx, a, b, cur, true) // take left
    };
    let body = ctx.kernel.app(hnf, proj);
    let body = ctx.kernel.abstract_fvars(body, &[fv]);
    Ok(Some(ctx.kernel.lam(
        anon,
        and_prop,
        body,
        BinderInfo::Default,
    )))
}

/// The `Prop` of the right-nested `And` chain of a non-empty operand slice.
fn and_chain_prop(ctx: &mut ReconstructCtx, args: &[AletheTerm]) -> ExprId {
    let (last, rest) = args.split_last().expect("non-empty And chain");
    let mut acc = ctx.gate_term_to_prop(last);
    for t in rest.iter().rev() {
        let head = ctx.gate_term_to_prop(t);
        acc = ctx.mk_and(head, acc);
    }
    acc
}

/// Build a proof of `Iff ⟦a⟧ ⟦b⟧` when `a`, `b` have the same truth value, else
/// `None`. `Iff.intro a b mp mpr` with both directions; the direction not taken
/// by the live branch is discharged ex-falso (it is never reached, but must
/// type-check), so we build it from the operand witnesses directly.
fn prove_iff_true(
    ctx: &mut ReconstructCtx,
    a_t: &AletheTerm,
    b_t: &AletheTerm,
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    let a_true = prove_term_true(ctx, a_t, assignment)?;
    let b_true = prove_term_true(ctx, b_t, assignment)?;
    let a = ctx.gate_term_to_prop(a_t);
    let b = ctx.gate_term_to_prop(b_t);
    let anon = ctx.kernel.anon();

    match (a_true, b_true) {
        // Both true: mp := fun (_ : a) => hb; mpr := fun (_ : b) => ha.
        (Some(ha), Some(hb)) => {
            let mp = ctx.kernel.lam(anon, a, hb, BinderInfo::Default);
            let mpr = ctx.kernel.lam(anon, b, ha, BinderInfo::Default);
            Ok(Some(iff_intro(ctx, a, b, mp, mpr)))
        }
        // Both false: mp := fun (ha : a) => absurd; mpr := fun (hb : b) => absurd.
        (None, None) => {
            let hna = prove_term_false(ctx, a_t, assignment)?.expect("a is false");
            let hnb = prove_term_false(ctx, b_t, assignment)?.expect("b is false");
            // mp : a → b := fun (ha : a) => False.rec (fun _ => b) (hna ha).
            let fv = fresh_fvar_id(ctx);
            let ha = ctx.kernel.fvar(fv);
            let false_app = ctx.kernel.app(hna, ha);
            let ex = ex_falso(ctx, b, false_app);
            let mp_body = ctx.kernel.abstract_fvars(ex, &[fv]);
            let mp = ctx.kernel.lam(anon, a, mp_body, BinderInfo::Default);
            // mpr : b → a := fun (hb : b) => False.rec (fun _ => a) (hnb hb).
            let fv2 = fresh_fvar_id(ctx);
            let hb = ctx.kernel.fvar(fv2);
            let false_app2 = ctx.kernel.app(hnb, hb);
            let ex2 = ex_falso(ctx, a, false_app2);
            let mpr_body = ctx.kernel.abstract_fvars(ex2, &[fv2]);
            let mpr = ctx.kernel.lam(anon, b, mpr_body, BinderInfo::Default);
            Ok(Some(iff_intro(ctx, a, b, mp, mpr)))
        }
        // Differ: not an Iff.
        _ => Ok(None),
    }
}

/// Build a proof of `Not (Iff ⟦a⟧ ⟦b⟧)` when `a`, `b` differ, else `None`. With
/// (say) `ha : a`, `hnb : Not b`: `fun (hiff : Iff a b) => hnb (hiff.mp ha)`.
fn prove_iff_false(
    ctx: &mut ReconstructCtx,
    a_t: &AletheTerm,
    b_t: &AletheTerm,
    assignment: &Assignment,
) -> Result<Option<ExprId>, ReconstructError> {
    let a_true = prove_term_true(ctx, a_t, assignment)?;
    let b_true = prove_term_true(ctx, b_t, assignment)?;
    let a = ctx.gate_term_to_prop(a_t);
    let b = ctx.gate_term_to_prop(b_t);
    let iff = ctx.mk_iff(a, b);
    let anon = ctx.kernel.anon();

    // We need exactly one of a,b true and the other false.
    let (mp_dir, hpos, hneg) = match (a_true, b_true) {
        (Some(ha), None) => {
            // a true, b false: hiff.mp ha : b, contradict with hnb.
            let hnb = prove_term_false(ctx, b_t, assignment)?.expect("b is false");
            (true, ha, hnb)
        }
        (None, Some(hb)) => {
            // a false, b true: hiff.mpr hb : a, contradict with hna.
            let hna = prove_term_false(ctx, a_t, assignment)?.expect("a is false");
            (false, hb, hna)
        }
        _ => return Ok(None),
    };

    // fun (hiff : Iff a b) => hneg ((Iff.rec … hiff) hpos) : False.
    let fv = fresh_fvar_id(ctx);
    let hiff = ctx.kernel.fvar(fv);
    // Extract the chosen direction from hiff via Iff.rec.
    let dir = iff_project(ctx, a, b, hiff, mp_dir);
    // Apply the direction to hpos to get the other side, then contradict.
    let other = ctx.kernel.app(dir, hpos);
    let body = ctx.kernel.app(hneg, other);
    let body = ctx.kernel.abstract_fvars(body, &[fv]);
    Ok(Some(ctx.kernel.lam(anon, iff, body, BinderInfo::Default)))
}

/// `Iff.intro a b mp mpr : Iff a b`.
pub(super) fn iff_intro(
    ctx: &mut ReconstructCtx,
    a: ExprId,
    b: ExprId,
    mp: ExprId,
    mpr: ExprId,
) -> ExprId {
    let intro = ctx.kernel.const_(ctx.prelude.iff_intro, vec![]);
    let e = ctx.kernel.app(intro, a);
    let e = ctx.kernel.app(e, b);
    let e = ctx.kernel.app(e, mp);
    ctx.kernel.app(e, mpr)
}

/// `Iff.rec`-project the `mp : a → b` (`select_mp = true`) or `mpr : b → a`
/// (`false`) direction out of `h : Iff a b`.
fn iff_project(
    ctx: &mut ReconstructCtx,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    select_mp: bool,
) -> ExprId {
    let anon = ctx.kernel.anon();
    // The projection's type: `a → b` (mp) or `b → a` (mpr).
    let (dom, cod) = if select_mp { (a, b) } else { (b, a) };
    let arrow = ctx.kernel.pi(anon, dom, cod, BinderInfo::Default);
    // motive := fun (_ : Iff a b) => arrow.
    let iff_ab = ctx.mk_iff(a, b);
    let motive = ctx.kernel.lam(anon, iff_ab, arrow, BinderInfo::Default);
    // minor := fun (mp : a → b) (mpr : b → a) => (mp | mpr).
    //   Under binders mp, mpr: mp = BVar 1, mpr = BVar 0.
    let chosen = if select_mp {
        ctx.kernel.bvar(1)
    } else {
        ctx.kernel.bvar(0)
    };
    // mpr : b → a (inner binder).
    let mpr_ty = ctx.kernel.pi(anon, b, a, BinderInfo::Default);
    let inner = ctx.kernel.lam(anon, mpr_ty, chosen, BinderInfo::Default);
    // mp : a → b (outer binder).
    let mp_ty = ctx.kernel.pi(anon, a, b, BinderInfo::Default);
    let minor = ctx.kernel.lam(anon, mp_ty, inner, BinderInfo::Default);
    // Iff.rec.{0} a b motive minor h : arrow.
    let z = ctx.kernel.level_zero();
    let rec = ctx.kernel.const_(ctx.prelude.iff_rec, vec![z]);
    let e = ctx.kernel.app(rec, a);
    let e = ctx.kernel.app(e, b);
    let e = ctx.kernel.app(e, motive);
    let e = ctx.kernel.app(e, minor);
    ctx.kernel.app(e, h)
}
