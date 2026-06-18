//! Alethe proof **emission** for quantifier-instantiation refutations
//! (Track 3 — the first quantified-`unsat` slice).
//!
//! A universally-quantified assertion `∀x. P(x)` that is refuted by **finitely
//! many ground instantiations** is the smallest quantifier proof obligation: the
//! solver finds witness terms `t1, …, tk` such that the ground set
//! `{P(t1), …, P(tk)} ∪ Γ` (where `Γ` is the quantifier-free assertions) is
//! unsatisfiable. This module emits a checkable Alethe proof of that refutation:
//!
//! 1. the universal is `assume`d as a unit clause over an **opaque `forall`
//!    atom** `(forall (x) ⟦P_body⟧)`;
//! 2. each instantiation `x := t_i` is a `forall_inst` step
//!    `(cl (not (forall (x) ⟦P_body⟧)) ⟦P(t_i)⟧)` — the Alethe instantiation
//!    lemma `∀x.P → P[t]`, whose validity is the structural substitution check
//!    `⟦P(t_i)⟧ = ⟦P_body⟧[x := t_i]`;
//! 3. each `forall_inst` is `resolution`-resolved against the `assume`d universal
//!    to the ground instance unit `(cl ⟦P(t_i)⟧)`;
//! 4. the resulting ground instances plus `Γ` are refuted by the existing EUF
//!    congruence emitter ([`crate::prove_qf_uf_unsat_alethe`]), spliced in with
//!    renamed ids.
//!
//! Emission is **self-validating**: the assembled proof is run through
//! [`axeyum_cnf::check_alethe_with`] — the internal Alethe checker plus a
//! `forall_inst` `extra` hook that re-checks the substitution structurally —
//! before being returned, so a buggy build is *rejected* (`None`), never returned
//! wrong. The `forall_inst` hook is the only rule the base checker does not know;
//! resolution, the ground EUF tail, and the empty clause are checked by
//! `check_alethe`'s own (DRAT-backed) entailment and structural rules.
//!
//! The companion reconstruction
//! ([`crate::reconstruct::reconstruct_quant_unsat_proof`]) reconstructs the same
//! proof shape to a Lean-kernel-checked `False`: the universal becomes a
//! dependent `Pi (x : α), ⟦P x⟧` axiom and each `forall_inst` is `forall_elim`
//! (application of that axiom to the witness `⟦t_i⟧`).

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm, check_alethe_with};
use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};

/// Emits a checkable Alethe refutation for a quantifier-instantiation `unsat`,
/// or `None` if the query is not a single top-level universal (plus
/// quantifier-free side assertions) refuted by finitely many ground
/// instantiations within this slice.
///
/// The returned proof, when non-`None`, is guaranteed to pass
/// [`axeyum_cnf::check_alethe_with`] (with the `forall_inst` hook; self-validated
/// before return) and to derive the empty clause `(cl)`. `None` is returned when:
///
/// - `assertions` does not contain exactly one top-level `∀x. body` with a
///   quantifier-free `body` (nested/multiple universals, existentials, or a
///   non-prenex residual are out of this slice);
/// - the body / a side assertion uses an IR shape the translator does not cover;
/// - no finite ground instantiation refutes the query (the read-only EUF emitter
///   does not refute the instantiated query); or
/// - the ground EUF tail or the assembled proof fails its own self-check.
///
/// The proof is deterministic: ids are `q_forall`, `q_inst<i>`, `q_res<i>` for
/// the quantifier layer, then the spliced ground tail's ids are prefixed `g_`.
#[must_use]
pub fn prove_quant_unsat_alethe(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    // Exactly one top-level universal; the rest are quantifier-free side facts.
    let mut universal: Option<(SymbolId, TermId)> = None;
    let mut ground: Vec<TermId> = Vec::new();
    for &a in assertions {
        if let TermNode::App {
            op: Op::Forall(var),
            args,
        } = arena.node(a)
        {
            if universal.is_some() {
                return None; // more than one top-level universal: outside this slice
            }
            let (var, body) = (*var, args[0]);
            if contains_quantifier(arena, body) {
                return None; // nested/non-prenex body
            }
            universal = Some((var, body));
        } else {
            if contains_quantifier(arena, a) {
                return None; // an existential or buried quantifier
            }
            ground.push(a);
        }
    }
    let (var, body) = universal?;

    // Find the witness instances by deciding the ground instantiation (the
    // read-only EUF emitter). We keep the minimal refuting prefix so the emitted
    // proof carries no redundant instantiation.
    let witnesses = witness_instances(arena, var, body, &ground)?;
    if witnesses.is_empty() {
        return None;
    }

    // The Alethe form of the universal body and its bound variable.
    let var_name = arena.symbol(var).0.to_owned();
    let body_alethe = term_to_alethe(arena, body)?;
    let forall_atom = AletheTerm::App(
        "forall".to_owned(),
        vec![AletheTerm::Const(var_name.clone()), body_alethe.clone()],
    );

    let mut commands: Vec<AletheCommand> = Vec::new();

    // 1. assume the universal as a unit clause over the opaque `forall` atom.
    commands.push(AletheCommand::Assume {
        id: "q_forall".to_owned(),
        clause: vec![lit(forall_atom.clone(), false)],
    });

    // 2/3. per witness: forall_inst lemma, then resolve it against the universal.
    let mut instance_ground: Vec<TermId> = Vec::with_capacity(witnesses.len());
    for (i, &t) in witnesses.iter().enumerate() {
        // P[x := t] in the IR (for the ground tail) and its Alethe form.
        let inst = substitute(arena, body, var, t)?;
        let inst_alethe = term_to_alethe(arena, inst)?;
        let inst_id = format!("q_inst{i}");
        let res_id = format!("q_res{i}");
        // forall_inst: (cl (not (forall (x) body)) body[x:=t]).
        commands.push(AletheCommand::Step {
            id: inst_id.clone(),
            clause: vec![
                lit(forall_atom.clone(), true),
                lit(inst_alethe.clone(), false),
            ],
            rule: "forall_inst".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
        });
        // resolution with the assumed universal: (cl body[x:=t]).
        commands.push(AletheCommand::Step {
            id: res_id,
            clause: vec![lit(inst_alethe, false)],
            rule: "resolution".to_owned(),
            premises: vec!["q_forall".to_owned(), inst_id],
            args: Vec::new(),
        });
        instance_ground.push(inst);
    }

    // 4. ground EUF refutation of the instances + side assertions, spliced in. The
    //    EUF emitter assumes its own units; we feed it the instances and `ground`,
    //    and prefix its ids so they do not collide with the quantifier layer.
    let mut tail_inputs = instance_ground.clone();
    tail_inputs.extend_from_slice(&ground);
    let tail = crate::prove_qf_uf_unsat_alethe(arena, &tail_inputs)?;
    // The EUF tail re-`assume`s the instance units; replace those re-assumptions
    // with references to our `q_res<i>` resolvents so the ground instances are
    // *derived from the universal*, not re-introduced as fresh hypotheses.
    splice_ground_tail(&mut commands, &tail, &instance_ground, arena);

    finish(arena, &commands, &var_name, body)
}

/// Splices the EUF ground tail onto the quantifier layer: each tail command is
/// re-emitted with its id prefixed `g_` (and its premise references likewise),
/// **except** an `assume` whose unit clause is one of the derived ground
/// instances `(cl ⟦P(t_i)⟧)` — that is dropped, and any later reference to it is
/// redirected to the corresponding `q_res<i>` resolvent. This makes the ground
/// instances flow from the quantifier instantiation rather than being
/// re-assumed, so the final empty clause depends only on `q_forall` and the side
/// assertions.
fn splice_ground_tail(
    commands: &mut Vec<AletheCommand>,
    tail: &[AletheCommand],
    instances: &[TermId],
    arena: &TermArena,
) {
    use std::collections::BTreeMap;
    // Alethe key of each instance → the `q_res<i>` id that proves its unit clause.
    let inst_keys: BTreeMap<String, String> = instances
        .iter()
        .enumerate()
        .filter_map(|(i, &t)| Some((term_to_alethe(arena, t)?.key(), format!("q_res{i}"))))
        .collect();
    // Tail id → the id later references should resolve to (prefixed, or a q_res).
    let mut remap: BTreeMap<String, String> = BTreeMap::new();
    for cmd in tail {
        match cmd {
            AletheCommand::Assume { id, clause } => {
                if let [l] = clause.as_slice() {
                    if !l.negated {
                        if let Some(res_id) = inst_keys.get(&l.atom.key()) {
                            // A re-assumption of a derived instance: redirect, drop.
                            remap.insert(id.clone(), res_id.clone());
                            continue;
                        }
                    }
                }
                let new_id = format!("g_{id}");
                remap.insert(id.clone(), new_id.clone());
                commands.push(AletheCommand::Assume {
                    id: new_id,
                    clause: clause.clone(),
                });
            }
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                args,
            } => {
                let new_id = format!("g_{id}");
                remap.insert(id.clone(), new_id.clone());
                let premises = premises
                    .iter()
                    .map(|p| remap.get(p).cloned().unwrap_or_else(|| format!("g_{p}")))
                    .collect();
                commands.push(AletheCommand::Step {
                    id: new_id,
                    clause: clause.clone(),
                    rule: rule.clone(),
                    premises,
                    args: args.clone(),
                });
            }
        }
    }
}

/// Runs the assembled proof through [`axeyum_cnf::check_alethe_with`] with the
/// `forall_inst` `extra` hook and returns it only if it checks (`Ok(true)`); any
/// other outcome yields `None`. This is the single self-validation gate.
fn finish(
    arena: &TermArena,
    commands: &[AletheCommand],
    var_name: &str,
    body: TermId,
) -> Option<Vec<AletheCommand>> {
    // The Alethe form of the body, used to re-check each `forall_inst` step's
    // substitution structurally.
    let body_alethe = term_to_alethe(arena, body)?;
    let var_name = var_name.to_owned();
    let hook = move |rule: &str, clause: &[AletheLit]| -> Option<bool> {
        if rule != "forall_inst" {
            return None;
        }
        Some(check_forall_inst(&var_name, &body_alethe, clause))
    };
    match check_alethe_with(commands, &hook) {
        Ok(true) => Some(commands.to_vec()),
        _ => None,
    }
}

/// Validates a `forall_inst` clause `(cl (not (forall (x) body)) body[x:=t])`:
/// literal 0 is the negated universal atom `(forall (x) body)` with the expected
/// `body`, and literal 1 is the positive body with every `Const(x)` replaced by
/// the **same** witness term `t` (i.e. the result equals `body[x := t]` for some
/// consistent `t`). Returns `true` iff the instantiation is structurally sound.
fn check_forall_inst(var_name: &str, body: &AletheTerm, clause: &[AletheLit]) -> bool {
    let [neg, pos] = clause else {
        return false;
    };
    if !neg.negated || pos.negated {
        return false;
    }
    // Literal 0 must be the universal atom over exactly this body.
    let AletheTerm::App(head, qargs) = &neg.atom else {
        return false;
    };
    if head != "forall" || qargs.len() != 2 {
        return false;
    }
    if qargs[0] != AletheTerm::Const(var_name.to_owned()) || &qargs[1] != body {
        return false;
    }
    // Literal 1 must be `body[x := t]` for one consistent witness `t`: infer `t`
    // from where `x` occurs in `body`, then verify the whole substitution.
    let mut witness: Option<AletheTerm> = None;
    match_substitution(var_name, body, &pos.atom, &mut witness)
}

/// Structurally matches `inst` against `body[x := ?]`, binding the witness on the
/// first `Const(x)` encountered and requiring every later `Const(x)` to map to the
/// same term. Non-`x` constants and heads must match verbatim; arities must agree.
fn match_substitution(
    var_name: &str,
    body: &AletheTerm,
    inst: &AletheTerm,
    witness: &mut Option<AletheTerm>,
) -> bool {
    match body {
        AletheTerm::Const(c) if c == var_name => {
            if let Some(w) = witness {
                w == inst
            } else {
                *witness = Some(inst.clone());
                true
            }
        }
        AletheTerm::Const(_) => body == inst,
        AletheTerm::App(bh, bargs) => {
            let AletheTerm::App(ih, iargs) = inst else {
                return false;
            };
            bh == ih
                && bargs.len() == iargs.len()
                && bargs
                    .iter()
                    .zip(iargs)
                    .all(|(b, i)| match_substitution(var_name, b, i, witness))
        }
        AletheTerm::Indexed {
            op: bo,
            indices: bi,
            args: ba,
        } => {
            let AletheTerm::Indexed {
                op: io,
                indices: ii,
                args: ia,
            } = inst
            else {
                return false;
            };
            bo == io
                && bi == ii
                && ba.len() == ia.len()
                && ba
                    .iter()
                    .zip(ia)
                    .all(|(b, i)| match_substitution(var_name, b, i, witness))
        }
    }
}

/// Finds the finite witness terms `t_i` whose instances `P(t_i)` (with the side
/// assertions) are `unsat`. Uses the enumerative-instantiation universe — the
/// ground leaves of the bound variable's sort appearing in the side assertions —
/// and keeps the **minimal** prefix of them whose instances already refute the
/// query, so the emitted proof carries no redundant instantiation.
///
/// Returns `None` if no finite ground prefix refutes the query within this slice.
fn witness_instances(
    arena: &mut TermArena,
    var: SymbolId,
    body: TermId,
    ground: &[TermId],
) -> Option<Vec<TermId>> {
    let sort = arena.symbol(var).1;
    let mut candidates = ground_terms_of_sort(arena, ground, sort);
    candidates.sort_by_key(|t| t.index());
    candidates.dedup();
    if candidates.is_empty() || candidates.len() > WITNESS_CANDIDATE_CAP {
        return None;
    }
    // Find the smallest refuting *subset*: try every combination of size `k`,
    // `k` increasing, so the emitted proof carries no redundant instantiation.
    // (Candidate counts in this slice are tiny; the cap bounds the search.)
    for k in 1..=candidates.len() {
        let mut combo = (0..k).collect::<Vec<usize>>();
        loop {
            let chosen: Vec<TermId> = combo.iter().map(|&i| candidates[i]).collect();
            let mut probe: Vec<TermId> = Vec::with_capacity(chosen.len() + ground.len());
            for &t in &chosen {
                probe.push(substitute(arena, body, var, t)?);
            }
            probe.extend_from_slice(ground);
            if crate::prove_qf_uf_unsat_alethe(arena, &probe).is_some() {
                return Some(chosen);
            }
            if !next_combination(&mut combo, candidates.len()) {
                break;
            }
        }
    }
    None
}

/// The cap on instantiation candidates the subset search will consider, bounding
/// the combinatorial witness search to this slice's small inputs.
const WITNESS_CANDIDATE_CAP: usize = 8;

/// Advance `combo` (a strictly-increasing index vector into `0..n`) to the next
/// lexicographic combination of the same size, returning `false` when exhausted.
fn next_combination(combo: &mut [usize], n: usize) -> bool {
    let k = combo.len();
    if k == 0 {
        return false;
    }
    let mut i = k;
    while i > 0 {
        i -= 1;
        if combo[i] != i + n - k {
            combo[i] += 1;
            for j in (i + 1)..k {
                combo[j] = combo[j - 1] + 1;
            }
            return true;
        }
    }
    false
}

/// The distinct ground leaves of `sort` occurring in `assertions` (variables and
/// constant literals), the instantiation universe.
fn ground_terms_of_sort(arena: &TermArena, assertions: &[TermId], sort: Sort) -> Vec<TermId> {
    use std::collections::BTreeSet;
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut out: Vec<TermId> = Vec::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t.index()) {
            continue;
        }
        if arena.sort_of(t) == sort && is_ground_leaf(arena, t) {
            out.push(t);
        }
        if let TermNode::App { args, .. } = arena.node(t) {
            stack.extend(args.iter().copied());
        }
    }
    out
}

/// Whether `t` is a usable instantiation witness: a symbol (free variable /
/// constant) or a constant literal — the ground leaves enumeration binds.
fn is_ground_leaf(arena: &TermArena, t: TermId) -> bool {
    matches!(
        arena.node(t),
        TermNode::Symbol(_)
            | TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_)
    )
}

/// Substitutes the ground term `replacement` for `var` throughout `term`
/// (capture-free since `replacement` is ground). Returns the rewritten term, or
/// `None` on an IR builder error.
fn substitute(
    arena: &mut TermArena,
    term: TermId,
    var: SymbolId,
    replacement: TermId,
) -> Option<TermId> {
    match arena.node(term) {
        TermNode::Symbol(s) if *s == var => Some(replacement),
        TermNode::Symbol(_)
        | TermNode::BoolConst(_)
        | TermNode::BvConst { .. }
        | TermNode::WideBvConst(_)
        | TermNode::IntConst(_)
        | TermNode::RealConst(_) => Some(term),
        TermNode::App { args, .. } => {
            let args = args.clone();
            let mut new_args = Vec::with_capacity(args.len());
            for a in args {
                new_args.push(substitute(arena, a, var, replacement)?);
            }
            Some(arena.rebuild_with_args(term, &new_args))
        }
    }
}

/// Whether `term` contains a quantifier anywhere in its subtree.
fn contains_quantifier(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::App { op, args } => {
            matches!(op, Op::Forall(_) | Op::Exists(_))
                || args.iter().any(|&a| contains_quantifier(arena, a))
        }
        _ => false,
    }
}

/// Builds a positive/negative [`AletheLit`] over `atom`.
fn lit(atom: AletheTerm, negated: bool) -> AletheLit {
    AletheLit { atom, negated }
}

/// Converts an IR term to an [`AletheTerm`], or `None` for an unsupported shape.
/// Mirrors the EUF emitter's translator: a symbol → `Const(name)`; `(= a b)` →
/// `App("=", …)`; a not → `App("not", …)`; an `apply(f, …)` → `App(f_name, …)`;
/// other interpreted operators → `App("{op:?}", …)` (treated uninterpreted, as the
/// EUF congruence does); constants → a stable distinguishing `Const`.
fn term_to_alethe(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    match arena.node(t) {
        TermNode::Symbol(s) => {
            let (name, _sort) = arena.symbol(*s);
            Some(AletheTerm::Const(name.to_owned()))
        }
        TermNode::BoolConst(b) => Some(AletheTerm::Const(format!("#bool:{b}"))),
        TermNode::BvConst { width, value } => {
            Some(AletheTerm::Const(format!("#bv{width}:{value}")))
        }
        TermNode::WideBvConst(w) => Some(AletheTerm::Const(format!("#wbv:{w:?}"))),
        TermNode::IntConst(i) => Some(AletheTerm::Const(format!("#int:{i}"))),
        TermNode::RealConst(r) => Some(AletheTerm::Const(format!("#real:{r:?}"))),
        TermNode::App { op, args } => {
            let head = match op {
                Op::Eq => "=".to_owned(),
                Op::BoolNot => "not".to_owned(),
                Op::Apply(func) => arena.function(*func).0.to_owned(),
                other => format!("{other:?}"),
            };
            let mut converted = Vec::with_capacity(args.len());
            for &arg in args {
                converted.push(term_to_alethe(arena, arg)?);
            }
            Some(AletheTerm::App(head, converted))
        }
    }
}

#[cfg(test)]
// The EUF test fixtures are inherently dense in single-letter names (`a`, `b`,
// `c`, `f`, `g`, `x`, …), as in the EUF emitter's own tests.
#[allow(clippy::similar_names, clippy::many_single_char_names)]
mod tests {
    use super::prove_quant_unsat_alethe;
    use axeyum_cnf::{AletheCommand, AletheLit, check_alethe_with};
    use axeyum_ir::{Sort, TermArena, TermId};

    /// Re-check a quantifier proof with the `forall_inst` hook (the emitter's own
    /// gate), asserting it derives the empty clause.
    fn recheck(arena: &TermArena, proof: &[AletheCommand], var_name: &str, body: TermId) {
        let body_alethe = super::term_to_alethe(arena, body).expect("body translates");
        let var_name = var_name.to_owned();
        let hook = move |rule: &str, clause: &[AletheLit]| -> Option<bool> {
            if rule != "forall_inst" {
                return None;
            }
            Some(super::check_forall_inst(&var_name, &body_alethe, clause))
        };
        assert_eq!(
            check_alethe_with(proof, &hook),
            Ok(true),
            "emitted quantifier proof must independently re-check to the empty clause"
        );
    }

    /// Count of `forall_inst` steps in a proof.
    fn count_inst(proof: &[AletheCommand]) -> usize {
        proof
            .iter()
            .filter(|c| matches!(c, AletheCommand::Step { rule, .. } if rule == "forall_inst"))
            .count()
    }

    /// `∀x. (f(x) = c)  ∧  ¬(f(a) = c)` — refuted by instantiating `x := a`.
    #[test]
    fn minimal_one_instance() {
        let mut arena = TermArena::new();
        let alpha = Sort::BitVec(8);
        let x = arena.declare("x", alpha).unwrap();
        let a = arena.declare("a", alpha).unwrap();
        let c = arena.declare("c", alpha).unwrap();
        let f = arena.declare_fun("f", &[alpha], alpha).unwrap();

        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let cv = arena.var(c);
        let fx_eq_c = arena.eq(fx, cv).unwrap();
        let forall = arena.forall(x, fx_eq_c).unwrap();

        let av = arena.var(a);
        let fa = arena.apply(f, &[av]).unwrap();
        let fa_eq_c = arena.eq(fa, cv).unwrap();
        let not_fa_eq_c = arena.not(fa_eq_c).unwrap();

        let proof = prove_quant_unsat_alethe(&mut arena, &[forall, not_fa_eq_c])
            .expect("emits a quantifier-instantiation proof");
        recheck(&arena, &proof, "x", fx_eq_c);
        assert_eq!(count_inst(&proof), 1, "one instantiation");
    }

    /// `∀x. (g(x) = d)  ∧  g(a) ≠ d` — the witness search keeps the minimal
    /// refuting prefix, so still one instance even with extra ground leaves.
    #[test]
    fn minimal_picks_relevant_instance() {
        let mut arena = TermArena::new();
        let alpha = Sort::BitVec(8);
        let x = arena.declare("x", alpha).unwrap();
        let a = arena.declare("a", alpha).unwrap();
        let d = arena.declare("d", alpha).unwrap();
        let g = arena.declare_fun("g", &[alpha], alpha).unwrap();

        let xv = arena.var(x);
        let gx = arena.apply(g, &[xv]).unwrap();
        let dv = arena.var(d);
        let gx_eq_d = arena.eq(gx, dv).unwrap();
        let forall = arena.forall(x, gx_eq_d).unwrap();

        let av = arena.var(a);
        let ga = arena.apply(g, &[av]).unwrap();
        let ga_eq_d = arena.eq(ga, dv).unwrap();
        let not_ga_eq_d = arena.not(ga_eq_d).unwrap();

        let proof =
            prove_quant_unsat_alethe(&mut arena, &[forall, not_ga_eq_d]).expect("emits a proof");
        recheck(&arena, &proof, "x", gx_eq_d);
        assert_eq!(count_inst(&proof), 1);
    }

    /// Two top-level universals are out of this single-universal slice: the
    /// emitter returns `None` rather than guessing.
    #[test]
    fn two_universals_is_out_of_slice() {
        let mut arena = TermArena::new();
        let alpha = Sort::BitVec(8);
        let x = arena.declare("x", alpha).unwrap();
        let y = arena.declare("y", alpha).unwrap();
        let a = arena.declare("a", alpha).unwrap();
        let c = arena.declare("c", alpha).unwrap();
        let f = arena.declare_fun("f", &[alpha], alpha).unwrap();

        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let cv = arena.var(c);
        let fx_eq_c = arena.eq(fx, cv).unwrap();
        let f1 = arena.forall(x, fx_eq_c).unwrap();
        let yv = arena.var(y);
        let fy = arena.apply(f, &[yv]).unwrap();
        let fy_eq_c = arena.eq(fy, cv).unwrap();
        let f2 = arena.forall(y, fy_eq_c).unwrap();
        let av = arena.var(a);
        let fa = arena.apply(f, &[av]).unwrap();
        let fa_eq_c = arena.eq(fa, cv).unwrap();
        let not_fa = arena.not(fa_eq_c).unwrap();

        assert!(prove_quant_unsat_alethe(&mut arena, &[f1, f2, not_fa]).is_none());
    }

    /// Two genuine instances of one universal: `∀x. f(x) = c`, with
    /// `f(a) ≠ f(b)`. Instantiating `x := a` and `x := b` gives `f(a) = c` and
    /// `f(b) = c`, hence `f(a) = f(b)` — contradicting `f(a) ≠ f(b)`.
    #[test]
    fn two_genuine_instances() {
        let mut arena = TermArena::new();
        let alpha = Sort::BitVec(8);
        let x = arena.declare("x", alpha).unwrap();
        let a = arena.declare("a", alpha).unwrap();
        let b = arena.declare("b", alpha).unwrap();
        let c = arena.declare("c", alpha).unwrap();
        let f = arena.declare_fun("f", &[alpha], alpha).unwrap();

        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let cv = arena.var(c);
        let fx_eq_c = arena.eq(fx, cv).unwrap();
        let forall = arena.forall(x, fx_eq_c).unwrap();

        let av = arena.var(a);
        let bv = arena.var(b);
        let fa = arena.apply(f, &[av]).unwrap();
        let fb = arena.apply(f, &[bv]).unwrap();
        let fa_eq_fb = arena.eq(fa, fb).unwrap();
        let not_fa_eq_fb = arena.not(fa_eq_fb).unwrap();

        let proof = prove_quant_unsat_alethe(&mut arena, &[forall, not_fa_eq_fb])
            .expect("emits a two-instance proof");
        recheck(&arena, &proof, "x", fx_eq_c);
        assert_eq!(count_inst(&proof), 2, "two instantiations");
    }

    /// Not a quantified query: the emitter declines (returns `None`).
    #[test]
    fn none_for_quantifier_free() {
        let mut arena = TermArena::new();
        let a = arena.declare("a", Sort::BitVec(8)).unwrap();
        let av = arena.var(a);
        let e = arena.eq(av, av).unwrap();
        assert!(prove_quant_unsat_alethe(&mut arena, &[e]).is_none());
    }

    /// A satisfiable universal: no finite instantiation refutes it, so `None`.
    #[test]
    fn none_for_satisfiable_universal() {
        let mut arena = TermArena::new();
        let alpha = Sort::BitVec(8);
        let x = arena.declare("x", alpha).unwrap();
        let a = arena.declare("a", alpha).unwrap();
        let c = arena.declare("c", alpha).unwrap();
        let f = arena.declare_fun("f", &[alpha], alpha).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let cv = arena.var(c);
        let fx_eq_c = arena.eq(fx, cv).unwrap();
        let forall = arena.forall(x, fx_eq_c).unwrap();
        // `f(a) = c` is consistent with the universal: satisfiable, no proof.
        let av = arena.var(a);
        let fa = arena.apply(f, &[av]).unwrap();
        let fa_eq_c = arena.eq(fa, cv).unwrap();
        assert!(prove_quant_unsat_alethe(&mut arena, &[forall, fa_eq_c]).is_none());
    }
}
