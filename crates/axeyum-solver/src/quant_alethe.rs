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

use std::collections::BTreeMap;

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm, check_alethe_with};
use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};

/// Emits a checkable Alethe refutation for a quantifier-instantiation `unsat`,
/// or `None` if the query is not one or more top-level universals (plus
/// quantifier-free side assertions) refuted by finitely many ground
/// instantiations within this slice.
///
/// Each top-level universal `∀x. body` (with a quantifier-free `body`) becomes
/// its own opaque `forall` atom and its own `assume`d axiom; the universals may
/// share a bound-variable name (they are distinguished by body). Every ground
/// instance — over every universal — flows into a single shared EUF/`QF_BV` ground
/// refutation. Nested universals (`∀x.∀y. body`) are out of this slice (the body
/// carries its own quantifier) and yield `None`.
///
/// The returned proof, when non-`None`, is guaranteed to pass
/// [`axeyum_cnf::check_alethe_with`] (with the `forall_inst` hook; self-validated
/// before return) and to derive the empty clause `(cl)`. `None` is returned when:
///
/// - `assertions` contains no top-level `∀x. body`, or a body / side assertion
///   carries a nested quantifier (existential or buried quantifier);
/// - the body / a side assertion uses an IR shape the translator does not cover;
/// - no finite ground instantiation refutes the query (the read-only EUF emitter
///   does not refute the instantiated query); or
/// - the ground EUF tail or the assembled proof fails its own self-check.
///
/// The proof is deterministic: per universal `j` the ids are `q_forall<j>`,
/// `q_inst<j>_<i>`, `q_res<j>_<i>` for the quantifier layer, then the spliced
/// ground tail's ids are prefixed `g_`.
#[must_use]
pub fn prove_quant_unsat_alethe(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    // Partition into top-level universals and quantifier-free side facts. A
    // universal may be a chain `∀x.∀y. body` — peel the chain to a list of bound
    // variables and a quantifier-free inner body.
    let mut universals: Vec<Universal> = Vec::new();
    let mut ground: Vec<TermId> = Vec::new();
    for &a in assertions {
        if matches!(
            arena.node(a),
            TermNode::App {
                op: Op::Forall(_),
                ..
            }
        ) {
            let u = peel_universal(arena, a)?;
            universals.push(u);
        } else {
            if contains_quantifier(arena, a) {
                return None; // an existential or buried quantifier
            }
            ground.push(a);
        }
    }
    if universals.is_empty() {
        return None;
    }

    // Jointly find the witness instances across all universals by deciding the
    // ground instantiation (the read-only EUF emitter). Prefer the brute-force
    // cartesian/subset search for tiny inputs (it yields the minimal refuting
    // subset); when that would exceed the candidate cap — many ground terms or
    // several binders — fall back to the solver's trigger-driven e-matching, which
    // scales to real quantified queries.
    let chosen = witness_instances_multi(arena, &universals, &ground)
        .or_else(|| witness_instances_via_ematch(arena, &universals, &ground))?;
    if chosen.iter().all(Vec::is_empty) {
        return None;
    }

    let mut commands: Vec<AletheCommand> = Vec::new();

    // 1. assume each universal as a unit clause over its opaque (possibly nested)
    //    `forall` atom `(forall (x) (forall (y) … body))`.
    let mut forall_atoms: Vec<AletheTerm> = Vec::with_capacity(universals.len());
    for (j, u) in universals.iter().enumerate() {
        let forall_atom = forall_atom_of(arena, u)?;
        commands.push(AletheCommand::Assume {
            id: format!("q_forall{j}"),
            clause: vec![lit(forall_atom.clone(), false)],
        });
        forall_atoms.push(forall_atom);
    }

    // 2/3. per universal, per witness tuple: forall_inst lemma, then resolve it
    //      against the matching universal axiom. We keep each instance paired with
    //      the `q_res<j>_<i>` id that proves its unit, for splicing the ground tail.
    let mut instance_ground: Vec<(TermId, String)> = Vec::new();
    for (j, u) in universals.iter().enumerate() {
        for (i, tuple) in chosen[j].iter().enumerate() {
            // body[x:=s, y:=t, …] in the IR (for the ground tail) and its Alethe.
            let inst = substitute_tuple(arena, u, tuple)?;
            let inst_alethe = term_to_alethe(arena, inst)?;
            let inst_id = format!("q_inst{j}_{i}");
            let res_id = format!("q_res{j}_{i}");
            // forall_inst: (cl (not (forall (x) … body)) body[x:=s, …]).
            commands.push(AletheCommand::Step {
                id: inst_id.clone(),
                clause: vec![
                    lit(forall_atoms[j].clone(), true),
                    lit(inst_alethe.clone(), false),
                ],
                rule: "forall_inst".to_owned(),
                premises: Vec::new(),
                args: Vec::new(),
            });
            // resolution with the assumed universal: (cl body[x:=s, …]).
            commands.push(AletheCommand::Step {
                id: res_id.clone(),
                clause: vec![lit(inst_alethe, false)],
                rule: "resolution".to_owned(),
                premises: vec![format!("q_forall{j}"), inst_id],
                args: Vec::new(),
            });
            instance_ground.push((inst, res_id));
        }
    }

    // 4. ground EUF refutation of the instances + side assertions, spliced in. The
    //    EUF emitter assumes its own units; we feed it the instances and `ground`,
    //    and prefix its ids so they do not collide with the quantifier layer.
    let mut tail_inputs: Vec<TermId> = instance_ground.iter().map(|&(t, _)| t).collect();
    tail_inputs.extend_from_slice(&ground);
    let tail = crate::prove_qf_uf_unsat_alethe(arena, &tail_inputs)?;
    // The EUF tail re-`assume`s the instance units; replace those re-assumptions
    // with references to our `q_res<j>_<i>` resolvents so the ground instances are
    // *derived from the universals*, not re-introduced as fresh hypotheses.
    splice_ground_tail(&mut commands, &tail, &instance_ground, arena);

    finish(arena, &commands, &universals)
}

/// A top-level universal as a (possibly nested) **binder chain** `∀x.∀y.… body`:
/// the ordered bound variables and the quantifier-free inner body (with the bound
/// variables free as `Symbol`s). A single universal `∀x. body` is the one-variable
/// case (`vars = [x]`).
struct Universal {
    /// The bound variables, outermost first.
    vars: Vec<SymbolId>,
    /// The quantifier-free inner body.
    body: TermId,
}

/// Peel a top-level `∀x.∀y.… body` chain into its [`Universal`]. Returns `None`
/// if, after peeling all leading universals, the inner body still contains a
/// quantifier (a non-prenex residual or an existential) — out of this slice.
fn peel_universal(arena: &TermArena, mut term: TermId) -> Option<Universal> {
    let mut vars = Vec::new();
    while let TermNode::App {
        op: Op::Forall(var),
        args,
    } = arena.node(term)
    {
        vars.push(*var);
        term = args[0];
    }
    if vars.is_empty() || contains_quantifier(arena, term) {
        return None;
    }
    Some(Universal { vars, body: term })
}

/// Build the opaque Alethe `forall` atom for a (nested) universal:
/// `(forall (x) (forall (y) … ⟦body⟧))`, one `forall` wrapper per bound variable
/// outermost-first.
fn forall_atom_of(arena: &TermArena, u: &Universal) -> Option<AletheTerm> {
    let mut atom = term_to_alethe(arena, u.body)?;
    for &var in u.vars.iter().rev() {
        let var_name = arena.symbol(var).0.to_owned();
        atom = AletheTerm::App("forall".to_owned(), vec![AletheTerm::Const(var_name), atom]);
    }
    Some(atom)
}

/// Substitute a witness tuple `[s, t, …]` for the bound variables `[x, y, …]` of a
/// universal, yielding the ground instance `body[x:=s, y:=t, …]`. The tuple length
/// must match the binder count.
fn substitute_tuple(arena: &mut TermArena, u: &Universal, tuple: &[TermId]) -> Option<TermId> {
    if tuple.len() != u.vars.len() {
        return None;
    }
    let mut t = u.body;
    for (&var, &val) in u.vars.iter().zip(tuple) {
        t = substitute(arena, t, var, val)?;
    }
    Some(t)
}

/// Splices the EUF ground tail onto the quantifier layer: each tail command is
/// re-emitted with its id prefixed `g_` (and its premise references likewise),
/// **except** an `assume` whose unit clause is one of the derived ground
/// instances `(cl ⟦P(t_i)⟧)` — that is dropped, and any later reference to it is
/// redirected to the corresponding `q_res<j>_<i>` resolvent. This makes the ground
/// instances flow from the quantifier instantiation rather than being
/// re-assumed, so the final empty clause depends only on the universal axioms and
/// the side assertions.
///
/// Each instance is paired with the id of the resolvent that proves its unit, so
/// instances from different universals redirect to the right `q_res<j>_<i>`.
fn splice_ground_tail(
    commands: &mut Vec<AletheCommand>,
    tail: &[AletheCommand],
    instances: &[(TermId, String)],
    arena: &TermArena,
) {
    use std::collections::BTreeMap;
    // Alethe key of each instance → the `q_res<j>_<i>` id that proves its unit.
    let inst_keys: BTreeMap<String, String> = instances
        .iter()
        .filter_map(|(t, res_id)| Some((term_to_alethe(arena, *t)?.key(), res_id.clone())))
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
///
/// The hook closes over the bound-variable names and inner body of **every**
/// universal in the query (a chain `∀x.∀y.…` carries all its variables), so a
/// `forall_inst` step is validated against whichever universal its literal-0
/// (possibly nested) `(forall (x) … body)` atom identifies.
fn finish(
    arena: &TermArena,
    commands: &[AletheCommand],
    universals: &[Universal],
) -> Option<Vec<AletheCommand>> {
    // The bound-variable names and inner body of each universal, used to re-check
    // each `forall_inst` step's substitution structurally.
    let mut forms: Vec<(Vec<String>, AletheTerm)> = Vec::with_capacity(universals.len());
    for u in universals {
        let names: Vec<String> = u
            .vars
            .iter()
            .map(|&v| arena.symbol(v).0.to_owned())
            .collect();
        forms.push((names, term_to_alethe(arena, u.body)?));
    }
    let hook = move |rule: &str, clause: &[AletheLit]| -> Option<bool> {
        if rule != "forall_inst" {
            return None;
        }
        // Accept the step iff it is a sound instantiation of some universal.
        Some(
            forms
                .iter()
                .any(|(names, body)| check_forall_inst(names, body, clause)),
        )
    };
    match check_alethe_with(commands, &hook) {
        Ok(true) => Some(commands.to_vec()),
        _ => None,
    }
}

/// Validates a `forall_inst` clause `(cl (not (forall (x) … body)) body[x:=s, …])`:
/// literal 0 is the negated (possibly nested) universal atom `(forall (x) …
/// body)`, whose peeled binder names must equal `var_names` and whose inner body
/// must equal `body`; literal 1 is the positive body with each bound `Const(x_i)`
/// replaced by a **consistent** witness `t_i` (i.e. the result equals
/// `body[x_1:=t_1, …]` for some witness tuple). Returns `true` iff the
/// instantiation is structurally sound for **this** universal chain.
fn check_forall_inst(var_names: &[String], body: &AletheTerm, clause: &[AletheLit]) -> bool {
    let [neg, pos] = clause else {
        return false;
    };
    if !neg.negated || pos.negated {
        return false;
    }
    // Literal 0 must be the (nested) universal atom over exactly these binders and
    // this inner body.
    let mut atom = &neg.atom;
    for name in var_names {
        let AletheTerm::App(head, qargs) = atom else {
            return false;
        };
        if head != "forall" || qargs.len() != 2 {
            return false;
        }
        if qargs[0] != AletheTerm::Const(name.clone()) {
            return false;
        }
        atom = &qargs[1];
    }
    if atom != body {
        return false;
    }
    // Literal 1 must be `body[x_i := t_i]` for a consistent witness tuple: infer
    // each `t_i` from where `x_i` occurs in `body`, then verify the substitution.
    let mut witnesses: BTreeMap<String, AletheTerm> = BTreeMap::new();
    match_substitution(var_names, body, &pos.atom, &mut witnesses)
}

/// Structurally matches `inst` against `body[x_i := ?]`, binding each bound
/// variable's witness on its first occurrence and requiring every later occurrence
/// to map to the same term. Non-bound constants and heads must match verbatim;
/// arities must agree.
fn match_substitution(
    var_names: &[String],
    body: &AletheTerm,
    inst: &AletheTerm,
    witnesses: &mut BTreeMap<String, AletheTerm>,
) -> bool {
    match body {
        AletheTerm::Const(c) if var_names.iter().any(|v| v == c) => {
            if let Some(w) = witnesses.get(c) {
                w == inst
            } else {
                witnesses.insert(c.clone(), inst.clone());
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
                    .all(|(b, i)| match_substitution(var_names, b, i, witnesses))
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
                    .all(|(b, i)| match_substitution(var_names, b, i, witnesses))
        }
    }
}

/// Jointly finds the finite witness **tuples** for **every** universal whose
/// instances (with the side assertions) are `unsat`. Each universal `j` draws
/// each binder's witness from the enumerative-instantiation universe of that
/// binder's sort — the ground leaves appearing in the side assertions — and its
/// candidate witness tuples are the cartesian product over the binders. The search
/// returns the **minimal** refuting subset across all universals (smallest total
/// instance count first), so the emitted proof carries no redundant instantiation.
///
/// The return value is one list of witness tuples per universal (parallel to
/// `universals`); each tuple has one term per binder. Some lists may be empty when
/// that universal is not needed for the refutation.
///
/// Returns `None` if no finite ground subset refutes the query within this slice.
fn witness_instances_multi(
    arena: &mut TermArena,
    universals: &[Universal],
    ground: &[TermId],
) -> Option<Vec<Vec<Vec<TermId>>>> {
    // The flat candidate list: each entry is `(universal_index, witness_tuple)`,
    // labelled so the chosen subset can be projected back per universal.
    let mut candidates: Vec<(usize, Vec<TermId>)> = Vec::new();
    for (j, u) in universals.iter().enumerate() {
        // Per binder, the ground leaves of its sort; then the cartesian product.
        let mut per_binder: Vec<Vec<TermId>> = Vec::with_capacity(u.vars.len());
        for &var in &u.vars {
            let sort = arena.symbol(var).1;
            let mut leaves = ground_terms_of_sort(arena, ground, sort);
            leaves.sort_by_key(|t| t.index());
            leaves.dedup();
            if leaves.is_empty() {
                return None; // a binder with no candidate witness: no instance
            }
            per_binder.push(leaves);
        }
        for tuple in cartesian_product(&per_binder) {
            candidates.push((j, tuple));
        }
    }
    if candidates.is_empty() || candidates.len() > WITNESS_CANDIDATE_CAP {
        return None;
    }
    // Find the smallest refuting *subset* of labelled candidates: try every
    // combination of size `k`, `k` increasing, so the emitted proof carries no
    // redundant instantiation. (Candidate counts in this slice are tiny; the cap
    // bounds the search.)
    for k in 1..=candidates.len() {
        let mut combo = (0..k).collect::<Vec<usize>>();
        loop {
            let mut probe: Vec<TermId> = Vec::with_capacity(k + ground.len());
            for &idx in &combo {
                let (j, tuple) = &candidates[idx];
                probe.push(substitute_tuple(arena, &universals[*j], tuple)?);
            }
            probe.extend_from_slice(ground);
            if crate::prove_qf_uf_unsat_alethe(arena, &probe).is_some() {
                // Project the chosen labelled candidates back per universal.
                let mut chosen: Vec<Vec<Vec<TermId>>> = vec![Vec::new(); universals.len()];
                for &idx in &combo {
                    let (j, tuple) = &candidates[idx];
                    chosen[*j].push(tuple.clone());
                }
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
/// the combinatorial witness search to this slice's small inputs. Nested
/// universals form witness *tuples* (a cartesian product over their binders), so
/// the cap is large enough to admit a couple of binders over a handful of ground
/// leaves while keeping the worst-case subset enumeration (2^cap) bounded.
const WITNESS_CANDIDATE_CAP: usize = 16;

/// Sources the witness tuples from the solver's **trigger-driven e-matching**
/// (`crate::witness_tuples_via_egraph`) instead of the brute-force cartesian/subset
/// search, so a quantified `unsat` the solver decides scalably also gets an
/// emitted, kernel-reconstructible proof. This is the fallback when
/// [`witness_instances_multi`] declines (the cartesian candidate set exceeds
/// [`WITNESS_CANDIDATE_CAP`], or a binder has no ground leaf of its sort).
///
/// For each universal it e-matches the body's trigger(s) against the ground
/// assertions to get candidate witness tuples (one ground term per binder, in
/// binder order). It then **validates** that those instances actually refute: the
/// full e-matched instance set plus the side assertions must be `unsat` under the
/// read-only EUF/`QF_BV` emitter. If so, a small minimal-subset trim keeps the
/// emitted proof tidy when it is cheap (few candidates); otherwise the full,
/// validated set is used. The validation makes a wrong/insufficient match set fail
/// cleanly (`None`) rather than ever producing a bad proof.
///
/// Returns the per-universal witness tuples (parallel to `universals`), or `None`
/// when e-matching finds no tuple for some universal or no refuting instance set.
fn witness_instances_via_ematch(
    arena: &mut TermArena,
    universals: &[Universal],
    ground: &[TermId],
) -> Option<Vec<Vec<Vec<TermId>>>> {
    // E-match each universal independently against the ground assertions. A
    // universal that contributes no tuple stays empty (it may not be needed).
    let mut per_universal: Vec<Vec<Vec<TermId>>> = Vec::with_capacity(universals.len());
    for u in universals {
        // Reconstruct the universal's `forall` term so the e-matcher can peel it.
        let forall_term = rebuild_forall_term(arena, u)?;
        let tuples = match crate::witness_tuples_via_egraph(arena, ground, forall_term) {
            Some((_, _, tuples)) => tuples,
            None => Vec::new(),
        };
        per_universal.push(tuples);
    }
    if per_universal.iter().all(Vec::is_empty) {
        return None;
    }

    // Validate the full e-matched instance set refutes; if not, this shape is not
    // (yet) decided by e-matching here — decline cleanly.
    if !refutes(arena, universals, &per_universal, ground)? {
        return None;
    }

    // Optional minimal-subset trim: greedily drop tuples whose removal keeps the
    // ground set unsat, so the emitted proof carries no redundant instantiation.
    // Bounded by the small e-matched candidate count, so it stays cheap.
    let total: usize = per_universal.iter().map(Vec::len).sum();
    if total <= WITNESS_CANDIDATE_CAP {
        trim_minimal(arena, universals, &mut per_universal, ground)?;
    }
    Some(per_universal)
}

/// Whether the instances obtained by substituting `chosen` into the universals,
/// together with the side assertions, are refuted by the read-only EUF/`QF_BV`
/// emitter. `None` on a substitution/IR error.
fn refutes(
    arena: &mut TermArena,
    universals: &[Universal],
    chosen: &[Vec<Vec<TermId>>],
    ground: &[TermId],
) -> Option<bool> {
    let mut probe: Vec<TermId> = Vec::new();
    for (u, tuples) in universals.iter().zip(chosen) {
        for tuple in tuples {
            probe.push(substitute_tuple(arena, u, tuple)?);
        }
    }
    probe.extend_from_slice(ground);
    Some(crate::prove_qf_uf_unsat_alethe(arena, &probe).is_some())
}

/// Greedily removes any single witness tuple whose deletion preserves the
/// refutation, leaving a (locally) minimal refuting set. Mutates `chosen` in place.
/// `None` on a substitution/IR error.
fn trim_minimal(
    arena: &mut TermArena,
    universals: &[Universal],
    chosen: &mut [Vec<Vec<TermId>>],
    ground: &[TermId],
) -> Option<()> {
    let mut changed = true;
    while changed {
        changed = false;
        'outer: for j in 0..chosen.len() {
            for i in 0..chosen[j].len() {
                let removed = chosen[j].remove(i);
                if refutes(arena, universals, chosen, ground)? {
                    changed = true;
                    break 'outer; // restart the scan after a successful removal
                }
                chosen[j].insert(i, removed);
            }
        }
    }
    Some(())
}

/// Rebuilds the IR `forall` term `∀x.∀y.… body` for a peeled [`Universal`], so the
/// e-matcher (which peels a `forall` term) can be driven from the emitter's
/// already-peeled representation. `None` on an IR builder error.
fn rebuild_forall_term(arena: &mut TermArena, u: &Universal) -> Option<TermId> {
    let mut term = u.body;
    for &var in u.vars.iter().rev() {
        term = arena.forall(var, term).ok()?;
    }
    Some(term)
}

/// The cartesian product of `per_binder[0] × per_binder[1] × …`, in
/// lexicographic order with the first binder varying slowest. With no binders
/// (empty input) yields a single empty tuple; with any empty factor yields none.
fn cartesian_product(per_binder: &[Vec<TermId>]) -> Vec<Vec<TermId>> {
    let mut out: Vec<Vec<TermId>> = vec![Vec::new()];
    for factor in per_binder {
        let mut next = Vec::with_capacity(out.len() * factor.len());
        for prefix in &out {
            for &t in factor {
                let mut tuple = prefix.clone();
                tuple.push(t);
                next.push(tuple);
            }
        }
        out = next;
    }
    out
}

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
        let var_names = vec![var_name.to_owned()];
        let hook = move |rule: &str, clause: &[AletheLit]| -> Option<bool> {
            if rule != "forall_inst" {
                return None;
            }
            Some(super::check_forall_inst(&var_names, &body_alethe, clause))
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

    /// **Two top-level universals**: `∀x.(f x = a) ∧ ∀y.(f y = b) ∧ a ≠ b`.
    /// Instantiating both at the same witness `w` gives `f w = a` and `f w = b`,
    /// hence `a = b`, contradicting `a ≠ b`. Each universal becomes its own
    /// `forall` axiom; each `forall_inst` cites the matching one.
    #[test]
    fn two_universals_both_instantiated() {
        let mut arena = TermArena::new();
        let alpha = Sort::BitVec(8);
        let x = arena.declare("x", alpha).unwrap();
        let y = arena.declare("y", alpha).unwrap();
        let a = arena.declare("a", alpha).unwrap();
        let b = arena.declare("b", alpha).unwrap();
        let f = arena.declare_fun("f", &[alpha], alpha).unwrap();

        let av = arena.var(a);
        let bv = arena.var(b);

        // ∀x. f(x) = a
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let fx_eq_a = arena.eq(fx, av).unwrap();
        let f1 = arena.forall(x, fx_eq_a).unwrap();
        // ∀y. f(y) = b
        let yv = arena.var(y);
        let fy = arena.apply(f, &[yv]).unwrap();
        let fy_eq_b = arena.eq(fy, bv).unwrap();
        let f2 = arena.forall(y, fy_eq_b).unwrap();
        // a ≠ b  (the witness comes from these leaves; both universals share it)
        let a_eq_b = arena.eq(av, bv).unwrap();
        let not_a_eq_b = arena.not(a_eq_b).unwrap();

        let proof = prove_quant_unsat_alethe(&mut arena, &[f1, f2, not_a_eq_b])
            .expect("emits a two-universal refutation");
        // Re-check with a hook that accepts an instantiation of either universal.
        let forms = [("x", fx_eq_a), ("y", fy_eq_b)];
        let alethe_forms: Vec<(Vec<String>, _)> = forms
            .iter()
            .map(|&(n, body)| {
                (
                    vec![n.to_owned()],
                    super::term_to_alethe(&arena, body).expect("body translates"),
                )
            })
            .collect();
        let hook = move |rule: &str, clause: &[AletheLit]| -> Option<bool> {
            if rule != "forall_inst" {
                return None;
            }
            Some(
                alethe_forms
                    .iter()
                    .any(|(n, body)| super::check_forall_inst(n, body, clause)),
            )
        };
        assert_eq!(
            check_alethe_with(&proof, &hook),
            Ok(true),
            "two-universal proof must independently re-check to the empty clause"
        );
        // Two universals, each instantiated once at the shared witness.
        assert_eq!(count_inst(&proof), 2, "one instantiation per universal");
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

    /// **Nested universal**: `∀x.∀y.(h x y = c) ∧ ¬(h s t = c)`. Instantiating the
    /// chain at `x := s, y := t` gives `h s t = c`, contradicting `¬(h s t = c)`.
    /// One `forall_inst` over the nested `(forall (x) (forall (y) …))` atom.
    #[test]
    fn nested_universal_one_instance() {
        let mut arena = TermArena::new();
        let alpha = Sort::BitVec(8);
        let x = arena.declare("x", alpha).unwrap();
        let y = arena.declare("y", alpha).unwrap();
        let s = arena.declare("s", alpha).unwrap();
        let t = arena.declare("t", alpha).unwrap();
        let c = arena.declare("c", alpha).unwrap();
        let h = arena.declare_fun("h", &[alpha, alpha], alpha).unwrap();

        let xv = arena.var(x);
        let yv = arena.var(y);
        let cv = arena.var(c);
        let hxy = arena.apply(h, &[xv, yv]).unwrap();
        let hxy_eq_c = arena.eq(hxy, cv).unwrap();
        // ∀x.∀y. h(x, y) = c
        let inner = arena.forall(y, hxy_eq_c).unwrap();
        let forall = arena.forall(x, inner).unwrap();
        // ¬(h(s, t) = c)
        let sv = arena.var(s);
        let tv = arena.var(t);
        let hst = arena.apply(h, &[sv, tv]).unwrap();
        let hst_eq_c = arena.eq(hst, cv).unwrap();
        let not_hst = arena.not(hst_eq_c).unwrap();

        let proof = prove_quant_unsat_alethe(&mut arena, &[forall, not_hst])
            .expect("emits a nested-universal proof");
        // Re-check with a hook over the two-binder chain `[x, y]` and inner body.
        let body_alethe = super::term_to_alethe(&arena, hxy_eq_c).expect("body translates");
        let names = vec!["x".to_owned(), "y".to_owned()];
        let hook = move |rule: &str, clause: &[AletheLit]| -> Option<bool> {
            if rule != "forall_inst" {
                return None;
            }
            Some(super::check_forall_inst(&names, &body_alethe, clause))
        };
        assert_eq!(
            check_alethe_with(&proof, &hook),
            Ok(true),
            "nested-universal proof must independently re-check to the empty clause"
        );
        assert_eq!(count_inst(&proof), 1, "one nested instantiation");
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

    /// **Scale past the brute-force cap via e-matching**: `∀x.(f x = c)` with the
    /// single refuting fact `f a ≠ c`, but buried among **far more ground leaves of
    /// the binder's sort** than [`super::WITNESS_CANDIDATE_CAP`]. The cartesian
    /// candidate count (one per leaf) overflows the cap, so the brute-force
    /// `witness_instances_multi` returns `None`; the trigger `f(x)` only matches the
    /// lone `f`-application `f(a)`, so the e-matching path picks `x := a` and the
    /// proof still emits + self-checks. The decoys never enter the proof.
    #[test]
    fn ematch_sources_witness_past_cap() {
        let mut arena = TermArena::new();
        let alpha = Sort::BitVec(8);
        let x = arena.declare("x", alpha).unwrap();
        let a = arena.declare("a", alpha).unwrap();
        let c = arena.declare("c", alpha).unwrap();
        let f = arena.declare_fun("f", &[alpha], alpha).unwrap();

        let xv = arena.var(x);
        let cv = arena.var(c);
        let fx = arena.apply(f, &[xv]).unwrap();
        let fx_eq_c = arena.eq(fx, cv).unwrap();
        let forall = arena.forall(x, fx_eq_c).unwrap();

        // The single refuting fact.
        let av = arena.var(a);
        let fa = arena.apply(f, &[av]).unwrap();
        let fa_eq_c = arena.eq(fa, cv).unwrap();
        let not_fa_eq_c = arena.not(fa_eq_c).unwrap();

        // Many decoy ground leaves of the binder's sort `alpha`, all summed into one
        // harmless ground equality so they are collected as instantiation
        // candidates. 24 decoys ≫ the cap of 16, so the cartesian search bails.
        let mut decoys: Vec<TermId> = Vec::new();
        for i in 0..24u32 {
            let s = arena.declare(&format!("d{i}"), alpha).unwrap();
            decoys.push(arena.var(s));
        }
        let mut acc = decoys[0];
        for &d in &decoys[1..] {
            acc = arena.bv_add(acc, d).unwrap();
        }
        let sum_eq_self = arena.eq(acc, acc).unwrap();

        // Confirm the brute-force path alone would decline (cap exceeded).
        let universals = vec![super::Universal {
            vars: vec![x],
            body: fx_eq_c,
        }];
        let ground = vec![not_fa_eq_c, sum_eq_self];
        assert!(
            super::witness_instances_multi(&mut arena, &universals, &ground).is_none(),
            "brute-force must bail past the candidate cap"
        );

        // The full emitter sources the witness from e-matching and still proves it.
        let proof = prove_quant_unsat_alethe(&mut arena, &[forall, not_fa_eq_c, sum_eq_self])
            .expect("e-matching sources the witness past the brute-force cap");
        recheck(&arena, &proof, "x", fx_eq_c);
        assert_eq!(count_inst(&proof), 1, "only the relevant f(a) instance");
    }
}
