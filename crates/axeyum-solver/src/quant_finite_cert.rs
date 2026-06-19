//! Checkable Alethe certificate for a **finite-expansion guarded-`Int` universal**
//! `unsat` (the first finite quantifier-proof slice).
//!
//! A very common decidable quantified shape is a universal whose body *guards* an
//! integer variable to a concrete range:
//!
//! ```text
//! ∀x:Int. (lo <= x ∧ x <= hi) => inner(x)
//! ```
//!
//! For an integer `x` this is logically equivalent to the finite conjunction
//! `⋀_{v=lo}^{hi} inner[x:=v]` (outside `[lo, hi]` the guard is false, so the
//! implication is vacuously true; see [`crate::quant_guarded_int`]). When those
//! ground instances — together with the quantifier-free side assertions — are
//! `unsat` in linear integer arithmetic, this module emits an **independently
//! checkable** Alethe refutation rather than a bare `Evidence::Unsat(None)`:
//!
//! 1. the universal is `assume`d as a unit clause over an opaque
//!    `(forall (x) ⟦(=> guard inner)⟧)` atom;
//! 2. each in-range value `v ∈ [lo, hi]` yields a **`forall_inst_guarded`** step
//!    `(cl (not (forall (x) …)) ⟦inner[x:=v]⟧)` — the instantiation lemma
//!    `∀x.(g ⇒ i) ∧ g[v] ⊢ i[v]` specialised to a *concretely-true* guard, whose
//!    validity is re-checked structurally (`⟦inner[x:=v]⟧ = ⟦inner⟧[x:=v]`) **and**
//!    arithmetically (`guard[x:=v]` is a true ground `Int` fact) by the checker
//!    hook below — so it is **certified, not trusted**;
//! 3. each `forall_inst_guarded` is `resolution`-resolved against the assumed
//!    universal to the ground instance unit `(cl ⟦inner[x:=v]⟧)`;
//! 4. those instances plus the side assertions are refuted by the existing
//!    `lia_generic` ground emitter ([`crate::prove_lia_unsat_alethe`]), spliced in
//!    with renamed ids.
//!
//! Emission is **self-validating**: the assembled proof is run through
//! [`check_alethe_lra_guarded_inst`] — the arithmetic-aware Alethe checker plus the
//! `forall_inst_guarded` hook — before being returned, so a buggy build is
//! *rejected* (`None`), never returned wrong. The same checker re-validates the
//! attached [`crate::Evidence::UnsatGuardedQuantAletheProof`] in
//! [`crate::Evidence::check`].
//!
//! This slice is deliberately narrow: a **single** guarded-finite-`Int` universal
//! with a quantifier-free body whose inner is a linear-integer comparison, plus
//! quantifier-free linear-integer side assertions. Anything else declines cleanly
//! (`None`), leaving the existing bare-`unsat` behaviour untouched.

use std::collections::HashMap;

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm, check_alethe_with};
use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

use crate::alethe_lra::{int_atom_to_alethe_pub, la_generic_check_pub};
use crate::backend::CheckResult;
use crate::lra::check_with_lia_simplex;

/// The largest integer range `hi - lo + 1` this certificate will expand over,
/// matching [`crate::quant_guarded_int::RANGE_SIZE_CAP`] so a certificate is
/// attempted exactly when the guarded-`Int` decision pass fires.
const RANGE_SIZE_CAP: i128 = 4096;

/// A detected guarded-finite-`Int` universal `∀x:Int. (lo<=x<=hi) => inner`.
struct GuardedUniversal {
    /// The bound integer variable `x`.
    var: SymbolId,
    /// The guard subterm `(and lo<=x x<=hi)`.
    guard: TermId,
    /// The inner consequent `inner` (with `x` free).
    inner: TermId,
    /// The inclusive range `[lo, hi]`.
    lo: i128,
    /// The inclusive range `[lo, hi]`.
    hi: i128,
}

/// Emits a checkable Alethe refutation for a finite-expansion guarded-`Int`
/// universal `unsat`, or `None` if `assertions` are not of this slice or not
/// refuted within it.
///
/// `assertions` must be exactly one guarded-finite-`Int` universal
/// `∀x:Int. (lo<=x<=hi) => inner` (an `Int` bound variable, a concrete range
/// within `RANGE_SIZE_CAP`, and a quantifier-free inner that translates to a
/// linear-integer comparison) plus zero or more quantifier-free linear-integer
/// side assertions, whose finite expansion `⋀_{v=lo}^{hi} inner[x:=v]` together
/// with the side assertions is integer-`unsat`.
///
/// The returned proof, when non-`None`, is guaranteed to pass
/// [`check_alethe_lra_guarded_inst`] and to derive the empty clause `(cl)`.
#[must_use]
pub fn prove_finite_int_quant_unsat_alethe(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    // Partition into the (single) guarded universal and quantifier-free side facts.
    let mut universal: Option<GuardedUniversal> = None;
    let mut ground: Vec<TermId> = Vec::new();
    for &a in assertions {
        if matches!(
            arena.node(a),
            TermNode::App {
                op: Op::Forall(_),
                ..
            }
        ) {
            if universal.is_some() {
                return None; // more than one universal is out of this slice
            }
            universal = Some(detect_guarded_universal(arena, a)?);
        } else {
            if contains_quantifier(arena, a) {
                return None; // an existential or buried quantifier
            }
            ground.push(a);
        }
    }
    let u = universal?;

    // Build the ground instances `inner[x:=v]` for v ∈ [lo, hi].
    let instances = build_instances(arena, &u)?;

    // The expansion (instances ∧ ground) must be genuinely integer-`unsat`; only
    // then is there a refutation to certify. Decline cleanly otherwise.
    let mut expanded: Vec<TermId> = instances.clone();
    expanded.extend_from_slice(&ground);
    if !matches!(
        check_with_lia_simplex(arena, &expanded),
        Ok(CheckResult::Unsat)
    ) {
        return None;
    }

    // 1. assume the universal as a unit clause over its opaque `forall` atom.
    let forall_atom = forall_atom_of(arena, &u)?;
    let mut commands: Vec<AletheCommand> = vec![AletheCommand::Assume {
        id: "q_forall".to_owned(),
        clause: vec![lit(forall_atom.clone(), false)],
    }];

    // 2/3. per in-range value: forall_inst_guarded lemma, then resolve against the
    //      assumed universal to the bare instance unit. Keep each instance paired
    //      with the `q_res<i>` id that proves its unit, for splicing the LIA tail.
    let mut instance_ground: Vec<(TermId, String)> = Vec::with_capacity(instances.len());
    for (i, &inst) in instances.iter().enumerate() {
        // The instance literal MUST be the same Alethe atom the lia tail emits,
        // so it key-matches when the tail's re-assumption is redirected.
        let inst_alethe = int_atom_to_alethe_pub(arena, inst)?;
        let inst_id = format!("q_inst{i}");
        let res_id = format!("q_res{i}");
        // forall_inst_guarded: (cl (not (forall (x) (=> guard inner))) inner[x:=v]).
        commands.push(AletheCommand::Step {
            id: inst_id.clone(),
            clause: vec![
                lit(forall_atom.clone(), true),
                lit(inst_alethe.clone(), false),
            ],
            rule: "forall_inst_guarded".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
        });
        // resolution with the assumed universal: (cl inner[x:=v]).
        commands.push(AletheCommand::Step {
            id: res_id.clone(),
            clause: vec![lit(inst_alethe, false)],
            rule: "resolution".to_owned(),
            premises: vec!["q_forall".to_owned(), inst_id],
            args: Vec::new(),
        });
        instance_ground.push((inst, res_id));
    }

    // 4. lia_generic ground refutation of (instances ∧ ground), spliced in: the
    //    tail re-assumes the instance units; redirect those to our q_res<i>
    //    resolvents so the instances flow from the universal, not fresh hypotheses.
    let mut tail_inputs: Vec<TermId> = instance_ground.iter().map(|&(t, _)| t).collect();
    tail_inputs.extend_from_slice(&ground);
    let tail = crate::prove_lia_unsat_alethe(arena, &tail_inputs)?;
    splice_ground_tail(&mut commands, &tail, &instance_ground, arena);

    // Self-validate with the combined (arithmetic + guarded-inst) checker.
    finish(arena, &u, commands)
}

/// Checks an Alethe proof that may use the **`forall_inst_guarded`** rule (the
/// finite-`Int` instantiation lemma) in addition to everything
/// [`crate::check_alethe_lra`] validates.
///
/// `forall_inst_guarded` is re-checked against `universal` by `guarded_inst_hook`
/// — both the structural substitution and the concrete guard truth — so the
/// instantiation step is **certified, not trusted**. Every other rule (resolution,
/// the structural CNF/EUF rules, and `lia_generic`/`la_generic`) is checked exactly
/// as in [`crate::check_alethe_lra`].
///
/// Returns `Ok(true)` only when a fully re-checked proof derives the empty clause.
///
/// # Errors
///
/// Mirrors [`axeyum_cnf::check_alethe_with`]: a missing premise, an unsupported
/// rule, or a non-entailed step.
pub fn check_alethe_lra_guarded_inst(
    universal: &GuardedUniversalForm,
    commands: &[AletheCommand],
) -> Result<bool, axeyum_cnf::AletheError> {
    let guarded = guarded_inst_hook(universal);
    // Chain: try the `forall_inst_guarded` hook first, then the arithmetic
    // (`la_generic`/`lia_generic`) checker, so one checker validates the
    // instantiation lemma AND the ground refutation.
    let hook = move |rule: &str, clause: &[AletheLit]| -> Option<bool> {
        guarded(rule, clause).or_else(|| la_generic_check_pub(rule, clause))
    };
    check_alethe_with(commands, &hook)
}

/// The closed-over data the [`check_alethe_lra_guarded_inst`] hook re-checks a
/// `forall_inst_guarded` step against: the bound-variable name, the guarded body's
/// Alethe form, the inner consequent's Alethe form, and the concrete `[lo, hi]`
/// range. Carried on the [`crate::Evidence`] so the certificate re-checks without
/// the original arena.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuardedUniversalForm {
    /// The bound integer variable's name (the `(forall (x) …)` binder).
    pub var_name: String,
    /// The inner consequent's Alethe form `⟦inner⟧` (with `x` as `Const(var_name)`).
    pub inner: AletheTerm,
    /// The guarded body's Alethe form `⟦(=> guard inner)⟧`.
    pub body: AletheTerm,
    /// The inclusive lower bound `lo`.
    pub lo: i128,
    /// The inclusive upper bound `hi`.
    pub hi: i128,
}

/// Builds the `forall_inst_guarded` checker hook closing over `universal`.
///
/// A `forall_inst_guarded` clause `(cl (not (forall (x) body)) inst)` is accepted
/// iff: literal 0 is the negated opaque `(forall (x) body)` atom over exactly this
/// binder and body; and literal 1 is `inner[x:=v]` for some **in-range** integer
/// `v ∈ [lo, hi]` — i.e. the substitution maps `x` to the integer constant `v` and
/// `v` satisfies the guard `lo<=v<=hi`. The guard truth is the arithmetic half of
/// the instantiation lemma, re-derived here from the concrete witness, so the step
/// carries no trust hole.
fn guarded_inst_hook(
    universal: &GuardedUniversalForm,
) -> impl Fn(&str, &[AletheLit]) -> Option<bool> + '_ {
    move |rule: &str, clause: &[AletheLit]| -> Option<bool> {
        if rule != "forall_inst_guarded" {
            return None;
        }
        Some(check_guarded_inst(universal, clause))
    }
}

/// Validates a `forall_inst_guarded` clause `(cl (not (forall (x) body)) inst)`.
fn check_guarded_inst(universal: &GuardedUniversalForm, clause: &[AletheLit]) -> bool {
    let [neg, pos] = clause else {
        return false;
    };
    if !neg.negated || pos.negated {
        return false;
    }
    // Literal 0 must be `(forall (x) body)` over exactly this binder and body.
    let AletheTerm::App(head, qargs) = &neg.atom else {
        return false;
    };
    if head != "forall" || qargs.len() != 2 {
        return false;
    }
    if qargs[0] != AletheTerm::Const(universal.var_name.clone()) || qargs[1] != universal.body {
        return false;
    }
    // Literal 1 must be `inner[x:=v]` for a consistent integer witness `v` that is
    // in range (the guard `lo<=v<=hi` holds).
    let mut witness: Option<AletheTerm> = None;
    if !match_substitution(
        &universal.var_name,
        &universal.inner,
        &pos.atom,
        &mut witness,
    ) {
        return false;
    }
    // No witness means `x` does not occur in `inner` — then any `v` in the
    // (non-empty) range instantiates it, and the range non-emptiness is the guard
    // satisfiability; accept (the body is `x`-independent, the instance is `inner`).
    let Some(w) = witness else {
        return universal.lo <= universal.hi;
    };
    // The witness must be an integer constant in `[lo, hi]` (the guard truth).
    let AletheTerm::Const(text) = w else {
        return false;
    };
    let Ok(v) = text.parse::<i128>() else {
        return false;
    };
    universal.lo <= v && v <= universal.hi
}

/// Structurally matches `inst` against `inner[x := ?]`, binding the witness on the
/// first occurrence of the bound variable and requiring every later occurrence to
/// map to the same term. Non-bound constants and heads must match verbatim; arities
/// must agree.
fn match_substitution(
    var_name: &str,
    inner: &AletheTerm,
    inst: &AletheTerm,
    witness: &mut Option<AletheTerm>,
) -> bool {
    match inner {
        AletheTerm::Const(c) if c == var_name => {
            if let Some(w) = witness {
                w == inst
            } else {
                *witness = Some(inst.clone());
                true
            }
        }
        AletheTerm::Const(_) => inner == inst,
        AletheTerm::App(ih, iargs) => {
            let AletheTerm::App(jh, jargs) = inst else {
                return false;
            };
            ih == jh
                && iargs.len() == jargs.len()
                && iargs
                    .iter()
                    .zip(jargs)
                    .all(|(a, b)| match_substitution(var_name, a, b, witness))
        }
        AletheTerm::Indexed {
            op: io,
            indices: ii,
            args: ia,
        } => {
            let AletheTerm::Indexed {
                op: jo,
                indices: ji,
                args: ja,
            } = inst
            else {
                return false;
            };
            io == jo
                && ii == ji
                && ia.len() == ja.len()
                && ia
                    .iter()
                    .zip(ja)
                    .all(|(a, b)| match_substitution(var_name, a, b, witness))
        }
    }
}

/// The [`GuardedUniversalForm`] for a detected universal (the data the checker
/// hook closes over and the [`crate::Evidence`] carries).
fn universal_form(arena: &TermArena, u: &GuardedUniversal) -> Option<GuardedUniversalForm> {
    Some(GuardedUniversalForm {
        var_name: arena.symbol(u.var).0.to_owned(),
        inner: int_body_to_alethe(arena, u.inner)?,
        body: forall_body_to_alethe(arena, u)?,
        lo: u.lo,
        hi: u.hi,
    })
}

/// Runs the assembled proof through [`check_alethe_lra_guarded_inst`] and returns
/// it only if it checks (`Ok(true)`, deriving the empty clause); any other outcome
/// yields `None`. The single self-validation gate.
fn finish(
    arena: &TermArena,
    u: &GuardedUniversal,
    commands: Vec<AletheCommand>,
) -> Option<Vec<AletheCommand>> {
    let form = universal_form(arena, u)?;
    match check_alethe_lra_guarded_inst(&form, &commands) {
        Ok(true) => Some(commands),
        _ => None,
    }
}

/// Detects whether `assertion` is a guarded-finite-`Int` universal
/// `∀x:Int. (lo<=x<=hi) => inner`, returning its parts. Mirrors the detection in
/// [`crate::quant_guarded_int`].
fn detect_guarded_universal(arena: &TermArena, assertion: TermId) -> Option<GuardedUniversal> {
    let TermNode::App {
        op: Op::Forall(var),
        args,
    } = arena.node(assertion)
    else {
        return None;
    };
    let var = *var;
    let body = args[0];
    if arena.symbol(var).1 != Sort::Int {
        return None;
    }
    let TermNode::App {
        op: Op::BoolImplies,
        args: imp_args,
    } = arena.node(body)
    else {
        return None;
    };
    let guard = imp_args[0];
    let inner = imp_args[1];
    if contains_quantifier(arena, body) {
        return None;
    }
    let (lo, hi) = detect_range(arena, guard, var)?;
    if lo > hi {
        return None;
    }
    let width = hi.checked_sub(lo).and_then(|d| d.checked_add(1))?;
    if width > RANGE_SIZE_CAP {
        return None;
    }
    Some(GuardedUniversal {
        var,
        guard,
        inner,
        lo,
        hi,
    })
}

/// Builds the ground inner instances `inner[x:=v]` for `v ∈ [lo, hi]`. Substituting
/// a ground `Int` constant for the (quantifier-free-body) bound variable is
/// capture-free.
fn build_instances(arena: &mut TermArena, u: &GuardedUniversal) -> Option<Vec<TermId>> {
    let var_term = arena.var(u.var);
    let mut out = Vec::new();
    let mut v = u.lo;
    loop {
        let value = arena.int_const(v);
        let mut replacements: HashMap<TermId, TermId> = HashMap::new();
        replacements.insert(var_term, value);
        let mut memo: HashMap<TermId, TermId> = HashMap::new();
        let inst = replace_subterms(arena, u.inner, &replacements, &mut memo).ok()?;
        out.push(inst);
        if v == u.hi {
            break;
        }
        v += 1;
    }
    Some(out)
}

/// The opaque Alethe `forall` atom `(forall (x) ⟦(=> guard inner)⟧)`.
fn forall_atom_of(arena: &TermArena, u: &GuardedUniversal) -> Option<AletheTerm> {
    let body = forall_body_to_alethe(arena, u)?;
    let var_name = arena.symbol(u.var).0.to_owned();
    Some(AletheTerm::App(
        "forall".to_owned(),
        vec![AletheTerm::Const(var_name), body],
    ))
}

/// The guarded body's Alethe form `⟦(=> guard inner)⟧` (with `x` free as
/// `Const(var_name)`). The inner half uses the **same** comparison translation the
/// lia tail uses ([`int_body_to_alethe`]) so an instance literal key-matches.
fn forall_body_to_alethe(arena: &TermArena, u: &GuardedUniversal) -> Option<AletheTerm> {
    let guard = int_bool_to_alethe(arena, u.guard)?;
    let inner = int_body_to_alethe(arena, u.inner)?;
    Some(AletheTerm::App("=>".to_owned(), vec![guard, inner]))
}

/// Translates an `Int`-arithmetic **Boolean** term (a comparison atom, or `and`/`or`
/// of comparisons) to Alethe. Used for the guard. `None` outside this fragment.
fn int_bool_to_alethe(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    if let TermNode::App { op, args } = arena.node(t) {
        let head = match op {
            Op::BoolAnd => "and",
            Op::BoolOr => "or",
            _ => return int_body_to_alethe(arena, t),
        };
        let mut converted = Vec::with_capacity(args.len());
        for &a in args {
            converted.push(int_bool_to_alethe(arena, a)?);
        }
        return Some(AletheTerm::App(head.to_owned(), converted));
    }
    int_body_to_alethe(arena, t)
}

/// Translates an `Int` comparison atom to its Alethe form — the **same** shape
/// [`int_atom_to_alethe_pub`] produces, so the guard's inner comparisons and the
/// instance literals share keys. `None` outside the comparison fragment.
fn int_body_to_alethe(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    int_atom_to_alethe_pub(arena, t)
}

/// Detects whether `guard` constrains `var` to a concrete closed integer range
/// `[lo, hi]`. Mirrors [`crate::quant_guarded_int`]'s detection.
fn detect_range(arena: &TermArena, guard: TermId, var: SymbolId) -> Option<(i128, i128)> {
    let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(guard)
    else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (a, b) = (args[0], args[1]);
    let bound_a = atom_bound(arena, a, var)?;
    let bound_b = atom_bound(arena, b, var)?;
    match (bound_a, bound_b) {
        (Bound::Lower(lo), Bound::Upper(hi)) | (Bound::Upper(hi), Bound::Lower(lo)) => {
            Some((lo, hi))
        }
        _ => None,
    }
}

/// One side of an integer range constraint.
enum Bound {
    /// `x >= c`.
    Lower(i128),
    /// `x <= c`.
    Upper(i128),
}

/// Interprets a single guard atom as a lower/upper bound on `var`.
fn atom_bound(arena: &TermArena, atom: TermId, var: SymbolId) -> Option<Bound> {
    let TermNode::App { op, args } = arena.node(atom) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (left, right) = (args[0], args[1]);
    let left_is_var = is_var(arena, left, var);
    let right_is_var = is_var(arena, right, var);
    let (var_on_left, other) = match (left_is_var, right_is_var) {
        (true, false) => (true, right),
        (false, true) => (false, left),
        _ => return None,
    };
    let c = int_literal(arena, other)?;
    match op {
        Op::IntLe => Some(if var_on_left {
            Bound::Upper(c)
        } else {
            Bound::Lower(c)
        }),
        Op::IntGe => Some(if var_on_left {
            Bound::Lower(c)
        } else {
            Bound::Upper(c)
        }),
        _ => None,
    }
}

/// Whether `term` is the bare bound variable `var`.
fn is_var(arena: &TermArena, term: TermId, var: SymbolId) -> bool {
    matches!(arena.node(term), TermNode::Symbol(s) if *s == var)
}

/// The literal `Int` value of `term`, if it is an integer constant.
fn int_literal(arena: &TermArena, term: TermId) -> Option<i128> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(*value),
        _ => None,
    }
}

/// Whether `term` contains any quantifier operator.
fn contains_quantifier(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::App { op, args } => {
            matches!(op, Op::Forall(_) | Op::Exists(_))
                || args.iter().any(|&a| contains_quantifier(arena, a))
        }
        _ => false,
    }
}

/// Splices the `lia_generic` ground tail onto the quantifier layer: each tail
/// command is re-emitted with its id prefixed `g_` (and premise references
/// likewise), **except** an `assume` whose unit clause is one of the derived ground
/// instances — that is dropped and any later reference redirected to the matching
/// `q_res<i>` resolvent. The ground instances thus flow from the universal
/// instantiation rather than being re-introduced as fresh hypotheses.
fn splice_ground_tail(
    commands: &mut Vec<AletheCommand>,
    tail: &[AletheCommand],
    instances: &[(TermId, String)],
    arena: &TermArena,
) {
    use std::collections::BTreeMap;
    let inst_keys: BTreeMap<String, String> = instances
        .iter()
        .filter_map(|(t, res_id)| Some((int_atom_to_alethe_pub(arena, *t)?.key(), res_id.clone())))
        .collect();
    let mut remap: BTreeMap<String, String> = BTreeMap::new();
    for cmd in tail {
        match cmd {
            AletheCommand::Assume { id, clause } => {
                if let [l] = clause.as_slice()
                    && !l.negated
                    && let Some(res_id) = inst_keys.get(&l.atom.key())
                {
                    remap.insert(id.clone(), res_id.clone());
                    continue;
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

/// Builds a positive/negative [`AletheLit`].
fn lit(atom: AletheTerm, negated: bool) -> AletheLit {
    AletheLit { atom, negated }
}

/// Detects whether `assertions` are in this certificate's slice and, if so,
/// returns the [`GuardedUniversalForm`] the [`crate::Evidence`] should carry. The
/// emitter [`prove_finite_int_quant_unsat_alethe`] and this share the detection, so
/// the evidence form matches the proof's hook exactly.
pub(crate) fn guarded_universal_form(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<GuardedUniversalForm> {
    let mut found: Option<GuardedUniversalForm> = None;
    for &a in assertions {
        if matches!(
            arena.node(a),
            TermNode::App {
                op: Op::Forall(_),
                ..
            }
        ) {
            if found.is_some() {
                return None;
            }
            let u = detect_guarded_universal(arena, a)?;
            found = Some(universal_form(arena, &u)?);
        }
    }
    found
}

/// Test-only public accessor for [`guarded_universal_form`]: lets the
/// `evidence_quant_cert` integration test re-derive the [`GuardedUniversalForm`] a
/// hand-tampered proof should be checked against. Not part of the production
/// surface (the [`crate::Evidence`] carries the form internally).
#[doc(hidden)]
#[must_use]
pub fn guarded_universal_form_for_test(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<GuardedUniversalForm> {
    guarded_universal_form(arena, assertions)
}
