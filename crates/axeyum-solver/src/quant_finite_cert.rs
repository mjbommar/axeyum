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
//! [`check_alethe_lra_guarded_inst_against`] — the arithmetic-aware Alethe checker,
//! the `forall_inst_guarded` hook, AND the assume-independent premise verification —
//! before being returned, so a buggy build is *rejected* (`None`), never returned
//! wrong. The same checker re-validates the attached
//! [`crate::Evidence::UnsatGuardedQuantAletheProof`] in [`crate::Evidence::check`].
//!
//! The premise verification is what makes the check **independent of this emitter**:
//! every `assume` in the proof must be re-justified against the original query — the
//! quantified universal, an original assertion's rendering, a genuinely-fresh
//! Ackermann definition `c = f(t)`, or the abstracted form of an original side fact
//! (which follows from such a definition plus the original by transitivity). A proof
//! that assumes a fact *not* a consequence of the query is rejected, so the
//! certificate is verified end-to-end, not trusted from the emitter that built it.
//!
//! This slice is deliberately narrow: a **single** guarded-finite-`Int` universal
//! with a quantifier-free body whose inner is a linear-integer comparison, plus
//! quantifier-free linear-integer side assertions. Anything else declines cleanly
//! (`None`), leaving the existing bare-`unsat` behaviour untouched.

use std::collections::HashMap;

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm, check_alethe_with};
use axeyum_ir::{FuncId, Op, Sort, SymbolId, TermArena, TermId, TermNode};
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

    // Self-validate with the combined (arithmetic + guarded-inst) checker, in its
    // **assume-independent** form: every premise is re-verified against `assertions`
    // exactly as `Evidence::check` will, so emission and consumer re-check agree.
    finish(arena, &u, commands, assertions)
}

/// Emits a checkable Alethe refutation for a finite-expansion guarded-`Int`
/// universal `unsat` whose inner body **uses an uninterpreted function** over an
/// arithmetic-sorted residual — e.g. `∀x:Int. (0<=x<=1) => f(x)=0` together with
/// `f(0)=1` (the instances `f(0)=0, f(1)=0` clash with `f(0)=1`). Returns `None`
/// outside this slice (no UF in the residual, not `unsat`, or a non-arith-sorted
/// UF), leaving the bare-`unsat` behaviour untouched.
///
/// This is the UF sibling of [`prove_finite_int_quant_unsat_alethe`]: the ground
/// tail residual contains arith-sorted UF applications, so it cannot be refuted by
/// the plain `lia_generic` emitter. Instead the residual is **Ackermann-abstracted**
/// (each application `f(v)` to a fresh same-sorted symbol `v_k`, the same `unsat`
/// because identical applications share a symbol) and refuted over the pure-LIA
/// abstraction; each universal instance is then bridged from the abstraction by
/// `eq_transitive` through the abstraction's defining equation `v_k = f(v)` (a
/// conservative fresh-variable introduction, assumed as a checkable hypothesis —
/// the same trust posture as the Ackermann congruence certs). The combined proof
/// uses three rule families — `forall_inst_guarded` (the custom instantiation
/// lemma), `eq_transitive`/`symm` (the bridge), and `lia_generic` (the residual) —
/// all re-validated by [`check_alethe_lra_guarded_inst`].
///
/// The returned proof, when non-`None`, is guaranteed to pass
/// [`check_alethe_lra_guarded_inst`] and to derive the empty clause `(cl)`.
#[must_use]
pub fn prove_finite_int_quant_unsat_uf_alethe(
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
                return None;
            }
            universal = Some(detect_guarded_universal(arena, a)?);
        } else {
            if contains_quantifier(arena, a) {
                return None;
            }
            ground.push(a);
        }
    }
    let u = universal?;

    // Build the ground instances `inner[x:=v]` for v ∈ [lo, hi].
    let instances = build_instances(arena, &u)?;

    // The expanded residual `(instances ∧ ground)`.
    let mut expanded: Vec<TermId> = instances.clone();
    expanded.extend_from_slice(&ground);

    // This sibling owns the UF case: the residual MUST contain at least one
    // uninterpreted-function application, and EVERY application must be
    // arithmetic-sorted (`Int`/`Real`) so the Ackermann abstraction is pure
    // LIA/LRA. A residual with no UF is the plain-LIA path's job (decline here);
    // a non-arith-sorted application is out of slice.
    if !residual_has_arith_uf(arena, &expanded) {
        return None;
    }

    // Ackermann-abstract the residual: each application `f(v)` → fresh same-sorted
    // `v_k`. Identical applications share a symbol, so the abstraction is `unsat`
    // exactly when the residual is. The `applications()` give the `f(v) → v_k` map
    // the per-instance bridge needs.
    let elim = axeyum_rewrite::eliminate_functions(arena, &expanded).ok()?;
    if !elim.had_functions() {
        return None;
    }
    let abstraction: Vec<TermId> = elim.abstraction().to_vec();
    // Map `(func, args) → fresh symbol` for each abstracted application.
    let app_map: HashMap<(FuncId, Vec<TermId>), SymbolId> = elim
        .applications()
        .into_iter()
        .map(|(func, args, fresh)| ((func, args.to_vec()), fresh))
        .collect();

    // The abstraction must be a genuine LIA `unsat`; only then is there a residual
    // to refute. (Real residuals are out of this integer slice.)
    if !matches!(
        check_with_lia_simplex(arena, &abstraction),
        Ok(CheckResult::Unsat)
    ) {
        return None;
    }

    // For each instance `f(v)=c`, locate its abstracted symbol `v_k` and the
    // rewritten instance atom (the EXACT term the LIA tail assumes — taken from the
    // abstraction so orientation matches verbatim). An instance whose UF
    // application is not abstractable, or whose rewritten form is not the matching
    // `(= v_k c)`, is out of slice → decline.
    if abstraction.len() < instances.len() {
        return None;
    }
    let mut bridges: Vec<UfInstanceBridge> = Vec::with_capacity(instances.len());
    for (i, &inst) in instances.iter().enumerate() {
        bridges.push(uf_instance_bridge(arena, inst, abstraction[i], &app_map)?);
    }

    // 1. assume the universal as a unit clause over its opaque `forall` atom (the
    //    UF-aware body/inner rendering).
    let forall_atom = forall_atom_of_uf(arena, &u)?;
    let mut commands: Vec<AletheCommand> = vec![AletheCommand::Assume {
        id: "q_forall".to_owned(),
        clause: vec![lit(forall_atom.clone(), false)],
    }];

    // 2/3/bridge. per instance: forall_inst_guarded → resolve to the bare instance
    //     `(= (f v) c)`, assume the defining equation `(= v_k (f v))`, then
    //     `eq_transitive` to the abstracted `(= v_k c)` (keyed to splice the tail).
    let mut instance_ground: Vec<(TermId, String)> = Vec::with_capacity(instances.len());
    for (i, bridge) in bridges.iter().enumerate() {
        let final_id = emit_uf_instance(&mut commands, &forall_atom, bridge, i);
        instance_ground.push((bridge.abstract_term, final_id));
    }

    // 4. lia_generic ground refutation of the pure-LIA abstraction, spliced in: the
    //    tail re-assumes the abstracted atoms; redirect each abstracted instance's
    //    assume to our bridge resolvent so the instance flows from the universal.
    let tail = crate::prove_lia_unsat_alethe(arena, &abstraction)?;
    splice_ground_tail(&mut commands, &tail, &instance_ground, arena);

    // Self-validate with the combined checker (the UF-aware universal form), in its
    // **assume-independent** form: every premise — the universal, the fresh-var
    // abstraction definitions, and the abstracted side facts — is re-verified against
    // `assertions`, so emission and consumer re-check agree.
    finish_uf(arena, &u, commands, assertions)
}

/// Emits the per-instance command block for instance `i`: the `forall_inst_guarded`
/// step, its resolution against the assumed universal, the defining-equation
/// `Assume`, the `eq_transitive` bridge tautology, and the resolution to the
/// abstracted instance unit `(cl (= v_k c))`. Returns the id of that final unit (the
/// splice redirect target). The block proves `(= v_k c)` from the universal and the
/// (assumed, conservative) abstraction definition — no trusted reduction.
fn emit_uf_instance(
    commands: &mut Vec<AletheCommand>,
    forall_atom: &AletheTerm,
    bridge: &UfInstanceBridge,
    i: usize,
) -> String {
    let inst_id = format!("q_inst{i}");
    let res_id = format!("q_res{i}");
    let def_id = format!("q_def{i}");
    let bridge_id = format!("q_brg{i}");
    let final_id = format!("q_fin{i}");

    // forall_inst_guarded: (cl (not (forall (x) body)) (= (f v) c)).
    commands.push(AletheCommand::Step {
        id: inst_id.clone(),
        clause: vec![
            lit(forall_atom.clone(), true),
            lit(bridge.inst_atom.clone(), false),
        ],
        rule: "forall_inst_guarded".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    });
    // resolution with the assumed universal: (cl (= (f v) c)).
    commands.push(AletheCommand::Step {
        id: res_id.clone(),
        clause: vec![lit(bridge.inst_atom.clone(), false)],
        rule: "resolution".to_owned(),
        premises: vec!["q_forall".to_owned(), inst_id],
        args: Vec::new(),
    });
    // assume the defining equation `(= v_k (f v))` (a conservative fresh-var
    // introduction, the same checkable-hypothesis posture as the Ackermann
    // congruence certs).
    commands.push(AletheCommand::Assume {
        id: def_id.clone(),
        clause: vec![lit(bridge.def_atom.clone(), false)],
    });
    // eq_transitive tautology: (cl (not (= v_k (f v))) (not (= (f v) c)) (= v_k c)).
    commands.push(AletheCommand::Step {
        id: bridge_id.clone(),
        clause: vec![
            lit(bridge.def_atom.clone(), true),
            lit(bridge.inst_atom.clone(), true),
            lit(bridge.abstract_atom.clone(), false),
        ],
        rule: "eq_transitive".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    });
    // resolve the tautology against the defining-eq assume and the derived instance
    // to the abstracted unit (cl (= v_k c)).
    commands.push(AletheCommand::Step {
        id: final_id.clone(),
        clause: vec![lit(bridge.abstract_atom.clone(), false)],
        rule: "resolution".to_owned(),
        premises: vec![bridge_id, def_id, res_id],
        args: Vec::new(),
    });
    final_id
}

/// The data linking one universal instance `f(v)=c` to the LIA tail's abstracted
/// assume `v_k=c`, used to bridge the two by `eq_transitive` through the defining
/// equation `v_k = f(v)`.
struct UfInstanceBridge {
    /// The instance literal `(= (f v) c)` (the `forall_inst_guarded` consequent).
    inst_atom: AletheTerm,
    /// The abstraction's defining equation `(= v_k (f v))` (assumed).
    def_atom: AletheTerm,
    /// The abstracted instance atom `(= v_k c)` (the tail's assume key).
    abstract_atom: AletheTerm,
    /// The abstracted instance IR term `(= v_k c)` (for the splice key).
    abstract_term: TermId,
}

/// Builds the [`UfInstanceBridge`] linking one universal instance `inst` to its
/// `rewritten` abstraction `(= v_k c)` (taken verbatim from the abstraction, so the
/// orientation matches the tail's assume exactly). `None` unless `inst` is
/// `(= (f v) c)` / `(= c (f v))` for an abstractable application and `rewritten` is
/// the matching abstracted equality `(= v_k c)` / `(= c v_k)`.
fn uf_instance_bridge(
    arena: &TermArena,
    inst: TermId,
    rewritten: TermId,
    app_map: &HashMap<(FuncId, Vec<TermId>), SymbolId>,
) -> Option<UfInstanceBridge> {
    // The instance must be `(= (f v) c)` — the canonical inner-body shape with the
    // abstractable UF application `f(v)` on the LEFT and the value `c` on the right.
    // (A value-on-left instance is a sound decline; the eq_transitive bridge below
    // is built for the app-left orientation only.)
    let (app_term, value_term) = eq_operands(arena, inst)?;
    let (func, app_args) = uf_apply(arena, app_term)?;
    if uf_apply(arena, value_term).is_some() {
        return None; // both sides applications — out of this canonical slice
    }
    let fresh = *app_map.get(&(func, app_args))?;

    // The rewritten instance MUST be the abstracted equality `(= v_k c)` with `f(v)`
    // replaced by the SAME fresh symbol `v_k` in the SAME (left) position and the
    // value side unchanged. Verifying this against the abstraction's own term
    // forecloses any keying mismatch that would leave the tail's assume
    // unredirected (and thus an unjustified hypothesis).
    let (rewritten_app, rewritten_value) = eq_operands(arena, rewritten)?;
    if !matches!(arena.node(rewritten_app), TermNode::Symbol(s) if *s == fresh) {
        return None;
    }
    if rewritten_value != value_term {
        return None;
    }

    // Render the atoms. The instance keeps `(f v)`; the abstracted form and the
    // defining equation use `v_k`. The chain `v_k = (f v) = c ⊢ v_k = c` shares its
    // middle term `(f v)`.
    let app_alethe = term_to_alethe_uf(arena, app_term)?;
    let value_alethe = term_to_alethe_uf(arena, value_term)?;
    let fresh_alethe = term_to_alethe_uf(arena, rewritten_app)?;
    let inst_atom = eq_alethe(app_alethe.clone(), value_alethe.clone());
    let def_atom = eq_alethe(fresh_alethe.clone(), app_alethe);
    let abstract_atom = eq_alethe(fresh_alethe, value_alethe);

    Some(UfInstanceBridge {
        inst_atom,
        def_atom,
        abstract_atom,
        abstract_term: rewritten,
    })
}

/// The two operands of an `(= a b)` term, or `None` if `t` is not a binary
/// equality.
fn eq_operands(arena: &TermArena, t: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(t) else {
        return None;
    };
    let [a, b] = args[..] else {
        return None;
    };
    Some((a, b))
}

/// If `t` is an uninterpreted-function application `f(args)`, returns
/// `(func, args)`; otherwise `None`.
fn uf_apply(arena: &TermArena, t: TermId) -> Option<(FuncId, Vec<TermId>)> {
    match arena.node(t) {
        TermNode::App {
            op: Op::Apply(func),
            args,
        } => Some((*func, args.to_vec())),
        _ => None,
    }
}

/// Whether `residual` contains at least one uninterpreted-function application AND
/// every application is arithmetic-sorted (`Int`/`Real`). A non-arith-sorted
/// application means the abstraction would not be pure LIA/LRA — out of slice.
fn residual_has_arith_uf(arena: &TermArena, residual: &[TermId]) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = residual.to_vec();
    let mut found = false;
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            if matches!(op, Op::Apply(_)) {
                if !matches!(arena.sort_of(t), Sort::Int | Sort::Real) {
                    return false;
                }
                found = true;
            }
            stack.extend(args.iter().copied());
        }
    }
    found
}

/// Translates an IR term to Alethe for the UF-aware body fragment: integer
/// comparisons / linear terms (delegating to [`int_atom_to_alethe_pub`] where it
/// applies), plus uninterpreted applications `f(args)` rendered head-first. `None`
/// outside this fragment.
fn term_to_alethe_uf(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    match arena.node(t) {
        TermNode::Symbol(s) => {
            let (name, _sort) = arena.symbol(*s);
            Some(AletheTerm::Const(name.to_owned()))
        }
        TermNode::IntConst(n) => Some(AletheTerm::Const(n.to_string())),
        TermNode::App {
            op: Op::Apply(func),
            args,
        } => {
            let (name, _params, _result) = arena.function(*func);
            let name = name.to_owned();
            let converted = args
                .iter()
                .map(|&a| term_to_alethe_uf(arena, a))
                .collect::<Option<Vec<_>>>()?;
            Some(AletheTerm::App(name, converted))
        }
        TermNode::App { op, args } => {
            let head = match op {
                Op::IntLe => "<=",
                Op::IntLt => "<",
                Op::IntGe => ">=",
                Op::IntGt => ">",
                Op::Eq => "=",
                Op::IntAdd => "+",
                Op::IntSub | Op::IntNeg => "-",
                Op::IntMul => "*",
                _ => return None,
            };
            let converted = args
                .iter()
                .map(|&a| term_to_alethe_uf(arena, a))
                .collect::<Option<Vec<_>>>()?;
            Some(AletheTerm::App(head.to_owned(), converted))
        }
        _ => None,
    }
}

/// `(= a b)`.
fn eq_alethe(a: AletheTerm, b: AletheTerm) -> AletheTerm {
    AletheTerm::App("=".to_owned(), vec![a, b])
}

/// The opaque Alethe `forall` atom `(forall (x) ⟦(=> guard inner)⟧)` for the UF
/// case (the inner consequent is rendered UF-aware).
fn forall_atom_of_uf(arena: &TermArena, u: &GuardedUniversal) -> Option<AletheTerm> {
    let body = forall_body_to_alethe_uf(arena, u)?;
    let var_name = arena.symbol(u.var).0.to_owned();
    Some(AletheTerm::App(
        "forall".to_owned(),
        vec![AletheTerm::Const(var_name), body],
    ))
}

/// The UF-aware guarded body `⟦(=> guard inner)⟧` (the guard is pure-int, the inner
/// may use an uninterpreted application).
fn forall_body_to_alethe_uf(arena: &TermArena, u: &GuardedUniversal) -> Option<AletheTerm> {
    let guard = int_bool_to_alethe(arena, u.guard)?;
    let inner = term_to_alethe_uf(arena, u.inner)?;
    Some(AletheTerm::App("=>".to_owned(), vec![guard, inner]))
}

/// The [`GuardedUniversalForm`] for a UF-bodied detected universal (the inner /
/// body rendered UF-aware), carried on the [`crate::Evidence`].
fn universal_form_uf(arena: &TermArena, u: &GuardedUniversal) -> Option<GuardedUniversalForm> {
    Some(GuardedUniversalForm {
        var_name: arena.symbol(u.var).0.to_owned(),
        inner: term_to_alethe_uf(arena, u.inner)?,
        body: forall_body_to_alethe_uf(arena, u)?,
        lo: u.lo,
        hi: u.hi,
    })
}

/// Self-validation gate for the UF emitter: runs the assembled proof through
/// [`check_alethe_lra_guarded_inst_against`] with the UF-aware universal form and the
/// original `assertions`, returning it only on a clean re-check (`Ok(true)`, deriving
/// the empty clause AND every premise verified against the query) — so the emitted
/// proof passes the exact assume-independent check [`crate::Evidence::check`] runs.
fn finish_uf(
    arena: &TermArena,
    u: &GuardedUniversal,
    commands: Vec<AletheCommand>,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    let form = universal_form_uf(arena, u)?;
    match check_alethe_lra_guarded_inst_against(&form, &commands, arena, assertions) {
        Ok(true) => Some(commands),
        _ => None,
    }
}

/// Detects whether `assertions` are in the UF-bodied finite-`Int` quantifier slice
/// and, if so, returns the [`GuardedUniversalForm`] the [`crate::Evidence`] should
/// carry. Shared with the emitter so the evidence form matches the proof's hook.
pub(crate) fn guarded_universal_form_uf(
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
            found = Some(universal_form_uf(arena, &u)?);
        }
    }
    found
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
/// # Soundness scope
///
/// This entry point validates every *rule application* but **trusts the proof's
/// `assume` commands as given** — it cannot, without the original query, tell a
/// genuine premise from a fabricated one. Use it only where the premises are known
/// good (the emitters' own self-validation, where the proof was just built from the
/// query). Consumer re-checking of an attached
/// [`crate::Evidence::UnsatGuardedQuantAletheProof`] goes through
/// [`check_alethe_lra_guarded_inst_against`], which **also verifies every `assume`
/// against the original assertions** (the assume-independent check).
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

/// The **assume-independent** strengthening of [`check_alethe_lra_guarded_inst`]:
/// re-validates every rule application AND verifies that every `assume` command is a
/// sound premise *of the original `assertions`*, so the check no longer trusts the
/// emitter for its premises.
///
/// The carried `universal` is **also** cross-verified against the query: it must be
/// the rendering of a guarded-finite-`Int` universal that is genuinely one of the
/// original `assertions` (re-derived by the same guarded-universal detection and
/// re-rendered by the same emitter renderers). A forged `GuardedUniversalForm` not corresponding
/// to any original assertion is rejected — the check is independent of the carried
/// form as well as of the proof's `assume`s, so the certificate is verified
/// end-to-end against the original query.
///
/// On top of the rule-structure / `forall_inst_guarded` / `la_generic` checks, each
/// `assume` clause must classify as exactly one of:
///
/// 1. **the universal** — the opaque `(forall (x) body)` unit clause matching
///    `universal` (the quantified premise being instantiated);
/// 2. **an original assertion** — a unit clause `(cl φ)` whose atom is the Alethe
///    rendering (the *same* `term_to_alethe_uf` the emitters use) of one of
///    `assertions`;
/// 3. **a fresh-var definition** — `(= c (f t…))` where `c` is a `Const` whose name
///    does **not** occur (as a symbol) anywhere in `assertions`/`universal` (a
///    genuinely fresh Ackermann constant — the `!`-prefixed `eliminate_functions`
///    naming), defining it equal to an application. A fresh `c = app` is a
///    conservative definitional extension: it can never make a satisfiable query
///    unsat;
/// 4. **an abstracted original assertion** — `(= c value)` / `(= value c)` where `c`
///    is a fresh constant introduced by a class-3 definition `(= c app)` in this same
///    proof, and `(= app value)` (either orientation) is the rendering of an original
///    assertion. This is the Ackermann-abstracted form of an original ground fact:
///    it follows from the conservative definition `c = app` and the original
///    `app = value` by transitivity (the bridge the UF emitter's splice elides), so
///    it is a sound premise — re-derived here rather than trusted.
///
/// Any `assume` that classifies as none of these means the proof rests on a premise
/// that is **not** a consequence of this query, so it is not a sound refutation of
/// it: the check returns `Ok(false)`. This closes the emitter-trust gap — the
/// certificate is now verified end-to-end against the original query, independent of
/// the emitter that produced it.
///
/// # Errors
///
/// Mirrors [`axeyum_cnf::check_alethe_with`]: a missing premise, an unsupported
/// rule, or a non-entailed step.
pub fn check_alethe_lra_guarded_inst_against(
    universal: &GuardedUniversalForm,
    commands: &[AletheCommand],
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<bool, axeyum_cnf::AletheError> {
    // First: every `assume` must be a sound premise of THIS query (no emitter trust).
    if !verify_assumes_against(universal, commands, arena, assertions) {
        return Ok(false);
    }
    // Then: every rule application re-checks exactly as before.
    check_alethe_lra_guarded_inst(universal, commands)
}

/// Verifies that every `assume` in `commands` is a sound premise of `assertions`
/// (plus the quantified `universal`), classifying each against the four accepted
/// shapes documented on [`check_alethe_lra_guarded_inst_against`]. Returns `false`
/// the moment any `assume` matches none of them.
///
/// Before classifying the `assume`s, the carried `universal` itself is cross-verified
/// against the query by [`carried_universal_in_assertions`]: it must be the rendering
/// of a guarded universal that is actually one of `assertions`. This forecloses a
/// forged carried form that the class-1 `assume` test (which compares against the
/// carried form, not the query) would otherwise let through.
///
/// The original assertions are rendered with the **same** [`term_to_alethe_uf`] the
/// emitters use, so an "original assertion" premise matches syntactically (compared
/// by [`AletheTerm::key`]). The freshness test for a definition's introduced constant
/// rejects any name that occurs as a symbol in the rendered assertions or the
/// universal — only a genuinely fresh (`!`-prefixed) Ackermann constant qualifies.
fn verify_assumes_against(
    universal: &GuardedUniversalForm,
    commands: &[AletheCommand],
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    use std::collections::BTreeSet;

    // First, cross-verify the carried `universal` itself: it must be the rendering of
    // a guarded universal that is actually one of the original `assertions`. Without
    // this a forged `GuardedUniversalForm` (e.g. a different bound-variable body) would
    // be accepted by the class-1 `assume` test below, since that test compares the
    // `assume` to the carried form rather than to the query. A carried universal not
    // derived from the query cannot certify a refutation of THIS query, so reject it.
    if !carried_universal_in_assertions(universal, arena, assertions) {
        return false;
    }

    // The rendered original assertions, keyed for syntactic comparison.
    let mut assertion_keys: BTreeSet<String> = BTreeSet::new();
    // Every symbol/`Const` name occurring in the rendered assertions or the
    // universal — the "not fresh" set a definition's introduced constant must avoid.
    let mut query_consts: BTreeSet<String> = BTreeSet::new();
    collect_consts(&universal.body, &mut query_consts);
    query_consts.insert(universal.var_name.clone());
    // An original-assertion rendering that fails (outside the UF/int fragment) cannot
    // be matched against, so the corresponding `assume` will simply not classify as
    // class 2 — still sound (it falls through to rejection unless another class fits).
    let mut rendered_assertions: Vec<AletheTerm> = Vec::with_capacity(assertions.len());
    for &a in assertions {
        if let Some(rendered) = term_to_alethe_uf(arena, a) {
            collect_consts(&rendered, &mut query_consts);
            assertion_keys.insert(rendered.key());
            rendered_assertions.push(rendered);
        }
    }

    // The fresh constants introduced by accepted class-3 definitions, paired with the
    // application they were defined equal to — so a class-4 abstracted assertion can
    // bridge `c = value` through `c = app` and the original `app = value`.
    let mut definitions: Vec<(String, AletheTerm)> = Vec::new();

    for cmd in commands {
        let AletheCommand::Assume { clause, .. } = cmd else {
            continue;
        };
        let [l] = clause.as_slice() else {
            return false; // an assume must be a unit clause (every emitter shape is)
        };
        if l.negated {
            return false; // a negated assume is never one of the accepted premises
        }
        if classify_assume(
            &l.atom,
            universal,
            &assertion_keys,
            &query_consts,
            &mut definitions,
        ) {
            continue;
        }
        return false; // unclassifiable premise ⇒ not a sound refutation of THIS query
    }
    true
}

/// Verifies that the carried `universal` corresponds to a guarded-finite-`Int`
/// universal that is genuinely one of the original `assertions` — making the premise
/// verification fully assume-independent (the carried form is no longer trusted from
/// the emitter either).
///
/// For each assertion `a`, [`detect_guarded_universal`] re-derives the guarded
/// structure; when present, both renderers the emitters use are applied
/// ([`universal_form`] for the pure-`Int` body and [`universal_form_uf`] for the
/// UF-aware body — a carried form was produced by exactly one of them) and compared
/// to `universal` by `==`. The check accepts iff some assertion renders (in either
/// fragment) to exactly the carried form; otherwise the carried universal is not in
/// the query and the certificate is rejected.
fn carried_universal_in_assertions(
    universal: &GuardedUniversalForm,
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    for &a in assertions {
        let Some(u) = detect_guarded_universal(arena, a) else {
            continue;
        };
        if universal_form(arena, &u).as_ref() == Some(universal)
            || universal_form_uf(arena, &u).as_ref() == Some(universal)
        {
            return true;
        }
    }
    false
}

/// Classifies one `assume` atom against the four accepted premise shapes, recording a
/// fresh-var definition into `definitions` when it is class 3. Returns `true` iff the
/// atom is an accepted premise.
fn classify_assume(
    atom: &AletheTerm,
    universal: &GuardedUniversalForm,
    assertion_keys: &std::collections::BTreeSet<String>,
    query_consts: &std::collections::BTreeSet<String>,
    definitions: &mut Vec<(String, AletheTerm)>,
) -> bool {
    // Class 1: the universal `(forall (x) body)`.
    if let AletheTerm::App(head, qargs) = atom
        && head == "forall"
        && qargs.len() == 2
        && qargs[0] == AletheTerm::Const(universal.var_name.clone())
        && qargs[1] == universal.body
    {
        return true;
    }
    // Class 2: an original assertion's rendering.
    if assertion_keys.contains(&atom.key()) {
        return true;
    }
    // Equality-shaped premises (classes 3 and 4) inspect `(= a b)`.
    if let AletheTerm::App(head, eq_args) = atom
        && head == "="
        && let [lhs, rhs] = eq_args.as_slice()
    {
        // Class 3: a fresh-var definition `(= c (f t…))` (or `(= (f t…) c)`) — `c`
        // fresh (not in the query) and the other side an application.
        if let Some((fresh, app)) = fresh_definition(lhs, rhs, query_consts) {
            definitions.push((fresh, app));
            return true;
        }
        // Class 4: an abstracted original assertion `(= c value)` / `(= value c)` —
        // `c` introduced by a prior class-3 definition `(= c app)`, and `(= app value)`
        // (either orientation) is the rendering of an original assertion.
        if abstracted_assertion(lhs, rhs, assertion_keys, definitions)
            || abstracted_assertion(rhs, lhs, assertion_keys, definitions)
        {
            return true;
        }
    }
    false
}

/// Recognises a fresh-variable definition `(= lhs rhs)` (in either orientation): one
/// side is a `Const` whose name is **not** in `query_consts` (a genuinely fresh
/// Ackermann constant) and the other side is an application. Returns
/// `(fresh_name, application)`, or `None` if neither orientation fits.
fn fresh_definition(
    lhs: &AletheTerm,
    rhs: &AletheTerm,
    query_consts: &std::collections::BTreeSet<String>,
) -> Option<(String, AletheTerm)> {
    let is_fresh_const = |t: &AletheTerm| -> Option<String> {
        match t {
            AletheTerm::Const(name) if !query_consts.contains(name) => Some(name.clone()),
            _ => None,
        }
    };
    let is_app = |t: &AletheTerm| matches!(t, AletheTerm::App(..) | AletheTerm::Indexed { .. });
    if let Some(name) = is_fresh_const(lhs)
        && is_app(rhs)
    {
        return Some((name, rhs.clone()));
    }
    if let Some(name) = is_fresh_const(rhs)
        && is_app(lhs)
    {
        return Some((name, lhs.clone()));
    }
    None
}

/// Whether `(= fresh value)` is the abstracted form of an original assertion: `fresh`
/// is a `Const` introduced by a class-3 definition `(= fresh app)` in `definitions`,
/// and `(= app value)` (either orientation) is the rendering of an original assertion
/// (its `key` is in `assertion_keys`). When so, the assume follows from the
/// conservative definition and the original assertion by transitivity.
fn abstracted_assertion(
    fresh: &AletheTerm,
    value: &AletheTerm,
    assertion_keys: &std::collections::BTreeSet<String>,
    definitions: &[(String, AletheTerm)],
) -> bool {
    let AletheTerm::Const(name) = fresh else {
        return false;
    };
    definitions.iter().any(|(def_name, app)| {
        def_name == name
            && (assertion_keys.contains(&eq_alethe(app.clone(), value.clone()).key())
                || assertion_keys.contains(&eq_alethe(value.clone(), app.clone()).key()))
    })
}

/// Collects every `Const` name appearing anywhere in `term` into `out` (the symbols
/// the query already uses, so a definition's introduced constant can be tested for
/// genuine freshness against them).
fn collect_consts(term: &AletheTerm, out: &mut std::collections::BTreeSet<String>) {
    match term {
        AletheTerm::Const(name) => {
            out.insert(name.clone());
        }
        AletheTerm::App(_, args) | AletheTerm::Indexed { args, .. } => {
            for arg in args {
                collect_consts(arg, out);
            }
        }
    }
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

/// Runs the assembled proof through [`check_alethe_lra_guarded_inst_against`] with the
/// original `assertions` and returns it only if it checks (`Ok(true)`, deriving the
/// empty clause AND every premise verified against the query); any other outcome
/// yields `None`. The single self-validation gate — it runs the exact
/// assume-independent check [`crate::Evidence::check`] will, so emission and consumer
/// re-check agree.
fn finish(
    arena: &TermArena,
    u: &GuardedUniversal,
    commands: Vec<AletheCommand>,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    let form = universal_form(arena, u)?;
    match check_alethe_lra_guarded_inst_against(&form, &commands, arena, assertions) {
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
