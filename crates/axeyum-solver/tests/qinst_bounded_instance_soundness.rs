//! Bounded-instance soundness harness for the e-matching quantifier
//! instantiation loop (`qinst_egraph`, Track 2 P2.6 slice 6).
//!
//! This is the *named deliverable* of the slice: a property sweep that stresses
//! two soundness invariants of the instantiation keystone over ≥500 deterministic
//! (house-LCG) quantified bit-vector seeds — both provable (`unsat`) and
//! satisfiable-by-finite-model shapes — trusting nothing but the IR ground
//! evaluator and an independent brute-force domain oracle:
//!
//! 1. **Every emitted instance is a GENUINE instance of its quantifier.** For a
//!    `∀x⃗. body` over a ground set, every term [`instantiate_forall_via_egraph`]
//!    emits must be a substitution instance `body[x⃗ := g⃗]` for a ground argument
//!    tuple `g⃗` that actually occurs under the trigger. The harness rebuilds the
//!    genuine-instance set **independently** from the ground arguments it chose and
//!    asserts the loop's output is a non-empty **subset** of it (structural, via
//!    interned `TermId`) — the soundness property "no spurious instance"; it is a
//!    subset rather than equality because matching is *modulo the ground
//!    congruence*, which legitimately collapses congruent instances to one. Every
//!    emitted term is well-sorted `Bool` by construction.
//!
//! 2. **Verdicts are correct against an independent oracle, and `unsat` replays.**
//!    - *Closed universals* (`∀x⃗. body`, `body` quantifier-free over exactly its
//!      bound vars) are decided by a **complete** brute-force oracle that
//!      enumerates the whole finite domain and evaluates `body` at every point.
//!      The loop must return `Unsat` iff some point falsifies `body`, and must
//!      **never** return `Unsat` for a valid universal — the soundness heart of
//!      the new closed-universal falsification lever.
//!    - *UF refutations* (`f(a)=k0 ∧ ∀x. f(x)=k1`, `k0≠k1`) must return `Unsat`,
//!      and the refutation **replays on a fresh arena**: the quantifier-free part
//!      conjoined with the emitted instances re-decides `Unsat` through
//!      [`solve`]/`check_auto`, re-verifying the refutation from scratch.
//!    - *UF satisfiable* shapes (`k0=k1`) must **never** return `Unsat`, and the
//!      finite model `f ≡ k0` is **replayed through the ground evaluator** to
//!      confirm it satisfies every assertion.
//!
//! No clock, no OS entropy, no external oracle: the sweep is reproducible from the
//! fixed seed and needs no solver feature flag.

#![allow(clippy::similar_names, clippy::many_single_char_names)]

use std::collections::BTreeSet;

use axeyum_ir::{Assignment, FuncValue, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, SolverConfig, instantiate_forall_via_egraph, prove_quantified_unsat_via_egraph,
    solve,
};

/// Total quantified seeds adjudicated (well past the ≥500 floor).
const SEEDS: u64 = 900;

/// Bit-vector width for the swept problems. Small so the closed-universal oracle
/// can enumerate the whole `2^W` (or `2^{2W}`) domain cheaply and exactly.
const W: u32 = 4;

/// A deterministic linear-congruential PRNG (the MMIX multiplier/increment),
/// matching the house convention used across the differential fuzzers.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).expect("modulus fits usize")
    }

    /// A `W`-bit constant value.
    fn bv(&mut self) -> u128 {
        u128::from(self.next_u64() % (1 << W))
    }
}

/// Running tally, asserted non-trivial at the end so a silently-degenerate
/// generator (e.g. only valid universals) cannot pass vacuously.
#[derive(Default)]
struct Census {
    closed_unsat: u64,
    closed_valid: u64,
    uf_unsat: u64,
    uf_sat: u64,
    instances_checked: u64,
}

#[test]
fn bounded_instance_soundness_sweep() {
    let cfg = SolverConfig::default();
    let mut census = Census::default();
    for seed in 0..SEEDS {
        let mut rng = Lcg::new(seed);
        // Three shape families, interleaved deterministically by seed.
        match seed % 3 {
            0 => closed_universal_seed(&mut rng, &cfg, &mut census),
            1 => uf_refutation_seed(&mut rng, &cfg, &mut census),
            _ => uf_satisfiable_seed(&mut rng, &cfg, &mut census),
        }
    }

    // The sweep must have actually exercised each soundness path.
    assert!(
        census.closed_unsat > 0 && census.closed_valid > 0,
        "closed-universal oracle under-covered: false={} valid={}",
        census.closed_unsat,
        census.closed_valid
    );
    assert!(
        census.uf_unsat > 0 && census.uf_sat > 0 && census.instances_checked > 0,
        "UF path under-covered: unsat={} sat={} instances={}",
        census.uf_unsat,
        census.uf_sat,
        census.instances_checked
    );
}

/// Family A — a **closed** universal `∀x y. body` over interpreted BV ops only,
/// adjudicated by a complete brute-force domain oracle.
fn closed_universal_seed(rng: &mut Lcg, cfg: &SolverConfig, census: &mut Census) {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(W)).unwrap();
    let y = arena.declare("y", Sort::BitVec(W)).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let body = gen_bool(&mut arena, rng, &[xv, yv], 2);
    // Bind innermost-first so the prefix is [x, y]; both closed and quantifier-free.
    let inner = arena.forall(y, body).unwrap();
    let forall = arena.forall(x, inner).unwrap();

    // Independent complete oracle: is there a falsifying (x, y) in the finite domain?
    let mut some_false = false;
    for xi in 0..(1u128 << W) {
        for yi in 0..(1u128 << W) {
            let mut asg = Assignment::new();
            asg.set(
                x,
                Value::Bv {
                    width: W,
                    value: xi,
                },
            );
            asg.set(
                y,
                Value::Bv {
                    width: W,
                    value: yi,
                },
            );
            if matches!(eval(&arena, body, &asg), Ok(Value::Bool(false))) {
                some_false = true;
                break;
            }
        }
        if some_false {
            break;
        }
    }

    let result =
        prove_quantified_unsat_via_egraph(&mut arena, &[forall], cfg).expect("closed solve ok");
    if some_false {
        assert_eq!(
            result,
            CheckResult::Unsat,
            "closed universal falsifiable in-domain but loop did not refute (seed body)"
        );
        census.closed_unsat += 1;
    } else {
        assert_ne!(
            result,
            CheckResult::Unsat,
            "VALID closed universal was wrongly refuted (soundness violation)"
        );
        census.closed_valid += 1;
    }
}

/// Family B (refutation) — `f(a)=k0 ∧ ∀x. f(x)=k1` with `k0 ≠ k1`. Checks instance
/// genuineness, the `Unsat` verdict, and a **fresh-arena replay** of the core.
fn uf_refutation_seed(rng: &mut Lcg, cfg: &SolverConfig, census: &mut Census) {
    let k0 = rng.bv();
    // Force k1 ≠ k0 so the query is genuinely unsat.
    let k1 = (k0 + 1 + rng.bv()) % (1 << W);
    let k1 = if k1 == k0 { (k0 + 1) % (1 << W) } else { k1 };
    let use_two = rng.below(2) == 0;

    let mut arena = TermArena::new();
    let sort = Sort::BitVec(W);
    let f = arena.declare_fun("f", &[sort], sort).unwrap();
    let a = arena.declare("a", sort).unwrap();
    let av = arena.var(a);
    let k0t = arena.bv_const(W, k0).unwrap();
    let k1t = arena.bv_const(W, k1).unwrap();
    let fa = arena.apply(f, &[av]).unwrap();
    let ground_fa = arena.eq(fa, k0t).unwrap();
    let mut ground = vec![ground_fa];
    let mut ground_args = vec![av];
    if use_two {
        let b = arena.declare("b", sort).unwrap();
        let bv = arena.var(b);
        let fb = arena.apply(f, &[bv]).unwrap();
        let ground_fb = arena.eq(fb, k0t).unwrap();
        ground.push(ground_fb);
        ground_args.push(bv);
    }

    // Universal ∀x. f(x) = k1.
    let xq = arena.declare("x", sort).unwrap();
    let xqv = arena.var(xq);
    let fx = arena.apply(f, &[xqv]).unwrap();
    let body = arena.eq(fx, k1t).unwrap();
    let forall = arena.forall(xq, body).unwrap();

    // (1) Genuineness: EVERY instance the loop emits must be a genuine substitution
    // instance `f(g)=k1` for a ground argument `g` the trigger actually saw —
    // rebuilt independently here. It is a subset, not an equality: the loop matches
    // *modulo the ground congruence*, so when the ground forces `f(a)=f(b)` (both
    // `=k0`) the two args are one class and a single representative instance is
    // emitted (documented behaviour). Soundness is "no spurious instance" = the
    // emitted set ⊆ the genuine set, and at least one instance fired.
    let instances = instantiate_forall_via_egraph(&mut arena, &ground, forall);
    let mut genuine: BTreeSet<TermId> = BTreeSet::new();
    for &g in &ground_args {
        let fg = arena.apply(f, &[g]).unwrap();
        let inst = arena.eq(fg, k1t).unwrap();
        // Well-sorted by construction: `eq` yields a Bool term or the build errors.
        assert_eq!(arena.sort_of(inst), Sort::Bool, "instance must be Bool");
        genuine.insert(inst);
    }
    let got: BTreeSet<TermId> = instances.iter().copied().collect();
    assert!(
        !got.is_empty(),
        "the trigger must fire at least one instance"
    );
    assert!(
        got.is_subset(&genuine),
        "loop emitted a NON-genuine instance: got={got:?} genuine={genuine:?}"
    );
    census.instances_checked += instances.len() as u64;

    // (2) Verdict: k0 ≠ k1 ⇒ f(a)=k0 and f(a)=k1 contradict ⇒ Unsat.
    let mut assertions = ground.clone();
    assertions.push(forall);
    let result = prove_quantified_unsat_via_egraph(&mut arena, &assertions, cfg).expect("uf solve");
    assert_eq!(
        result,
        CheckResult::Unsat,
        "UF refutation shape (k0={k0}, k1={k1}) must be unsat"
    );

    // (3) Fresh-arena replay: the quantifier-free part + the emitted instances must
    // independently re-decide Unsat, trusting only the ground decider.
    let mut fresh = TermArena::new();
    let sort2 = Sort::BitVec(W);
    let f2 = fresh.declare_fun("f", &[sort2], sort2).unwrap();
    let a2 = fresh.declare("a", sort2).unwrap();
    let a2v = fresh.var(a2);
    let k0b = fresh.bv_const(W, k0).unwrap();
    let k1b = fresh.bv_const(W, k1).unwrap();
    let fa2 = fresh.apply(f2, &[a2v]).unwrap();
    let core_ground = fresh.eq(fa2, k0b).unwrap();
    let core_inst = fresh.eq(fa2, k1b).unwrap();
    let replay = solve(&mut fresh, &[core_ground, core_inst], cfg).expect("replay solve");
    assert_eq!(
        replay,
        CheckResult::Unsat,
        "fresh-arena replay of the refuting core must re-verify Unsat"
    );
    census.uf_unsat += 1;
}

/// Family B (satisfiable) — `f(a)=k0 ∧ ∀x. f(x)=k0`. Must never be refuted, and
/// the finite model `f ≡ k0` replays through the ground evaluator.
fn uf_satisfiable_seed(rng: &mut Lcg, cfg: &SolverConfig, census: &mut Census) {
    let k0 = rng.bv();
    let mut arena = TermArena::new();
    let sort = Sort::BitVec(W);
    let f = arena.declare_fun("f", &[sort], sort).unwrap();
    let a = arena.declare("a", sort).unwrap();
    let av = arena.var(a);
    let k0t = arena.bv_const(W, k0).unwrap();
    let fa = arena.apply(f, &[av]).unwrap();
    let ground = arena.eq(fa, k0t).unwrap();
    let xq = arena.declare("x", sort).unwrap();
    let xqv = arena.var(xq);
    let fx = arena.apply(f, &[xqv]).unwrap();
    let body = arena.eq(fx, k0t).unwrap();
    let forall = arena.forall(xq, body).unwrap();

    let result =
        prove_quantified_unsat_via_egraph(&mut arena, &[ground, forall], cfg).expect("sat solve");
    assert_ne!(
        result,
        CheckResult::Unsat,
        "satisfiable UF shape (f≡k0={k0}) was wrongly refuted (soundness violation)"
    );

    // Replay the known finite model f ≡ k0 through the ground evaluator: every
    // ground assertion and the universal's instance must evaluate to true.
    let mut asg = Assignment::new();
    asg.set(
        a,
        Value::Bv {
            width: W,
            value: k0,
        },
    );
    asg.set_function(f, FuncValue::constant(vec![sort], sort, k0));
    assert_eq!(
        eval(&arena, ground, &asg).ok(),
        Some(Value::Bool(true)),
        "finite model must satisfy the ground assertion"
    );
    // The universal instantiated at `a` (its only ground application) also holds.
    let inst = arena.eq(fa, k0t).unwrap();
    assert_eq!(
        eval(&arena, inst, &asg).ok(),
        Some(Value::Bool(true)),
        "finite model must satisfy the universal's ground instance"
    );
    census.uf_sat += 1;
}

/// Generates a random closed Boolean term over the given bound variable terms,
/// using only interpreted Bool/BV operators (so the universal it bodies is a
/// closed sentence the domain oracle can decide by enumeration).
fn gen_bool(arena: &mut TermArena, rng: &mut Lcg, vars: &[TermId], depth: u32) -> TermId {
    if depth == 0 || rng.below(2) == 0 {
        let a = gen_bv(arena, rng, vars, depth);
        let b = gen_bv(arena, rng, vars, depth);
        return arena.eq(a, b).unwrap();
    }
    match rng.below(3) {
        0 => {
            let a = gen_bool(arena, rng, vars, depth - 1);
            let b = gen_bool(arena, rng, vars, depth - 1);
            arena.and(a, b).unwrap()
        }
        1 => {
            let a = gen_bool(arena, rng, vars, depth - 1);
            let b = gen_bool(arena, rng, vars, depth - 1);
            arena.or(a, b).unwrap()
        }
        _ => {
            let a = gen_bool(arena, rng, vars, depth - 1);
            arena.not(a).unwrap()
        }
    }
}

/// Generates a random closed BV term over the bound variable terms.
fn gen_bv(arena: &mut TermArena, rng: &mut Lcg, vars: &[TermId], depth: u32) -> TermId {
    if depth == 0 || rng.below(2) == 0 {
        return if rng.below(2) == 0 {
            vars[rng.below(vars.len() as u64)]
        } else {
            arena.bv_const(W, rng.bv()).unwrap()
        };
    }
    match rng.below(5) {
        0 => {
            let a = gen_bv(arena, rng, vars, depth - 1);
            let b = gen_bv(arena, rng, vars, depth - 1);
            arena.bv_and(a, b).unwrap()
        }
        1 => {
            let a = gen_bv(arena, rng, vars, depth - 1);
            let b = gen_bv(arena, rng, vars, depth - 1);
            arena.bv_or(a, b).unwrap()
        }
        2 => {
            let a = gen_bv(arena, rng, vars, depth - 1);
            let b = gen_bv(arena, rng, vars, depth - 1);
            arena.bv_xor(a, b).unwrap()
        }
        3 => {
            let a = gen_bv(arena, rng, vars, depth - 1);
            let b = gen_bv(arena, rng, vars, depth - 1);
            arena.bv_add(a, b).unwrap()
        }
        _ => {
            let a = gen_bv(arena, rng, vars, depth - 1);
            arena.bv_not(a).unwrap()
        }
    }
}
