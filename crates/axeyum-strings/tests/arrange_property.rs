//! The trust anchor for T-B.4a. Three families over the house LCG:
//!
//! 1. **sat soundness + decided-rate** — from a random ground assignment we
//!    build an equality/disequality set that HOLDS under it, run the search, and
//!    require every `Sat` to **replay** against the assertions (the model may
//!    differ from the witness — any replaying model is correct). We also measure
//!    and assert a conservative decided-rate floor.
//! 2. **never a wrong sat on unsat seeds** — seeds that force two distinct
//!    constants equal (directly or through a variable chain), and `x ≈ y ∧
//!    x ≠ y`, must **never** return `Sat` (only `Unknown` — word-level unsat is
//!    deferred to T-B.7).
//! 3. **determinism** — identical inputs give identical outcomes.

mod common;

use axeyum_ir::{Assignment, SymbolId, TermArena, TermId, Value, eval};
use axeyum_strings::{SearchBudget, SearchOutcome, solve_word_equations};
use common::{cat, seq_sort, unit};

/// Deterministic linear-congruential generator (the repo's house constant).
struct Lcg(u64);

impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        (self.next_u64() >> 33) % n.max(1)
    }
    fn idx(&mut self, n: usize) -> usize {
        usize::try_from(self.below(u64::try_from(n).expect("fits"))).expect("fits")
    }
    fn coin(&mut self) -> bool {
        self.next_u64() & (1 << 40) != 0
    }
}

/// A generous budget — enough to decide the short straight-line instances.
fn budget() -> SearchBudget {
    SearchBudget::new(50_000)
}

/// A char constant `seq.unit` term over the 8-bit element sort.
fn char_term(arena: &mut TermArena, byte: u8) -> TermId {
    let c = arena.bv_const(8, u128::from(byte)).expect("char const");
    unit(arena, c)
}

/// A shared term pool: 2–4 seq variables, a couple of constants, and random
/// short concatenations of them.
struct Pool {
    seq_vars: Vec<(SymbolId, TermId)>,
    terms: Vec<TermId>,
}

impl Pool {
    fn new(arena: &mut TermArena, rng: &mut Lcg) -> Self {
        let nvars = 2 + rng.idx(3); // 2..=4
        let seq_vars: Vec<(SymbolId, TermId)> = (0..nvars)
            .map(|i| {
                let s = arena
                    .declare(&format!("v{i}"), seq_sort())
                    .expect("declare seq var");
                (s, arena.var(s))
            })
            .collect();

        let a = char_term(arena, b'a');
        let b = char_term(arena, b'b');

        let mut terms: Vec<TermId> = seq_vars.iter().map(|&(_, t)| t).collect();
        terms.push(a);
        terms.push(b);
        // A few short concatenations (2 components) of the current pool.
        for _ in 0..5 {
            let l = terms[rng.idx(terms.len())];
            let r = terms[rng.idx(terms.len())];
            terms.push(cat(arena, l, r));
        }
        Self { seq_vars, terms }
    }
}

/// A random ground assignment: each seq variable is a length-0..=3 string over
/// {a, b}.
fn gen_assignment(rng: &mut Lcg, pool: &Pool) -> Assignment {
    let mut asg = Assignment::new();
    for &(s, _) in &pool.seq_vars {
        let len = rng.below(4);
        let elems = (0..len)
            .map(|_| Value::Bv {
                width: 8,
                value: u128::from(b'a') + u128::from(rng.below(2)),
            })
            .collect();
        asg.set(s, Value::Seq(elems));
    }
    asg
}

/// Model-consistent equalities: pool pairs equal under `asg` (each kept ~1/2),
/// capped at 5.
fn holding_equalities(
    arena: &TermArena,
    pool: &Pool,
    vals: &[Value],
    rng: &mut Lcg,
) -> Vec<(TermId, TermId)> {
    let mut eqs = Vec::new();
    for i in 0..pool.terms.len() {
        for j in (i + 1)..pool.terms.len() {
            if vals[i] == vals[j] && rng.coin() {
                eqs.push((pool.terms[i], pool.terms[j]));
                if eqs.len() >= 5 {
                    return eqs;
                }
            }
        }
    }
    let _ = arena;
    eqs
}

/// Model-consistent disequalities: pool pairs distinct under `asg`, at most 2.
fn holding_disequalities(pool: &Pool, vals: &[Value], rng: &mut Lcg) -> Vec<(TermId, TermId)> {
    let mut out = Vec::new();
    for i in 0..pool.terms.len() {
        for j in (i + 1)..pool.terms.len() {
            if vals[i] != vals[j] && rng.below(6) == 0 {
                out.push((pool.terms[i], pool.terms[j]));
                if out.len() >= 2 {
                    return out;
                }
            }
        }
    }
    out
}

fn replay_ok(
    arena: &TermArena,
    asg: &Assignment,
    eqs: &[(TermId, TermId)],
    diseqs: &[(TermId, TermId)],
) -> bool {
    for &(a, b) in eqs {
        match (eval(arena, a, asg), eval(arena, b, asg)) {
            (Ok(va), Ok(vb)) if va == vb => {}
            _ => return false,
        }
    }
    for &(a, b) in diseqs {
        match (eval(arena, a, asg), eval(arena, b, asg)) {
            (Ok(va), Ok(vb)) if va != vb => {}
            _ => return false,
        }
    }
    true
}

// ----- (1) sat soundness + decided rate ---------------------------------------

#[test]
fn sat_models_replay_and_decided_rate_floor() {
    let mut rng = Lcg(0x51CE_D012_3456_789A);
    let mut total = 0u64;
    let mut decided = 0u64;

    for _ in 0..3000 {
        let mut arena = TermArena::new();
        let pool = Pool::new(&mut arena, &mut rng);
        let asg = gen_assignment(&mut rng, &pool);
        let vals: Vec<Value> = pool
            .terms
            .iter()
            .map(|&t| eval(&arena, t, &asg).expect("closed pool term"))
            .collect();

        let eqs = holding_equalities(&arena, &pool, &vals, &mut rng);
        let diseqs = holding_disequalities(&pool, &vals, &mut rng);
        if eqs.len() < 2 {
            continue; // want 2..=5 equalities per the spec
        }
        total += 1;

        match solve_word_equations(&mut arena, &eqs, &diseqs, &budget()) {
            SearchOutcome::Sat(model) => {
                assert!(
                    replay_ok(&arena, &model, &eqs, &diseqs),
                    "a Sat model failed to replay: eqs={eqs:?} diseqs={diseqs:?}"
                );
                decided += 1;
            }
            SearchOutcome::Unknown { .. } => {}
        }
    }

    // Integer-percent measurement (avoid a lossy u64->f64 cast).
    let pct = decided * 100 / total.max(1);
    println!("decided {decided}/{total} = {pct}% (satisfiable instances)");
    assert!(total >= 1000, "expected >= 1000 instances, got {total}");
    // Conservative floor — the measured rate is well above this (see stdout).
    assert!(pct >= 60, "decided-rate {pct}% below the 60% floor");
}

// ----- (2) never a wrong sat on unsat seeds -----------------------------------

/// A distinct pair of single-char constant strings.
fn two_constants(arena: &mut TermArena) -> (TermId, TermId) {
    (char_term(arena, b'a'), char_term(arena, b'b'))
}

#[test]
fn constant_clash_seeds_never_sat() {
    let mut rng = Lcg(0xC1A5_4321_FEED_0000);
    let mut checked = 0u64;

    for _ in 0..1200 {
        let mut arena = TermArena::new();
        // A chain x0 = x1 = ... = xk, with the ends pinned to two distinct
        // constants — forcing "a" = "b".
        let k = 1 + rng.idx(4); // chain length 1..=4
        let vars: Vec<TermId> = (0..=k)
            .map(|i| {
                let s = arena.declare(&format!("c{i}"), seq_sort()).expect("var");
                arena.var(s)
            })
            .collect();
        let (ca, cb) = two_constants(&mut arena);

        let mut eqs: Vec<(TermId, TermId)> = Vec::new();
        for w in vars.windows(2) {
            eqs.push((w[0], w[1]));
        }
        eqs.push((vars[0], ca));
        eqs.push((*vars.last().unwrap(), cb));
        // Optional consistent noise: a fresh variable equal to itself's neighbour.
        if rng.coin() {
            let s = arena.declare("noise", seq_sort()).expect("noise");
            let n = arena.var(s);
            eqs.push((n, vars[0]));
        }

        match solve_word_equations(&mut arena, &eqs, &[], &budget()) {
            SearchOutcome::Unknown { .. } => {}
            SearchOutcome::Sat(_) => panic!("constant-clash seed returned a (wrong) Sat: {eqs:?}"),
        }
        checked += 1;
    }
    assert!(
        checked >= 1000,
        "expected >= 1000 unsat seeds, got {checked}"
    );
}

#[test]
fn equal_and_distinct_seeds_never_sat() {
    let mut rng = Lcg(0xDEAD_BEEF_0BAD_F00D);
    let mut checked = 0u64;

    for _ in 0..1200 {
        let mut arena = TermArena::new();
        let sx = arena.declare("x", seq_sort()).expect("x");
        let sy = arena.declare("y", seq_sort()).expect("y");
        let x = arena.var(sx);
        let y = arena.var(sy);

        // A chain of equalities that transitively forces x ≈ y, plus x ≠ y.
        let mut eqs = vec![(x, y)];
        if rng.coin() {
            let sz = arena.declare("z", seq_sort()).expect("z");
            let z = arena.var(sz);
            eqs = vec![(x, z), (z, y)];
        }
        // A little consistent noise concat that still holds.
        if rng.coin() {
            let xy = cat(&mut arena, x, y);
            let yx = cat(&mut arena, y, x);
            eqs.push((xy, yx)); // holds whenever x ≈ y
        }

        match solve_word_equations(&mut arena, &eqs, &[(x, y)], &budget()) {
            SearchOutcome::Unknown { .. } => {}
            SearchOutcome::Sat(_) => panic!("x≈y ∧ x≠y returned a (wrong) Sat"),
        }
        checked += 1;
    }
    assert!(checked >= 1000, "expected >= 1000 seeds, got {checked}");
}

// ----- (3) determinism --------------------------------------------------------

#[test]
fn outcomes_are_deterministic_across_runs() {
    let mut rng = Lcg(0x0D15_EA5E_1234_ABCD);
    for _ in 0..400 {
        let seed = rng.next_u64();

        let run = |seed: u64| -> (Option<Vec<(SymbolId, Value)>>, TermArena) {
            let mut arena = TermArena::new();
            let mut r = Lcg(seed);
            let pool = Pool::new(&mut arena, &mut r);
            let asg = gen_assignment(&mut r, &pool);
            let vals: Vec<Value> = pool
                .terms
                .iter()
                .map(|&t| eval(&arena, t, &asg).expect("closed"))
                .collect();
            let eqs = holding_equalities(&arena, &pool, &vals, &mut r);
            let diseqs = holding_disequalities(&pool, &vals, &mut r);
            let out = solve_word_equations(&mut arena, &eqs, &diseqs, &budget());
            let model = match out {
                SearchOutcome::Sat(m) => Some(
                    pool.seq_vars
                        .iter()
                        .map(|&(s, _)| (s, m.get(s).unwrap_or(Value::Seq(Vec::new()))))
                        .collect(),
                ),
                SearchOutcome::Unknown { .. } => None,
            };
            (model, arena)
        };

        let (m1, _) = run(seed);
        let (m2, _) = run(seed);
        assert_eq!(m1, m2, "nondeterministic outcome for seed {seed:#x}");
    }
}
