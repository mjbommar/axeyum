//! Propagation-throughput benchmark for the native CDCL core on a **large,
//! bit-blasted** CNF — the shape the p4dfa corpus actually has.
//!
//! # Why this exists next to `benches/proof_sat_solve.rs`
//!
//! `proof_sat_solve_php_6_7` runs the same core on pigeonhole PHP(7,6): **42
//! variables, 133 clauses**. This lane measured what that costs (diary:
//! `docs/research/12-performance/bench-boolean-core-2026-09-07.md`). On the real
//! p4dfa corpus the native core does **1,800-11,000 propagations and
//! 2,500-29,000 watch-list visits per conflict** over 40,000-3,100,000
//! variables. On PHP(7,6) those numbers are smaller by three to four orders of
//! magnitude, and one per-conflict cost that is proportional to the *variable
//! count* — `analyze`'s `vec![false; nvars]` mark array — is 42 bytes there and
//! 3.1 MB on the largest p4dfa file. A 42-variable fixture is structurally
//! incapable of seeing it.
//!
//! This repository has the measured precedent: `cdclt_solve_php_6_7` reported
//! engine A beating engine B by 3.4% while, on a 330,000-variable real skeleton,
//! the same swap decided 4 more files at 12.9% better PAR-2 — opposite
//! directions. Pigeonhole instances are structurally unlike real CNF.
//!
//! # What this proxies, and the one axis on which it does not
//!
//! **The real workload is a `QF_BV` query bit-blasted through `axeyum-bv` and
//! Tseitin-encoded** — exactly what every p4dfa instance is, and what the
//! `dump_dimacs` path in `axeyum-bench` produces. The fixture here is built the
//! same way rather than written as DIMACS: six independent bounded-factor
//! multiplications (32-bit factors, 64-bit products, six 64-bit semiprimes),
//! bit-blasted and Tseitin-encoded.
//!
//! It is *not* a p4dfa file — those are 2-270 MB and cannot be committed. It is
//! a fixture whose measured shape sits in the p4dfa range rather than the
//! pigeonhole range. Measured 2026-09-07 on s5, against the eight-file p4dfa
//! population in the lane diary:
//!
//! | | this fixture | p4dfa range | PHP(7,6) |
//! |---|---:|---:|---:|
//! | variables | 23,997 | 31,482-3,098,002 | 42 |
//! | clauses | 100,221 | 118,228-11,377,248 | 133 |
//! | propagations / conflict | 440 | 735-11,055 | — |
//! | watch visits / conflict | 1,759 | 2,215-29,275 | — |
//! | blocking-literal miss rate | 0.418 | 0.473-0.523 | — |
//! | **resolutions / conflict** | **128** | **23-39** | — |
//!
//! Four of those five axes land in or just under the corpus range. **The fifth
//! does not, and the mismatch is recorded rather than hidden**: a factorisation
//! instance learns from far longer resolution chains than a p4dfa instance does
//! (128 antecedents per conflict against 23-39), so this fixture weights
//! `analyze` and `lit_redundant` more heavily than the corpus does, and weights
//! `propagate` correspondingly less. A change that only touches conflict
//! analysis will therefore look **better here than it will on the corpus**, and
//! a change that only touches propagation will look worse. Validate anything
//! that matters against real corpus DIMACS through
//! `examples/boolean_core_profile.rs`; that is what the diary does.
//!
//! The shape claims above are **asserted at run time**, not merely written down,
//! and the assertions have already rejected two fixtures rather than letting
//! them stand: a single 20-bit multiplier that encoded to 770 variables, and a
//! sum-of-products whose unsatisfiability is a parity argument that unit
//! propagation collapses in **2** conflicts.
//!
//! # Fixed conflict budget
//!
//! The bench solves under an explicit conflict budget rather than to a verdict,
//! and the fixture is chosen so it always exhausts it (32-bit factorisation is
//! far beyond a 2,000-conflict budget). Every sample therefore does exactly the
//! same amount of search, and two builds analyse the same conflicts along the
//! same trajectory — so the wall-time difference between them is per-conflict
//! throughput and not a difference in how much search each did. It also bounds
//! the runtime: the budget, not the instance's difficulty, decides how long a
//! sample takes (measured: 84 ms, so a default criterion run is seconds).
//!
//! Deterministic and seed-free: six declared variable pairs, one operator, six
//! constants and one budget fix the whole measurement.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;

use axeyum_bv::lower_terms;
use axeyum_cnf::{CnfFormula, VecProofSink, solve_with_drat_proof_counted, tseitin_encode};
use axeyum_ir::{Sort, TermArena};
use criterion::{Criterion, criterion_group, criterion_main};

/// Factor width, and how many independent factorisation constraints the fixture
/// conjoins.
///
/// A `w`-bit multiplier bit-blasts to roughly `w^2` AND gates and the Tseitin
/// encoder emits about two CNF variables per gate — measured, not assumed: a
/// single 20-bit multiplier gives **770** variables, which is why an earlier
/// version of this file was rejected by the shape assertion below rather than
/// quietly benchmarking a pigeonhole-sized instance. Six 32-bit factor pairs put
/// the fixture in the p4dfa variable range.
///
/// Six *independent* constraints over disjoint variables, rather than one wide
/// one, is also the closer analogue of a p4dfa query: those are packet-
/// processing decision procedures with many parallel word-level constraints, not
/// one monolithic arithmetic circuit.
const FACTOR_WIDTH: u32 = 32;
const PRODUCT_WIDTH: u32 = 64;
const CONSTRAINTS: usize = 6;

/// Conflicts per sample. Chosen so one sample is a fraction of a second: enough
/// conflicts that per-conflict costs dominate fixed call overhead, few enough
/// that criterion's default sample count fits in seconds.
const CONFLICT_BUDGET: usize = 2_000;

/// The shape a fixture must have to proxy the corpus. Both numbers come from
/// this lane's measurements on p4dfa DIMACS
/// (`docs/research/12-performance/bench-boolean-core-2026-09-07.md`): the
/// smallest file in the 2026-09-05 study population has 40,548 variables, and
/// propagations per conflict there run 735-11,055.
const MIN_CORPUS_VARIABLES: usize = 20_000;
const MIN_CORPUS_PROPAGATIONS_PER_CONFLICT: f64 = 200.0;

/// Six 64-bit semiprimes, each a product of two primes just under `2^31`, so
/// **both** factors need the full 32-bit width and the degenerate `N x 1`
/// factorisation is not representable.
///
/// Bounded-factor multiplication is the standard hard SAT fixture and is what
/// makes every sample cost the same: 32-bit factorisation is far beyond what
/// CDCL refutes or solves inside a 2,000-conflict budget, so the search runs to
/// the budget **every time** rather than being decided in however many conflicts
/// the decision heuristic happens to need. Two earlier fixtures failed exactly
/// this property and were caught by the assertion below rather than by review:
/// a satisfiable sum-of-products was decided in 52 conflicts, and an
/// unsatisfiable one whose refutation is a parity argument was decided in **2**,
/// because the low bit of a bit-blasted sum is a pure XOR chain that unit
/// propagation collapses immediately.
const SEMIPRIMES: [u128; CONSTRAINTS] = [
    2_147_483_647 * 2_147_483_629,
    2_147_483_647 * 2_147_483_587,
    2_147_483_629 * 2_147_483_587,
    2_147_483_647 * 2_147_483_579,
    2_147_483_629 * 2_147_483_563,
    2_147_483_587 * 2_147_483_563,
];

fn multiplier_formula() -> CnfFormula {
    let mut arena = TermArena::new();
    let zero = arena.bv_const(FACTOR_WIDTH, 0).unwrap();
    let mut conjuncts = Vec::with_capacity(CONSTRAINTS);
    for (i, &n) in SEMIPRIMES.iter().enumerate() {
        let a_sym = arena
            .declare(&format!("a{i}"), Sort::BitVec(FACTOR_WIDTH))
            .unwrap();
        let b_sym = arena
            .declare(&format!("b{i}"), Sort::BitVec(FACTOR_WIDTH))
            .unwrap();
        // Zero-extend both factors to the product width by concatenation, so the
        // multiplication is over 64 bits and cannot wrap.
        let a = arena.var(a_sym);
        let b = arena.var(b_sym);
        let a_wide = arena.concat(zero, a).unwrap();
        let b_wide = arena.concat(zero, b).unwrap();
        let product = arena.bv_mul(a_wide, b_wide).unwrap();
        let target = arena.bv_const(PRODUCT_WIDTH, n).unwrap();
        conjuncts.push(arena.eq(product, target).unwrap());
    }
    let lowering = lower_terms(&arena, &conjuncts).unwrap();
    let roots: Vec<_> = lowering.roots().iter().map(|r| r.bits()[0]).collect();
    let encoding = tseitin_encode(lowering.aig(), &roots).expect("fixed AIG encodes cleanly");
    encoding.formula().clone()
}

// The counters are event counts bounded by the conflict budget and the formula
// size, so every cast below is exact at the magnitudes this fixture reaches; a
// fallible conversion here would only add a branch to a println.
#[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
fn bench_proof_sat_propagate(c: &mut Criterion) {
    let formula = multiplier_formula();
    let mut sink = VecProofSink::new();
    let (_, counters) = solve_with_drat_proof_counted(&formula, None, CONFLICT_BUDGET, &mut sink);
    let propagations_per_conflict = counters.propagations as f64 / counters.conflicts.max(1) as f64;

    // The shape is printed BEFORE it is asserted, so a fixture that drifts out
    // of range reports the numbers it actually has instead of only the
    // threshold it missed.
    println!(
        "proof_sat_propagate fixture: {} variables, {} clauses; at a {CONFLICT_BUDGET}-conflict \
         budget: {} conflicts, {:.0} propagations/conflict, {:.0} watch visits/conflict, \
         {:.3} clause-deref rate, {:.1} resolutions/conflict",
        formula.variable_count(),
        formula.clauses().len(),
        counters.conflicts,
        propagations_per_conflict,
        counters.watch_visits_per_conflict(),
        counters.clause_deref_rate(),
        counters.resolutions as f64 / counters.conflicts.max(1) as f64,
    );

    // The proxy claim, asserted rather than described. This is not decoration:
    // it has already fired once, on a `WIDTH = 20` single multiplier that
    // encoded to 770 variables — a fixture that would have looked like a
    // corpus proxy in the module doc and behaved like pigeonhole in the
    // measurement.
    assert!(
        formula.variable_count() >= MIN_CORPUS_VARIABLES,
        "the fixture must be in the corpus variable range, not the pigeonhole \
         range; got {} variables (p4dfa's smallest is 40,548, PHP(7,6) is 42)",
        formula.variable_count()
    );
    assert_eq!(
        counters.conflicts as usize, CONFLICT_BUDGET,
        "the fixture must exhaust the conflict budget so that every sample does \
         the same work; it stopped after {} conflicts instead, which means the \
         parity argument above became reachable and a sample's cost is now \
         hostage to the decision heuristic",
        counters.conflicts
    );
    assert!(
        propagations_per_conflict >= MIN_CORPUS_PROPAGATIONS_PER_CONFLICT,
        "the fixture's implication chains collapsed: {propagations_per_conflict:.1} \
         propagations per conflict, against 735-11,055 measured on p4dfa. A \
         fixture with short chains cannot proxy a bit-blasted corpus instance."
    );

    c.bench_function("proof_sat_propagate_bvmul20_2k_conflicts", |b| {
        b.iter(|| {
            let mut sink = VecProofSink::new();
            let (outcome, counters) =
                solve_with_drat_proof_counted(&formula, None, CONFLICT_BUDGET, &mut sink);
            // A run that stopped early would silently make the sample cheaper
            // and the benchmark meaningless, so the work done is checked, not
            // assumed.
            assert!(
                counters.conflicts > 0,
                "a sample analysed no conflicts; the fixed-work premise is broken"
            );
            black_box((outcome, counters));
        });
    });
}

criterion_group!(benches, bench_proof_sat_propagate);
criterion_main!(benches);
