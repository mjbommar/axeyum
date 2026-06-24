//! Roadmap-aligned **progress-frontier** regression suite (oracle-free).
//!
//! This is the missing *frontier* counterpart to the soundness-only corpus gate
//! ([`corpus_regression.rs`](./corpus_regression.rs)). Where that gate asks "did
//! we ever return a wrong verdict?", this one asks "**how far** can axeyum push
//! a parametric family before it runs out of room?" — and pins that reach as a
//! committed baseline so a roadmap lever improving raises a visible number and a
//! regression lowers it past the floor (a hard test failure).
//!
//! # The frontier metric
//!
//! Each benchmark *family* has a difficulty knob `N = 1, 2, 3, …`. As `N` grows
//! the instance gets harder until axeyum times out / returns `unknown`. The
//! **frontier** is the largest `N` axeyum *decides* (sat/unsat) **and** whose
//! self-check confirms that verdict is correct, within a fixed per-instance
//! budget. It is one integer per family that **rises** when the underlying
//! lever improves. We commit `BASELINE_<family>` = the measured current
//! frontier; the test asserts `frontier >= baseline` and prints the live value
//! plus a `PROGRESS` flag when it exceeds the floor.
//!
//! # Oracle-free / self-checking — soundness is the contract
//!
//! Every instance carries its own ground truth, established **independently** of
//! the bit-blast-to-SAT search path (the same discipline as `axeyum-scenarios`,
//! ADR-0008):
//!
//! - **SAT** instances carry a concrete witness. The witness is verified by
//!   evaluating the query terms against it (via [`axeyum_scenarios::Scenario`]'s
//!   evaluator-only `self_check`, or — for the string family — by evaluating the
//!   string-theory constraints against the concrete witness string in plain
//!   Rust). A family that builds a *bad* witness fails its own self-check before
//!   the solver is ever consulted.
//! - **UNSAT** instances are the negation of a true-by-construction identity,
//!   refuted by exhaustive enumeration over the (small) finite domain — a
//!   genuine proof of UNSAT, not an oracle's say-so.
//!
//! A *decided-but-wrong* verdict (the solver's answer contradicts the
//! self-checked ground truth) is a **hard test failure** — this is the
//! soundness guard. We never trust an unverified decided result.
//!
//! # The three families and their levers
//!
//! | family          | knob `N` scales …                                  | roadmap lever                                                  |
//! |-----------------|----------------------------------------------------|----------------------------------------------------------------|
//! | `bv_reduction`  | depth of a constant-folding multiplier tower       | `QF_BV` **word-level reduction** (`preprocess`, ADR-0037)     |
//! | `lia_cuts`      | size/coupling of an integer-linear system          | `QF_LIA` **branch-and-bound** (the bounded integer engine)    |
//! | `string_bound`  | required string length                             | **bounded-string** `STRING_MAX_LEN` (currently 8, ADR-0029)   |
//!
//! Each family's fall-off is *attributable to its lever*: `bv_reduction` decides
//! far past where the same instances fall off with `preprocess` **disabled**
//! (proving reduction is doing the work — see `bv_reduction_falloff_is_the_lever`);
//! `string_bound` falls off exactly at the packed-string bound. When a lever
//! deepens, the corresponding baseline can be bumped — gradual progress, made
//! visible and attributable.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value};
use axeyum_query::Query;
use axeyum_scenarios::{Expectation, Family, Scenario, UnsatEvidence};
use axeyum_solver::{CheckResult, SolverConfig, SolverError, check_auto, solve_smtlib};

/// Per-instance solve budget. Modest so the whole sweep finishes in a couple of
/// minutes under `scripts/mem-run.sh`; large enough that the frontier reflects
/// real solving power, not a too-tight clock.
const BUDGET: Duration = Duration::from_secs(4);

/// How far past the frontier we keep sweeping, to log the shape of the fall-off
/// (decided → undecided) rather than stopping the instant we hit the wall.
const OVERSHOOT: u32 = 3;

// ---------------------------------------------------------------------------
// Committed baselines — the measured current frontier per family.
//
// These were measured by running this very suite (`-- --nocapture`) and reading
// the `FRONTIER` lines. The test asserts `frontier >= baseline`, so improving a
// lever shows up as a `PROGRESS` line and lets the baseline be bumped; a
// regression drops the frontier below the floor and fails the gate.
// ---------------------------------------------------------------------------

/// `bv_reduction`: largest `N` whose `N²`-multiplier tower reduction collapses
/// and decides UNSAT within budget. Measured frontier ≈ 33; the committed floor
/// is set below it with margin for timing noise near the knee. Rises when
/// word-level reduction deepens (collapses more multipliers per unit budget).
const BASELINE_BV_REDUCTION: u32 = 28;

/// `lia_cuts`: largest integer-linear system size decided (SAT, witness-checked)
/// under the bounded integer engine. Measured frontier ≈ 26; floor set below it
/// with margin (branch-and-bound runtime near the knee is noisy). Rises as the
/// LIA engine deepens.
const BASELINE_LIA_CUTS: u32 = 20;

/// `string_bound`: largest required string length decided before the
/// packed-string bound (`STRING_MAX_LEN`, currently 8) cuts it off. The fall-off
/// is deterministic (a hard packing bound, not a timing edge), so the floor sits
/// exactly at the measured frontier. Rises when the bound is raised.
const BASELINE_STRING_BOUND: u32 = 8;

/// The largest `N` any family is ever swept to (a hard ceiling so a regression
/// that suddenly decides "everything" can't run forever).
const MAX_N: u32 = 40;

// ---------------------------------------------------------------------------
// One point on a family's difficulty curve.
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct CurvePoint {
    n: u32,
    /// `true` iff the solver returned sat/unsat *and* the self-check confirmed
    /// that verdict is the correct one.
    decided_correct: bool,
    /// `"sat"`, `"unsat"`, `"unknown"`, `"timeout"`, or `"error"`.
    status: &'static str,
    solve_ms: f64,
}

/// A built, already-self-checked instance ready to hand to the solver, plus the
/// independent verdict its self-check established.
struct Instance {
    arena: TermArena,
    assertions: Vec<TermId>,
    /// `true` if the ground truth is SAT, `false` if UNSAT.
    expect_sat: bool,
}

/// Outcome of solving one instance under [`BUDGET`].
struct Solved {
    decided_correct: bool,
    status: &'static str,
    solve_ms: f64,
}

/// Run `check_auto` on a worker thread under [`BUDGET`]; degrade to a sound
/// timeout on overrun.
///
/// A generous stack mirrors `corpus_regression.rs` — deep bit-blasting can
/// recurse — and the wall-clock cap means a hard instance degrades to a sound
/// timeout (`unknown`), never a hang/OOM.
fn solve_capped(mut instance: Instance, config: SolverConfig) -> Solved {
    let expect_sat = instance.expect_sat;
    let (tx, rx) = mpsc::channel();
    let t0 = Instant::now();
    thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let res = check_auto(&mut instance.arena, &instance.assertions, &config);
            let _ = tx.send(res);
        })
        .expect("spawn solver thread");

    // Give the thread the budget plus a small margin to deliver its own
    // timeout-driven `unknown` before we declare a hard overrun.
    let outcome = rx.recv_timeout(BUDGET + Duration::from_secs(1));
    let solve_ms = t0.elapsed().as_secs_f64() * 1000.0;

    classify(&outcome, expect_sat, solve_ms)
}

fn classify(
    outcome: &Result<Result<CheckResult, SolverError>, mpsc::RecvTimeoutError>,
    expect_sat: bool,
    solve_ms: f64,
) -> Solved {
    match outcome {
        Ok(Ok(CheckResult::Sat(_))) => Solved {
            // Decided sat: correct iff ground truth is sat. A sat against a
            // self-checked UNSAT ground truth is a soundness failure (caught in
            // `sweep`).
            decided_correct: expect_sat,
            status: "sat",
            solve_ms,
        },
        Ok(Ok(CheckResult::Unsat)) => Solved {
            decided_correct: !expect_sat,
            status: "unsat",
            solve_ms,
        },
        Ok(Ok(CheckResult::Unknown(_))) => Solved {
            decided_correct: false,
            status: "unknown",
            solve_ms,
        },
        Ok(Err(_)) => Solved {
            decided_correct: false,
            status: "error",
            solve_ms,
        },
        Err(_) => Solved {
            decided_correct: false,
            status: "timeout",
            solve_ms,
        },
    }
}

// ---------------------------------------------------------------------------
// The frontier sweep.
// ---------------------------------------------------------------------------

/// Sweep `N = 1..` building + self-checking each instance, solving under
/// `config`, and recording the curve. The **frontier** is the largest `N` that
/// is decided *and* self-check-confirmed correct with no undecided `N` below it;
/// we keep sweeping [`OVERSHOOT`] points past the first miss to log the shape of
/// the fall-off.
///
/// `build` returns `None` once a family can no longer construct an instance,
/// which ends the sweep cleanly.
///
/// A **decided-but-wrong** verdict aborts with a panic — that is the soundness
/// guard, and it is intentionally not recoverable.
fn sweep(
    family: &str,
    config: &SolverConfig,
    mut build: impl FnMut(u32) -> Option<Instance>,
) -> (u32, Vec<CurvePoint>) {
    let mut curve = Vec::new();
    let mut frontier = 0u32;
    let mut consecutive_undecided = 0u32;

    for n in 1..=MAX_N {
        let Some(instance) = build(n) else {
            break;
        };
        let expect_sat = instance.expect_sat;
        let solved = solve_capped(instance, config.clone());

        // Soundness: a *wrong* decided verdict is never tolerated.
        let wrong_verdict = matches!(solved.status, "sat" | "unsat") && !solved.decided_correct;
        assert!(
            !wrong_verdict,
            "SOUNDNESS FAILURE [{family} N={n}]: solver said {} but the self-checked \
             ground truth is {}",
            solved.status,
            if expect_sat { "sat" } else { "unsat" },
        );

        if solved.decided_correct {
            // Only extend the frontier while the curve is still unbroken.
            if consecutive_undecided == 0 {
                frontier = n;
            }
        } else {
            consecutive_undecided += 1;
        }

        curve.push(CurvePoint {
            n,
            decided_correct: solved.decided_correct,
            status: solved.status,
            solve_ms: solved.solve_ms,
        });

        if consecutive_undecided > OVERSHOOT {
            break;
        }
    }

    (frontier, curve)
}

/// Print the curve and the headline `FRONTIER` line, write the JSON artifact,
/// and assert the regression floor.
fn report_and_assert(family: &str, baseline: u32, frontier: u32, curve: &[CurvePoint]) {
    eprintln!("--- frontier curve: {family} ---");
    eprintln!(
        "{:>4}  {:>9}  {:>9}  {:>10}",
        "N", "decided", "status", "solve_ms"
    );
    for p in curve {
        eprintln!(
            "{:>4}  {:>9}  {:>9}  {:>10.1}",
            p.n,
            if p.decided_correct { "yes" } else { "no" },
            p.status,
            p.solve_ms,
        );
    }
    let progress = if frontier > baseline {
        format!(", PROGRESS (+{} over baseline)", frontier - baseline)
    } else {
        String::new()
    };
    eprintln!("FRONTIER {family} = {frontier} (baseline {baseline}){progress}");

    write_curve_json(family, baseline, frontier, curve);

    assert!(
        frontier >= baseline,
        "REGRESSION [{family}]: frontier {frontier} < committed baseline {baseline} — a \
         roadmap lever lost ground. (Lowering the baseline is only correct if the loss is \
         understood and accepted.)",
    );
}

/// `bench-results/frontier/<family>.json`. Hand-rolled (no `serde_json` dep in
/// the solver test crate) — the schema is tiny and stable.
fn write_curve_json(family: &str, baseline: u32, frontier: u32, curve: &[CurvePoint]) {
    let dir = artifact_dir();
    if let Err(error) = std::fs::create_dir_all(&dir) {
        eprintln!("warn: could not create {}: {error}", dir.display());
        return;
    }
    let mut json = String::new();
    json.push_str("{\n");
    let _ = writeln!(json, "  \"family\": \"{family}\",");
    let _ = writeln!(json, "  \"baseline\": {baseline},");
    let _ = writeln!(json, "  \"frontier\": {frontier},");
    let _ = writeln!(json, "  \"budget_ms\": {},", BUDGET.as_millis());
    json.push_str("  \"curve\": [\n");
    for (i, p) in curve.iter().enumerate() {
        let comma = if i + 1 < curve.len() { "," } else { "" };
        let _ = writeln!(
            json,
            "    {{ \"n\": {}, \"decided\": {}, \"status\": \"{}\", \"solve_ms\": {:.1} }}{comma}",
            p.n, p.decided_correct, p.status, p.solve_ms,
        );
    }
    json.push_str("  ]\n}\n");

    let path = dir.join(format!("{family}.json"));
    if let Err(error) = std::fs::write(&path, json) {
        eprintln!("warn: could not write {}: {error}", path.display());
    }
}

fn artifact_dir() -> PathBuf {
    // Tests run with CWD = crate dir (crates/axeyum-solver); artifacts live at
    // the workspace root under bench-results/.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../bench-results/frontier")
}

// ===========================================================================
// Family 1: bv_reduction — lever: QF_BV word-level reduction (`preprocess`).
// ===========================================================================
//
// Instance `N` asserts the negation of a true-by-construction bit-vector
// identity whose left-hand side is a depth-`N` *constant-folding* tower of
// **multiplications**: `(((x * a1) * a2) … * aN) = x * A`, where
// `A = (a1·a2·…·aN) mod 2^width`. After word-level reduction (constant
// propagation + canonicalization, on by default in `check_auto`) the chain of
// constant multipliers folds to a single `x * A`, making the negation trivially
// UNSAT. Without reduction, the same instance bit-blasts **all `N` width-`width`
// multipliers** (each ~`width²` gates) into an AIG/CNF that, as `N` grows, blows
// the encoding budget and degrades to `unknown` — so the frontier is *the
// reduction's reach* (proven by `bv_reduction_falloff_is_the_lever`).
//
// Self-check: UNSAT by exhaustive enumeration over the single `width`-bit symbol
// `x` (an honest finite-domain proof — `2^width` cases). Multipliers (not
// adders) are the knob: an adder bit-blasts small even un-reduced, so it would
// not isolate the lever; a multiplier tower does.

const BV_REDUCTION_WIDTH: u32 = 8;

/// The multiplier-tower depth for `bv_reduction` instance `N`: quadratic, so the
/// bit-blast work grows fast enough to reach a real fall-off within the sweep.
fn bv_reduction_depth(n: u32) -> u32 {
    n * n
}

/// Build the `bv_reduction` instance of depth `N` as a self-checking
/// [`Scenario`] (UNSAT, exhaustively verified), then unwrap it to an
/// [`Instance`].
///
/// Returns `Option` to satisfy the [`sweep`] builder contract (other families
/// can stop building early); this family always constructs an instance.
#[allow(clippy::unnecessary_wraps)]
fn bv_reduction_instance(n: u32) -> Option<Instance> {
    let scenario = bv_reduction_scenario(n);
    scenario
        .self_check()
        .unwrap_or_else(|e| panic!("bv_reduction N={n} failed self-check: {e}"));
    Some(scenario_to_instance(&scenario))
}

fn bv_reduction_scenario(n: u32) -> Scenario {
    let width = BV_REDUCTION_WIDTH;
    let mask = (1u128 << width) - 1;
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);

    // Tower of constant multipliers: acc = (((x * a1) * a2) … * aD), tracking the
    // folded product A = (a1·a2·…·aD) mod 2^width. The constants are odd (so they
    // never collapse the product to 0 and the chain stays a genuine multiplier
    // structure un-reduced).
    //
    // The tower DEPTH grows *quadratically* in `N` (`depth = N²`): reduction must
    // collapse all `N²` width-`width` multipliers (each ~`width²` gates) before
    // the bit-blast fits the budget, so a real (non-ceiling) fall-off lands within
    // a bounded sweep, and the frontier measures the *reach of the collapse*.
    let depth = bv_reduction_depth(n);
    let mut acc = x;
    let mut product: u128 = 1;
    for k in 1..=depth {
        // Odd constants in 3, 5, 7, … (cycled into range).
        let a = ((u128::from(k) * 2 + 1) & mask) | 1;
        let c = arena.bv_const(width, a).unwrap();
        acc = arena.bv_mul(acc, c).unwrap();
        product = (product * a) & mask;
    }
    // Right-hand side: the single folded multiplier `x * A`.
    let a_const = arena.bv_const(width, product).unwrap();
    let folded = arena.bv_mul(x, a_const).unwrap();

    // Assert the *negation* of `acc == x * A`. The identity holds for every `x`,
    // so the negation is UNSAT.
    let eq = arena.eq(acc, folded).unwrap();
    let neq = arena.not(eq).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(neq).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("bv_reduction/n{n}_depth{depth}"),
        family: Family::Identity,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            // `self_check` recomputes the exhaustive evidence; this is a
            // placeholder of the right variant.
            evidence: UnsatEvidence::Exhaustive { cases: 0 },
        },
    }
}

// ===========================================================================
// Family 2: lia_cuts — lever: QF_LIA bounded integer engine (branch-and-bound).
// ===========================================================================
//
// Instance `N` is a satisfiable integer-linear system over `N` variables whose
// in-box integer solution is pinned by a tower of mutually-constraining boxes,
// strict orderings, and one scaled-sum cut — the kind of system that needs
// progressively deeper branch-and-bound to land on the integer witness as `N`
// (and the coefficients) grow. We keep it SAT and witness-checkable: the witness
// is chosen first and every constraint asserted to hold for it, so the
// self-check is purely the evaluator confirming the witness (UNSAT over
// `Sort::Int` has no finite enumeration, so we deliberately stay
// witness-checkable — fully oracle-free).
//
// The difficulty knob is `N` = the number of coupled variables (and the growth
// of the coefficients `a_i`), which deepens the search needed to find the model.

/// Returns `Option` for the [`sweep`] builder contract; this family always
/// constructs an instance.
#[allow(clippy::unnecessary_wraps)]
fn lia_cuts_instance(n: u32) -> Option<Instance> {
    let scenario = lia_cuts_scenario(n);
    scenario
        .self_check()
        .unwrap_or_else(|e| panic!("lia_cuts N={n} failed self-check: {e}"));
    Some(scenario_to_instance(&scenario))
}

fn lia_cuts_scenario(n: u32) -> Scenario {
    let count = n as usize; // `n <= MAX_N`, no truncation
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    // Each variable lives in a WIDE box whose half-width grows with `N`, so the
    // integer feasible region (and therefore the branch-and-bound search) expands
    // with the knob — the tight scaled-sum cut then pins a single integer corner
    // the engine must *find* inside that growing box.
    let half = i128::from(2 * n + 4); // box half-width grows with N
    let mut vars = Vec::with_capacity(count);
    let mut witness_vals = Vec::with_capacity(count);
    for i in 0..count {
        let sym = arena.declare(&format!("x{i}"), Sort::Int).unwrap();
        // Witness sits off-center in its box so the corner is non-obvious.
        let val = 1 + i128::try_from(i).unwrap() * 3;
        witness.set(sym, Value::Int(val));
        vars.push(arena.var(sym));
        witness_vals.push(val);
    }

    let mut goals = Vec::new();

    // Wide box: witness - half <= x_i <= witness + half. The region grows with N.
    for (i, &val) in witness_vals.iter().enumerate() {
        let lo = arena.int_const(val - half);
        let hi = arena.int_const(val + half);
        goals.push(arena.int_ge(vars[i], lo).unwrap());
        goals.push(arena.int_le(vars[i], hi).unwrap());
    }

    // Strict ordering x0 < x1 < … < x_{n-1} (consistent with the witness),
    // coupling the boxes so the search must respect a chain of inequalities.
    for i in 0..count.saturating_sub(1) {
        goals.push(arena.int_lt(vars[i], vars[i + 1]).unwrap());
    }

    // Two tight scaled-sum cuts with growing, coprime-ish coefficients — they
    // intersect the wide boxes in a thin lattice the engine must branch to hit.
    // Both pinned to the witness so the system is SAT by construction.
    for base in [2i128, 3i128] {
        let mut acc: Option<TermId> = None;
        let mut sum_val: i128 = 0;
        for (i, &val) in witness_vals.iter().enumerate() {
            // Coefficient grows with the position `i` and the cut's `base`.
            let coeff = base + i128::try_from(i).unwrap() * (base + 1);
            sum_val += coeff * val;
            let c = arena.int_const(coeff);
            let term = arena.int_mul(c, vars[i]).unwrap();
            acc = Some(match acc {
                None => term,
                Some(prev) => arena.int_add(prev, term).unwrap(),
            });
        }
        let lhs = acc.unwrap();
        let rhs = arena.int_const(sum_val);
        goals.push(arena.eq(lhs, rhs).unwrap());
    }

    let mut builder = Query::builder(&arena);
    for g in goals {
        builder.assert(g).unwrap();
    }
    let query = builder.build();

    Scenario {
        name: format!("lia_cuts/system_n{n}"),
        family: Family::Integer,
        width: 0,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

// ===========================================================================
// Family 3: string_bound — lever: bounded-string STRING_MAX_LEN (ADR-0029).
// ===========================================================================
//
// Instance `N` requires a string `s` of length exactly `N` that contains a
// fixed substring — `(str.len s) = N ∧ (str.contains s "ab")`. A concrete
// witness string of length `N` (containing "ab") satisfies it by construction.
// The packed-string model caps `max_len` at `STRING_MAX_LEN` (8), so once `N`
// exceeds the bound the instance can no longer be packed and axeyum degrades to
// `unknown` — the frontier is the bound's reach. Raise the bound ⇒ frontier
// rises.
//
// Self-check: the witness is verified in plain Rust against the *string-theory*
// semantics of the constraints (length and substring containment) — an
// independent check that never touches the solver's packed-BV model. SAT is the
// claim, so a wrong `unsat` from axeyum is caught (a witness provably exists).

/// The fixed substring every `string_bound` witness must contain.
const STRING_NEEDLE: &str = "ab";

fn string_bound_witness(n: u32) -> String {
    // A length-`N` string that contains "ab": "ab" padded with 'c' up to length
    // N. The sweep starts at N = 2 (the needle length).
    let mut s = String::from(STRING_NEEDLE);
    while u32::try_from(s.len()).unwrap_or(u32::MAX) < n {
        s.push('c');
    }
    s
}

/// Independently verify the witness against the string-theory constraints — no
/// solver involved. Returns `true` iff the concrete string satisfies
/// `len == n ∧ contains needle`.
fn string_bound_self_check(witness: &str, n: u32) -> bool {
    u32::try_from(witness.len()).is_ok_and(|len| len == n) && witness.contains(STRING_NEEDLE)
}

fn string_bound_smtlib(n: u32) -> String {
    format!(
        "(set-logic QF_S)\n\
         (declare-const s String)\n\
         (assert (= (str.len s) {n}))\n\
         (assert (str.contains s \"{STRING_NEEDLE}\"))\n\
         (check-sat)\n"
    )
}

/// Solve one `string_bound` instance end-to-end (it bypasses the generic
/// [`sweep`] because its solve path is `solve_smtlib`, not `check_auto`).
fn string_bound_point(n: u32, config: &SolverConfig) -> CurvePoint {
    let witness = string_bound_witness(n);
    assert!(
        string_bound_self_check(&witness, n),
        "string_bound N={n}: constructed witness {witness:?} fails its own self-check",
    );

    let text = string_bound_smtlib(n);
    let cfg = config.clone();
    let (tx, rx) = mpsc::channel();
    let t0 = Instant::now();
    thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let res = solve_smtlib(&text, &cfg).map(|o| o.result);
            let _ = tx.send(res);
        })
        .expect("spawn string solver thread");
    let outcome = rx.recv_timeout(BUDGET + Duration::from_secs(1));
    let solve_ms = t0.elapsed().as_secs_f64() * 1000.0;

    // Ground truth is SAT (a witness provably exists). A wrong `unsat` is a hard
    // failure; `unknown` past the bound is the expected benign fall-off.
    let (decided_correct, status) = match outcome {
        Ok(Ok(CheckResult::Sat(_))) => (true, "sat"),
        Ok(Ok(CheckResult::Unsat)) => {
            panic!(
                "SOUNDNESS FAILURE [string_bound N={n}]: solver said unsat but witness \
                 {witness:?} (len {n}, contains {STRING_NEEDLE:?}) provably satisfies it",
            );
        }
        Ok(Ok(CheckResult::Unknown(_))) => (false, "unknown"),
        Ok(Err(_)) => (false, "error"),
        Err(_) => (false, "timeout"),
    };

    CurvePoint {
        n,
        decided_correct,
        status,
        solve_ms,
    }
}

// ---------------------------------------------------------------------------
// Shared helpers.
// ---------------------------------------------------------------------------

/// Flatten a self-checked [`Scenario`] into an [`Instance`] for the solver. The
/// arena is cloned (cheap interned IDs) so the scenario's own copy stays intact.
fn scenario_to_instance(scenario: &Scenario) -> Instance {
    Instance {
        arena: scenario.arena.clone(),
        assertions: scenario.query.solver_terms().collect(),
        expect_sat: scenario.expectation.is_sat(),
    }
}

// ===========================================================================
// Tests.
// ===========================================================================

#[test]
fn frontier_bv_reduction() {
    let config = SolverConfig::new().with_timeout(BUDGET);
    let (frontier, curve) = sweep("bv_reduction", &config, bv_reduction_instance);
    report_and_assert("bv_reduction", BASELINE_BV_REDUCTION, frontier, &curve);
}

#[test]
fn frontier_lia_cuts() {
    let config = SolverConfig::new().with_timeout(BUDGET);
    let (frontier, curve) = sweep("lia_cuts", &config, lia_cuts_instance);
    report_and_assert("lia_cuts", BASELINE_LIA_CUTS, frontier, &curve);
}

#[test]
fn frontier_string_bound() {
    let config = SolverConfig::new().with_timeout(BUDGET);
    let mut curve = Vec::new();
    let mut frontier = 0u32;
    let mut consecutive_undecided = 0u32;

    // Strings start at length 2 (the needle is "ab"); the frontier is reported in
    // the same units as N (so a length-`L` string is point N=L).
    for n in 2..=MAX_N {
        let point = string_bound_point(n, &config);
        if point.decided_correct {
            if consecutive_undecided == 0 {
                frontier = n;
            }
        } else {
            consecutive_undecided += 1;
        }
        curve.push(point);
        if consecutive_undecided > OVERSHOOT {
            break;
        }
    }

    report_and_assert("string_bound", BASELINE_STRING_BOUND, frontier, &curve);
}

/// Soundness: the curves are built from self-checking instances. This test
/// re-verifies a sample of each generator independently of the solver — a
/// corrupted generator (one that builds a witness/identity that does not hold)
/// must be caught here, before any frontier number is trusted.
#[test]
fn every_generated_instance_self_checks() {
    // bv_reduction: each depth is an exhaustively-verified UNSAT identity.
    for n in 1..=8 {
        bv_reduction_scenario(n)
            .self_check()
            .unwrap_or_else(|e| panic!("bv_reduction N={n} self-check: {e}"));
    }
    // lia_cuts: each system is a witness-checked SAT scenario.
    for n in 1..=8 {
        lia_cuts_scenario(n)
            .self_check()
            .unwrap_or_else(|e| panic!("lia_cuts N={n} self-check: {e}"));
    }
    // string_bound: each witness independently satisfies its string constraints.
    for n in 2..=12 {
        let w = string_bound_witness(n);
        assert!(
            string_bound_self_check(&w, n),
            "string_bound N={n}: witness {w:?} failed self-check",
        );
    }
}

/// The `bv_reduction` fall-off is **the reduction lever**, not a generic limit.
/// With `preprocess` OFF (and a capped encoding so the un-reduced tower can't be
/// brute-bit-blasted under budget), an instance well *inside* the reduction-on
/// frontier degrades to a non-`unsat` result; with `preprocess` ON (the default)
/// the same instance is decided. This is the attributability proof: the frontier
/// moves with the lever.
#[test]
fn bv_reduction_falloff_is_the_lever() {
    // A modest `N` whose `N²` multiplier tower reduction-ON folds trivially but
    // which is well past where the un-reduced bit-blast fits a capped encoding.
    let n = 6;

    let on = SolverConfig::new().with_timeout(BUDGET); // preprocess defaults ON
    let mut off = SolverConfig::new().with_timeout(BUDGET);
    off.preprocess = false;
    // Force the un-reduced path to actually feel the blow-up by capping the
    // encoding so the `N²`-multiplier tower can't be brute-bit-blasted under budget.
    off.cnf_clause_budget = Some(20_000);
    off.cnf_variable_budget = Some(20_000);
    off.node_budget = Some(20_000);

    let solved_on = solve_capped(bv_reduction_instance(n).unwrap(), on);
    assert_eq!(
        solved_on.status,
        "unsat",
        "reduction-ON must decide N={n} (depth {}, got {})",
        bv_reduction_depth(n),
        solved_on.status,
    );

    let solved_off = solve_capped(bv_reduction_instance(n).unwrap(), off);
    assert_ne!(
        solved_off.status, "unsat",
        "reduction-OFF (budget-capped) was expected to fall short at N={n}, but it \
         decided unsat anyway — the family no longer isolates the reduction lever; \
         deepen the tower",
    );
    eprintln!(
        "bv_reduction lever check: N={n} (depth {}) → reduction-ON {} / reduction-OFF(capped) {}",
        bv_reduction_depth(n),
        solved_on.status,
        solved_off.status,
    );
}
