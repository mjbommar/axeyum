//! Wall-clock deadline regression for the regex-membership closure/witness
//! searches (task #54).
//!
//! The membership emptiness closure and witness DFS poll their deadline **inside**
//! each derivative (via `derivative_within`), not only between nodes. This test
//! pins a *deliberately pathological* `Σ*`-enlarged intersection — the shape a
//! `str.in_re` over a `str.++` of free vars produces (`R ∩ shape`, where `shape`
//! injects `Σ*` runs) — and asserts the solver **declines within the deadline's
//! wall-clock**, not merely within the state cap.
//!
//! Without the in-derivative poll the closure's between-node poll fires only every
//! 64 expansions, so a single pathological derivative could grind for a whole
//! ~64-derivative window (measured ≈ 1.3-1.8 s on the dev box for `K = 22`) before
//! the deadline is honored. The ceiling below is far under that window, so a
//! reversion that drops the frontier poll fails this test.

use std::time::{Duration, Instant};

use axeyum_strings::{Membership, MembershipOutcome, Regex, SearchBudget};

/// Number of overlapping `Σ* [c,c+40] Σ*` "contains a char in this range" atoms
/// intersected together. Their ranges overlap, so the derivative's `product`
/// frontier does real (non-collapsing) work per state, and the reachable closure
/// is large (hundreds of states, several seconds to fully materialize).
const K: u32 = 22;

/// The dev-box budget window (64 derivatives) for `K = 22` is ≈ 1.3-1.8 s; this
/// ceiling is comfortably under it and comfortably over the ~deadline the frontier
/// poll delivers, on any machine.
const CEILING: Duration = Duration::from_millis(1_500);
const DEADLINE: Duration = Duration::from_millis(100);

fn contains_range(lo: u32, hi: u32) -> Regex {
    Regex::concat(
        Regex::star(Regex::any_char()),
        Regex::concat(Regex::char_range(lo, hi), Regex::star(Regex::any_char())),
    )
}

/// The pathological `Σ*`-enlarged intersection as a `Membership` with `K`
/// overlapping-range positives.
fn pathological() -> Membership {
    let base = u32::from(b'A');
    Membership {
        positives: (0..K)
            .map(|i| contains_range(base + i, base + i + 40))
            .collect(),
        ..Membership::default()
    }
}

fn budget_with_deadline() -> SearchBudget {
    SearchBudget::with_deadline(1_000_000, Instant::now() + DEADLINE)
}

#[test]
fn solve_declines_within_deadline_on_enlarged_intersection() {
    let m = pathological();
    let t = Instant::now();
    let outcome = m.solve(&budget_with_deadline());
    let elapsed = t.elapsed();

    // The frontier poll bounds the wall-clock to ~the deadline. A wrong verdict is
    // impossible here: the honest answer on an over-budget search is `Unknown`.
    assert_eq!(
        outcome,
        MembershipOutcome::Unknown,
        "an over-budget enlarged intersection must decline to Unknown"
    );
    assert!(
        elapsed < CEILING,
        "solve overshot the deadline: {elapsed:?} >= {CEILING:?} \
         (the derivative frontier poll must bound the wall-clock)"
    );
}

#[test]
fn refute_empty_within_returns_within_deadline_on_enlarged_intersection() {
    // The `unsat`-side closure path (per-assert emptiness refuter on the online
    // string route): it builds the full derivative closure, which is exactly the
    // between-64-node-poll window the frontier poll closes.
    let m = pathological();
    let t = Instant::now();
    let refuted = m.refute_empty_within(20_000, &budget_with_deadline());
    let elapsed = t.elapsed();

    // The language is non-empty, so a *complete* closure would never certify it
    // empty; under the deadline the closure abandons (⇒ `false`, "not proven
    // empty") — never a fabricated conflict.
    assert!(
        !refuted,
        "a non-empty language must not be refuted as empty"
    );
    assert!(
        elapsed < CEILING,
        "refute_empty_within overshot the deadline: {elapsed:?} >= {CEILING:?}"
    );
}
