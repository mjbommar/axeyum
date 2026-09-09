//! How a linear-real query is routed between the two engines behind one route
//! label, as a policy object with a legacy arm.
//!
//! # The measurement this exists for
//!
//! `QF_LRA` has two deciders. The **online CDCL(T)** engine
//! ([`crate::lra_theory::check_qf_lra_online_cdclt`]) searches the Boolean
//! skeleton with an incremental simplex in lockstep, propagating bounds and
//! learning from theory conflicts inside the search. The **offline lazy-SMT**
//! loop ([`crate::dpll_t::check_with_lra_dpll_within`]) solves the whole
//! skeleton to a TOTAL assignment, hands every atom to a cold conjunctive
//! decision, and turns the refutation into one blocking clause. The second is
//! the fallback, and it is much weaker: measured 2026-09-08 over the 22
//! `QF_LRA` files bound by it, a round costs 48-2,000 ms and buys a clause of
//! 2.0-19.0 literals against 265-1,736 atoms.
//!
//! Which engine a file gets, and what that engine then spends its budget on,
//! were decided by three things that were not policy and not visible:
//!
//! 1. **The skeleton encoder's coverage.** The online encoder had no arm for
//!    Boolean equality, while the offline abstractor has always had one, so the
//!    two halves of one route disagreed about the input language and every file
//!    containing an `iff` took the weak half.
//! 2. **What `dpll_t` does with the probe's decline.** It treated every
//!    `ResourceLimit` as "the online engine owned the budget" and returned
//!    `unknown` — but the admission screen and the build ceilings are
//!    microsecond structural refusals, not exhausted budgets, and the offline
//!    loop is exactly the fallback they should reach.
//!
//! 3. **Which engine the conjunctive decider tries first.** Fourier-Motzkin ran
//!    before the exact-rational simplex on every system, and on this population
//!    it declined on 2,745 of 2,745 cubes after consuming 96-99.9% of the
//!    loop's theory time. See [`SIMPLEX_FIRST_AT_CONSTRAINTS`].
//!
//! All three are now fields with a [`LraRoutePolicy::legacy`] arm reproducing
//! the pre-2026-09-08 behaviour, so a base-vs-arm A/B is one binary and two
//! runs rather than two binaries whose difference is confounded by everything
//! else that changed between them.

use crate::lra_online::SkeletonEncoding;

/// Constraint count at or above which the exact-rational simplex decides a cube
/// **before** Fourier–Motzkin is tried.
///
/// Measured 2026-09-08 on the 2,745 cubes the offline lazy-SMT loop decided
/// across the 22 `QF_LRA` files bound by it (265–1,736 atoms): Fourier–Motzkin
/// declined on **every one of them**, having spent 96–99.9% of the loop's
/// theory time — 21.5 to 23.7 s of a 24 s budget — reaching its
/// `lra::MAX_FM_CONSTRAINTS` size guard, and the simplex then decided all 2,745
/// in 43–696 ms in total.
///
/// The threshold sits at the **bottom of the measured range**, not lower: 265
/// is the smallest system in that population, and there is no measurement of
/// the elimination's success rate below it. Elimination is exact, so on a small
/// system it produces the *tightest* refutation — which is evidence quality,
/// not just a verdict — and dropping the threshold to 0 measurably changed one
/// such certificate (`nra_handelman_cert`'s residual, `−31/400` → `−31/1580`).
/// So this bound is a claim about where the elimination is known to be useless,
/// and nothing more.
pub(crate) const SIMPLEX_FIRST_AT_CONSTRAINTS: usize = 256;

/// Route policy for the linear-real engines; see the module docs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LraRoutePolicy {
    /// Which connectives the online skeleton encoder covers.
    pub(crate) encoding: SkeletonEncoding,
    /// Whether a probe decline that consumed **none** of the budget falls
    /// through to the offline lazy-SMT loop.
    ///
    /// `false` is the pre-2026-09-08 rule: any `Timeout` or `ResourceLimit`
    /// from the probe ends the query. That is right for a `Timeout` and wrong
    /// for the admission screen and the two build ceilings, which refuse in
    /// microseconds on a structural property of the input. With the encoder
    /// widened, a file too large for the online engine would otherwise stop
    /// getting the 24 s of offline search it gets today — a change that shows
    /// up as a wall-clock improvement and is a capability loss.
    pub(crate) fall_through_on_cheap_decline: bool,
    /// Constraint count at or above which the exact-rational simplex decides a
    /// cube before Fourier–Motzkin is tried; see
    /// [`SIMPLEX_FIRST_AT_CONSTRAINTS`]. `usize::MAX` is the pre-2026-09-08
    /// order — the elimination always first, on every system.
    ///
    /// Both engines are sound and each declines on cases the other decides, so
    /// the order is a pure cost choice: whichever runs first, the one that
    /// declines hands the identical system to the other, and the union of what
    /// the pair decides does not depend on the order.
    pub(crate) simplex_first_at_constraints: usize,
}

impl LraRoutePolicy {
    /// Whether a system of `constraints` rows goes to the simplex first.
    pub(crate) fn simplex_first(&self, constraints: usize) -> bool {
        constraints >= self.simplex_first_at_constraints
    }
}

impl LraRoutePolicy {
    /// The shipped policy.
    pub(crate) const fn new() -> Self {
        Self {
            encoding: SkeletonEncoding::new(),
            fall_through_on_cheap_decline: true,
            simplex_first_at_constraints: SIMPLEX_FIRST_AT_CONSTRAINTS,
        }
    }

    /// The pre-2026-09-08 policy exactly. Kept runnable rather than remembered:
    /// it is the baseline every measurement of the new arm is a ratio against.
    pub(crate) const fn legacy() -> Self {
        Self {
            encoding: SkeletonEncoding::legacy(),
            fall_through_on_cheap_decline: false,
            simplex_first_at_constraints: usize::MAX,
        }
    }
}

impl Default for LraRoutePolicy {
    fn default() -> Self {
        Self::new()
    }
}

/// The policy in force, read **once** from `AXEYUM_LRA_ROUTE`.
///
/// Recognised values, all case- and space-insensitive:
///
/// - `legacy` — [`LraRoutePolicy::legacy`], the whole pre-2026-09-08 behaviour.
/// - `no-bool-eq` — the widened fall-through with the encoder arm off, which is
///   what isolates the encoder from the routing change.
/// - `no-fall-through` — the widened encoder with the old return rule, the
///   other half of the same isolation.
/// - `fm-first` — the shipped policy with the cube decider's old order, which
///   isolates the ~97%-of-budget elimination from everything else.
/// - `cube-order-only` — the legacy policy with ONLY the cube order changed,
///   the mirror of `fm-first` and the arm that attributes the whole gain to
///   the order without moving any file between engines.
/// - an integer — [`LraRoutePolicy::simplex_first_at_constraints`] on the
///   shipped policy, which is the one number here worth sweeping: it is set at
///   the bottom of a measured range and nothing has measured below it.
///
/// Anything else, including an unset variable, is [`LraRoutePolicy::new`]. An
/// unrecognised value falls back to the default rather than failing: this is a
/// measurement lever and a typo in a sweep script must not change a verdict.
/// Read once into a `OnceLock` because determinism is a public API promise —
/// the policy cannot change between two solves in one process — and the arm in
/// force is visible in `--trace` through `; lazy-smt online_probe=…`, which is
/// where a reader would notice the arm they did not intend.
pub(crate) fn configured() -> LraRoutePolicy {
    use std::sync::OnceLock;
    static POLICY: OnceLock<LraRoutePolicy> = OnceLock::new();
    *POLICY.get_or_init(|| match std::env::var("AXEYUM_LRA_ROUTE") {
        Ok(v) => match v.trim().to_ascii_lowercase().as_str() {
            "legacy" => LraRoutePolicy::legacy(),
            "no-bool-eq" => LraRoutePolicy {
                encoding: SkeletonEncoding::legacy(),
                ..LraRoutePolicy::new()
            },
            "no-fall-through" => LraRoutePolicy {
                fall_through_on_cheap_decline: false,
                ..LraRoutePolicy::new()
            },
            "fm-first" => LraRoutePolicy {
                simplex_first_at_constraints: usize::MAX,
                ..LraRoutePolicy::new()
            },
            "cube-order-only" => LraRoutePolicy {
                simplex_first_at_constraints: SIMPLEX_FIRST_AT_CONSTRAINTS,
                ..LraRoutePolicy::legacy()
            },
            other => other.parse::<usize>().map_or_else(
                |_| LraRoutePolicy::new(),
                |at| LraRoutePolicy {
                    simplex_first_at_constraints: at,
                    ..LraRoutePolicy::new()
                },
            ),
        },
        Err(_) => LraRoutePolicy::new(),
    })
}

#[cfg(test)]
mod tests {
    use super::{LraRoutePolicy, SIMPLEX_FIRST_AT_CONSTRAINTS, configured};

    /// The legacy arm must differ from the shipped one in EVERY field, or the
    /// A/B it exists for cannot separate the changes it bundles.
    ///
    /// Written field by field rather than as one `assert_ne!` on the struct: a
    /// whole-struct inequality passes when a single field differs, which is
    /// exactly the state this test exists to reject.
    #[test]
    fn the_legacy_arm_differs_in_every_field() {
        let new = LraRoutePolicy::new();
        let legacy = LraRoutePolicy::legacy();
        assert_ne!(new.encoding, legacy.encoding);
        assert_ne!(
            new.fall_through_on_cheap_decline,
            legacy.fall_through_on_cheap_decline
        );
        assert_ne!(
            new.simplex_first_at_constraints,
            legacy.simplex_first_at_constraints
        );
    }

    /// The threshold must actually gate, and it must gate at the size the
    /// measurement covers.
    ///
    /// The three probes are the bound itself and its two neighbours, derived
    /// from the constant rather than written as literals: a test that repeated
    /// `256` would keep passing after somebody moved the constant and would
    /// then be measuring nothing. The legacy arm must answer `false` at a size
    /// far above the bound, or it is not the pre-2026-09-08 order.
    #[test]
    fn the_threshold_gates_at_the_bottom_of_the_measured_range() {
        let shipped = LraRoutePolicy::new();
        assert!(!shipped.simplex_first(SIMPLEX_FIRST_AT_CONSTRAINTS - 1));
        assert!(shipped.simplex_first(SIMPLEX_FIRST_AT_CONSTRAINTS));
        assert!(shipped.simplex_first(SIMPLEX_FIRST_AT_CONSTRAINTS + 1));
        // 265 is the smallest system in the measured population; the bound has
        // to be below it or the measurement does not support the arm.
        assert!(shipped.simplex_first(265));
        assert!(!LraRoutePolicy::legacy().simplex_first(1_736));
    }

    /// `configured` is read once and must be self-consistent within a process;
    /// the test asserts the *identity* of the two reads rather than a literal,
    /// so it cannot drift from whatever arm the environment selected.
    #[test]
    fn the_configured_policy_is_stable_within_a_process() {
        assert_eq!(configured(), configured());
    }
}
