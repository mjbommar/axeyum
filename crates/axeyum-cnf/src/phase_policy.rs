//! Decision-phase policy for the CDCL core: the target/best split and the
//! rephase schedule.
//!
//! # The problem this exists to fix
//!
//! Phase saving decides a variable at its last-seen polarity. *Target* phasing
//! is stronger: it records the polarities of the deepest conflict-free
//! assignment seen (the one "closest to a model") and re-descends into it after
//! a restart. Stronger is not automatically better — a target that is recorded
//! once and never released is a **ratchet with no release**:
//!
//! 1. The high-water mark is monotone, so after one deep dive nothing beats it.
//! 2. The snapshot therefore stops firing for the rest of the run.
//! 3. But the restart-time `phase := target` keeps firing, at every restart.
//!
//! The result is that every restart re-descends into the same stale region with
//! no diversification path out — which is worse than plain phase saving, not
//! better. Kissat resets `target_assigned` at every rephase for exactly this
//! reason, and its own description says so: *"the target assignment is reset
//! after each rephasing to the initial all-unassigned state. This encourages the
//! solver to find larger and larger target assignments until the next
//! rephasing. The largest one will be recorded as best assignment and reused in
//! the next best rephasing."*
//!
//! # The split
//!
//! Two marks, two jobs:
//!
//! - **target** — what restarts read. Reset on every rephase, so the search is
//!   pushed to beat a fresh mark rather than an unbeatable one.
//! - **best** — the long-run archive. Reset only when a `Best` rephase consumes
//!   it, so the deepest assignment of the whole run is never lost.
//!
//! # The schedule
//!
//! The reference cycles `(B W I B W O)`: best, walk, inverted, best, walk,
//! original. `W` is a bounded `ProbSAT` local-search walk, which we do not have,
//! so the reachable subset is `(B I B O)`. [`RephaseAction::TargetOnly`] is a
//! fourth action with no reference analogue: release the ratchet and change
//! nothing else. It exists so the *reset* can be measured on its own, separately
//! from the schedule that would normally accompany it.
//!
//! # What the reference pairs this with, and we do not
//!
//! Kissat updates the target and best marks **only in stable mode**
//! (`backtrack.c:41-43`, `if (!solver->stable) return;`) and rephases **only in
//! stable mode** (`rephase.c:34-36`, the same guard). We have no stable/focused
//! mode switching, so a schedule enabled here runs over the whole search rather
//! than over half of it. That is the most likely explanation for the variance
//! measured on our corpora: on two bit-blasted SAT instances,
//! [`PhasePolicy::releasing`] was 48% better on one and 21% worse on the other,
//! and the full `(B I B O)` schedule was 4x worse on one of them. Treat mode
//! switching as a prerequisite for tuning this, not as an unrelated feature.
//!
//! # Source
//!
//! `docs/research/02-ecosystems/pipeline-survey-2026-09/cdcl-core-engine.md`,
//! finding R6, citing Kissat `rephase.c:86-89, 112, 117-123` and
//! Biere & Fleury, *Chasing Target Phases*, POS 2020.

/// What a scheduled rephase installs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RephaseAction {
    /// Release the target high-water mark and change no polarity. The minimal
    /// fix for a pinned ratchet: the search keeps its saved phases and simply
    /// becomes able to record a new target again.
    TargetOnly,
    /// Reinstall the long-run best assignment, then release both marks. This is
    /// the action that consumes the archive.
    Best,
    /// Install the complement of the initial phase everywhere — the strongest
    /// available diversification without a local-search walker.
    Inverted,
    /// Install the initial phase everywhere.
    Original,
}

/// Tunables for [`PhasePolicy`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhaseConfig {
    /// Whether rephasing runs at all. `false` reproduces the pre-2026-09
    /// behaviour exactly: one monotone mark, never released.
    pub enabled: bool,
    /// Conflict-interval scale. The interval before the `n`-th rephase is
    /// `base * n * log10(n + 9)^3`, so it starts at `base` and grows
    /// superlinearly — rephasing is disruptive and should get rarer. Default
    /// 1000, matching the reference's `rephaseint`.
    pub interval_base: u64,
    /// The cycle of actions, applied in order and repeated. Default
    /// `[Best, Inverted, Best, Original]` — the reference's `(B W I B W O)` with
    /// the two local-search walks removed.
    pub schedule: Vec<RephaseAction>,
}

impl Default for PhaseConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            interval_base: 1_000,
            schedule: vec![
                RephaseAction::Best,
                RephaseAction::Inverted,
                RephaseAction::Best,
                RephaseAction::Original,
            ],
        }
    }
}

/// The rephase schedule's state: how many rephases have happened and when the
/// next one is due.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhasePolicy {
    cfg: PhaseConfig,
    rephased: u64,
    next_conflicts: u64,
}

impl Default for PhasePolicy {
    fn default() -> Self {
        Self::new(PhaseConfig::default())
    }
}

impl PhasePolicy {
    /// A policy from an explicit configuration.
    #[must_use]
    pub fn new(cfg: PhaseConfig) -> Self {
        let next_conflicts = cfg.interval_base;
        Self {
            cfg,
            rephased: 0,
            next_conflicts,
        }
    }

    /// The pre-2026-09 behaviour: no rephasing, one monotone target mark that
    /// never releases. Kept selectable so the change can be A/B measured
    /// without reverting code.
    #[must_use]
    pub fn pinned() -> Self {
        Self::new(PhaseConfig {
            enabled: false,
            ..PhaseConfig::default()
        })
    }

    /// Release the target ratchet on the schedule and do nothing else. This
    /// isolates the *reset* from the phase reinstallation, which is what makes
    /// the two separately attributable in a measurement.
    #[must_use]
    pub fn releasing() -> Self {
        Self::new(PhaseConfig {
            enabled: true,
            schedule: vec![RephaseAction::TargetOnly],
            ..PhaseConfig::default()
        })
    }

    /// The full reachable schedule, `(B I B O)`.
    #[must_use]
    pub fn scheduled() -> Self {
        Self::new(PhaseConfig::default())
    }

    /// Is a rephase due at this conflict count?
    #[must_use]
    pub fn should_rephase(&self, conflicts: u64) -> bool {
        self.cfg.enabled && conflicts >= self.next_conflicts
    }

    /// Advances the schedule and returns the action to apply. Only call when
    /// [`PhasePolicy::should_rephase`] returned `true`.
    pub fn next_action(&mut self, conflicts: u64) -> RephaseAction {
        debug_assert!(self.cfg.enabled);
        debug_assert!(!self.cfg.schedule.is_empty());
        #[allow(clippy::cast_possible_truncation)]
        let index = (self.rephased % self.cfg.schedule.len() as u64) as usize;
        let action = self.cfg.schedule[index];
        self.rephased += 1;
        self.next_conflicts = conflicts.saturating_add(self.interval());
        action
    }

    /// Conflicts until the next rephase: `base * n * log10(n + 9)^3`, with `n`
    /// the number of rephases already performed.
    fn interval(&self) -> u64 {
        #[allow(clippy::cast_precision_loss)]
        let n = self.rephased.max(1) as f64;
        let factor = (n + 9.0).log10();
        #[allow(clippy::cast_precision_loss)]
        let base = self.cfg.interval_base as f64;
        let value = base * n * factor * factor * factor;
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        {
            (value as u64).max(1)
        }
    }

    /// Rephases performed so far.
    #[must_use]
    pub fn rephases(&self) -> u64 {
        self.rephased
    }

    /// Whether this policy ever releases the target mark. `false` means the
    /// search runs the monotone ratchet.
    #[must_use]
    pub fn releases_target(&self) -> bool {
        self.cfg.enabled
    }

    /// Resets the schedule for a fresh solve (incremental use).
    pub fn reset(&mut self) {
        self.rephased = 0;
        self.next_conflicts = self.cfg.interval_base;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pinned_policy_never_rephases() {
        let policy = PhasePolicy::pinned();
        assert!(!policy.should_rephase(0));
        assert!(!policy.should_rephase(u64::MAX));
        assert!(!policy.releases_target());
    }

    #[test]
    fn first_rephase_is_due_at_the_interval_base() {
        let mut policy = PhasePolicy::releasing();
        assert!(!policy.should_rephase(999));
        assert!(policy.should_rephase(1_000));
        assert_eq!(policy.next_action(1_000), RephaseAction::TargetOnly);
        assert_eq!(policy.rephases(), 1);
    }

    #[test]
    fn the_interval_grows_superlinearly() {
        let mut policy = PhasePolicy::scheduled();
        let mut conflicts = 0u64;
        let mut gaps = Vec::new();
        let mut previous = 0u64;
        for _ in 0..6 {
            while !policy.should_rephase(conflicts) {
                conflicts += 1;
            }
            gaps.push(conflicts - previous);
            previous = conflicts;
            policy.next_action(conflicts);
        }
        // The first two gaps are both `interval_base`: the schedule opens at
        // `base` and the first advance computes `base * 1 * log10(10)^3 = base`.
        // The reference has the same shape (`rephaseinit == rephaseint`).
        assert_eq!(gaps[0], 1_000);
        assert_eq!(gaps[1], 1_000);
        for window in gaps.windows(2) {
            assert!(
                window[1] >= window[0],
                "rephase gaps must never shrink: {gaps:?}"
            );
        }
        for window in gaps[1..].windows(2) {
            assert!(
                window[1] > window[0],
                "rephase gaps must grow after the first: {gaps:?}"
            );
        }
        // Superlinear, not merely linear: the 6th gap is more than 6x the first.
        assert!(gaps[5] > 6 * gaps[0], "gaps {gaps:?} grew only linearly");
    }

    #[test]
    fn the_schedule_cycles() {
        use RephaseAction::{Best, Inverted, Original};

        let mut policy = PhasePolicy::scheduled();
        let mut conflicts = 0u64;
        let mut seen = Vec::new();
        for _ in 0..9 {
            while !policy.should_rephase(conflicts) {
                conflicts += 1;
            }
            seen.push(policy.next_action(conflicts));
        }
        assert_eq!(
            seen,
            vec![
                Best, Inverted, Best, Original, Best, Inverted, Best, Original, Best
            ]
        );
    }

    #[test]
    fn reset_restarts_the_schedule() {
        let mut policy = PhasePolicy::scheduled();
        policy.next_action(1_000);
        policy.next_action(5_000);
        assert_eq!(policy.rephases(), 2);
        policy.reset();
        assert_eq!(policy.rephases(), 0);
        assert!(!policy.should_rephase(999));
        assert!(policy.should_rephase(1_000));
    }
}
