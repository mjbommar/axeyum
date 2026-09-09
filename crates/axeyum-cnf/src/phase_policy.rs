//! Search-schedule policy for the CDCL core: the target/best phase split and
//! the rephase schedule, and the stable/focused **mode schedule** that gates
//! them.
//!
//! Two policy families live here because they are one mechanism, not two. The
//! rephase schedule below was landed without the mode switch it depends on, and
//! that dependency is stated in this module's own docs (see *What the reference
//! pairs this with*). [`RestartPolicy`] is that missing half: it decides which
//! of the two search modes is in force, which restart rule each mode runs, and
//! therefore whether [`PhasePolicy`] is allowed to fire at all.
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
//! # What the reference pairs this with
//!
//! Kissat updates the target and best marks **only in stable mode**
//! (`backtrack.c:41-43`, `if (!solver->stable) return;`) and rephases **only in
//! stable mode** (`rephase.c:34-36`, the same guard). Until 2026-09-09 we had no
//! stable/focused mode switching, so a schedule enabled here ran over the whole
//! search rather than over half of it. That was the most likely explanation for
//! the variance measured on our corpora: on two bit-blasted SAT instances,
//! [`PhasePolicy::releasing`] was 48% better on one and 21% worse on the other,
//! and the full `(B I B O)` schedule was 4x worse on one of them.
//!
//! [`RestartPolicy`] now supplies the missing half.
//! [`RestartConfig::rephase_in_stable_only`] is the guard, and it is on by
//! default *when switching is enabled*: with switching off there is no stable
//! mode, so the guard is inert rather than silently disabling
//! [`PhasePolicy::scheduled`]. What is deliberately **not** adopted is Kissat's
//! second guard — the target/best *snapshots* still run in both modes here. Two
//! guards landed together would make neither attributable, and the snapshot is
//! the cheap, non-disruptive half; that measurement has not been made and this
//! module does not claim it.
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

// ---------------------------------------------------------------------------
// Stable/focused mode switching.
// ---------------------------------------------------------------------------

/// Which of the two search modes the core is in.
///
/// The reference runs **two search policies over one solve** and alternates
/// between them rather than picking one: `CaDiCaL` carries a single
/// `bool stable` and every policy that differs reads it
/// (`references/cadical/src/internal.hpp:476`,
/// `bool use_scores () const { return opts.score && stable; }`). The switch
/// itself is `Internal::stabilizing()`,
/// `references/cadical/src/restart.cpp:18-84`.
///
/// The names are the reference's: `stable` is the long, quiet half with few
/// restarts, and `!stable` — *focused* in the literature — is the aggressive
/// half that restarts on the glue signal. **The search starts focused**:
/// `stable` is default-constructed `false`, and `stabilizing()` returns early
/// while `stats.conflicts <= lim.stabilize`.
///
/// One reference distinction is **not** reproduced, because the machinery does
/// not exist here: `CaDiCaL` also swaps its decision heuristic on this bit
/// (EVSIDS in stable, a VMTF bump queue in focused, plus random-decision bursts
/// in focused only). This core has one VSIDS heap and no bump queue, so the
/// mode changes the restart rule and the rephase gate and nothing else.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SearchMode {
    /// The aggressive half: restart on the glue signal, no rephasing.
    Focused,
    /// The quiet half: reluctant-doubling restarts at a long interval, and the
    /// only half in which the reference rephases.
    Stable,
}

impl Default for SearchMode {
    /// Focused. The search starts here, as the reference's does.
    fn default() -> Self {
        Self::Focused
    }
}

impl SearchMode {
    /// The other mode.
    #[must_use]
    pub fn other(self) -> Self {
        match self {
            Self::Focused => Self::Stable,
            Self::Stable => Self::Focused,
        }
    }

    /// A stable, lowercase name for a log line or a test assertion. Spelled out
    /// here rather than taken from `Debug`, which is not an output-format
    /// promise.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Focused => "focused",
            Self::Stable => "stable",
        }
    }

    /// Index into a two-element per-mode array — the shape of the reference's
    /// `stats.ticks.search[stable]`.
    const fn index(self) -> usize {
        match self {
            Self::Focused => 0,
            Self::Stable => 1,
        }
    }
}

/// The restart rule a mode runs.
///
/// The reference picks between exactly these two on the mode bit
/// (`restart.cpp:87-118`): under `stabilizing () && opts.reluctant` it returns
/// the reluctant-doubling flag, otherwise it applies the Glucose fast/slow glue
/// comparison with a per-mode margin (`restartmarginfocused` 10 percent,
/// `restartmarginstable` 25 percent).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RestartSchedule {
    /// Reluctant doubling (Luby). What this core has always run.
    Luby,
    /// Glucose fast/slow glue exponential moving averages with a blocking rule.
    /// Implemented in the CDCL core since T1.3.2 and, until this policy
    /// existed, reachable only by assigning a private field from inside a
    /// `#[cfg(test)]` module.
    Ema,
}

/// Transitions recorded before the log stops growing.
///
/// A cap, not a ring: the interesting part of a mode schedule is its
/// **beginning** — the intervals grow quadratically, so the tail is a handful
/// of enormous phases and dropping it loses nothing. 256 is unreachable in
/// practice: with a first increment of `i` ticks the 256th phase alone costs
/// about `i * 16_384` ticks.
pub const MAX_RECORDED_MODE_TRANSITIONS: usize = 256;

/// One mode switch, with the deterministic quantities that placed it.
///
/// Every field is an integer count of search events. Nothing here is a clock
/// read, so two runs of the same formula under the same options produce
/// identical transition lists on any host under any load — which is the
/// property a wall-time budget could not give, and the reason the switch is
/// denominated in ticks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModeTransition {
    /// The mode being entered.
    pub to: SearchMode,
    /// Conflicts analysed when the switch happened.
    pub at_conflicts: u64,
    /// Total search ticks when the switch happened.
    pub at_ticks: u64,
    /// Ticks the phase that just ended consumed.
    pub phase_ticks: u64,
    /// Ticks granted to the phase now beginning — the reference's
    /// `next_delta_ticks`. This is the quantity that grows quadratically, and
    /// the one to assert growth on.
    pub budget_ticks: u64,
    /// The absolute threshold that budget becomes, on the **entered mode's own**
    /// tick counter (`lim.stabilize = stats.ticks.search[next_stable] +
    /// next_delta_ticks`). Not comparable against
    /// [`ModeTransition::at_ticks`], which is the whole-search total.
    pub next_limit_ticks: u64,
}

/// What a search did with its mode schedule.
///
/// This is the observable half of the feature, and it exists because a mode
/// switch is easy to implement and hard to see: a test that checks only the
/// verdict passes with switching disabled, since both arms decide the same
/// formula. The schedule itself has to be readable for the mechanism to be
/// testable at all.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ModeSchedule {
    /// The mode the search is in now.
    pub mode: SearchMode,
    /// Mode switches performed.
    pub switches: u64,
    /// Stable phases entered (the reference's `stats.stabphases`, which is what
    /// drives the quadratic interval growth).
    pub stable_phases: u64,
    /// Search ticks spent in focused mode, including the phase in flight.
    pub focused_ticks: u64,
    /// Search ticks spent in stable mode, including the phase in flight.
    pub stable_ticks: u64,
    /// The transitions, oldest first, capped at
    /// [`MAX_RECORDED_MODE_TRANSITIONS`].
    pub transitions: Vec<ModeTransition>,
    /// Whether [`ModeSchedule::switches`] outran what `transitions` holds.
    pub transitions_truncated: bool,
}

impl ModeSchedule {
    /// The modes occupied, in order, starting with the one the search opened
    /// in — the cheapest form for a test to assert a whole schedule against,
    /// and the form a later `axeyum-solver` span-log lane would serialize.
    #[must_use]
    pub fn mode_sequence(&self) -> Vec<&'static str> {
        core::iter::once(SearchMode::default().as_str())
            .chain(self.transitions.iter().map(|t| t.to.as_str()))
            .collect()
    }
}

/// Tunables for [`RestartPolicy`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RestartConfig {
    /// Whether the mode alternates at all. `false` pins the search in
    /// [`SearchMode::Focused`] forever and runs [`RestartConfig::focused`]'s
    /// rule for the whole solve, which is how every entry point behaved before
    /// this type existed.
    pub switching: bool,
    /// The restart rule in focused mode.
    pub focused: RestartSchedule,
    /// The restart rule in stable mode.
    pub stable: RestartSchedule,
    /// Conflicts the **first** focused phase runs for.
    ///
    /// The first interval cannot be denominated in ticks because there is no
    /// tick history to size it from yet. The reference has the same bootstrap
    /// (`restart.cpp:41-45`: while `inc.stabilize` is zero it compares
    /// `stats.conflicts` against `lim.stabilize`, seeded from
    /// `opts.stabilizeinit`, default `1e3`), and then calibrates every later
    /// interval from what the first phase actually cost. Conflicts are
    /// themselves deterministic, so the bootstrap does not make the schedule
    /// host-dependent; it makes the first interval instance-shaped rather than
    /// work-shaped.
    pub bootstrap_conflicts: u64,
    /// Whether the rephase schedule is confined to stable mode.
    ///
    /// Kissat rephases only in stable mode (`rephase.c:34-36`). With
    /// [`RestartConfig::switching`] off this field has no effect: there is no
    /// stable mode to confine anything to, and gating on one would silently
    /// disable [`PhasePolicy::scheduled`] instead of gating it.
    pub rephase_in_stable_only: bool,
}

impl Default for RestartConfig {
    /// Today's shipped behaviour, exactly: Luby restarts, no switching, one
    /// mode for the whole solve.
    fn default() -> Self {
        Self {
            switching: false,
            focused: RestartSchedule::Luby,
            stable: RestartSchedule::Luby,
            bootstrap_conflicts: 1_000,
            rephase_in_stable_only: true,
        }
    }
}

/// The mode schedule's running state: which mode the search is in, how much
/// deterministic work this phase has left, and the log of what it did.
///
/// # Why ticks
///
/// The budget is a **tick** count ([`crate::ticks`]) rather than a conflict
/// count or an elapsed duration. Conflicts are the wrong unit for the reason
/// the tick module gives — a conflict on a ten-clause formula and one on a
/// ten-million-clause formula are not the same amount of work — and wall time
/// is wrong for a harder reason: determinism is a public API promise in this
/// repository, and a schedule that moved with host load would break it
/// invisibly. It would change the restart trajectory, and therefore the emitted
/// `DRAT` stream, under nothing but a busy machine. The reference reached the
/// same place: `stabilizing()` budgets in `stats.ticks.search[stable]`.
///
/// # Why quadratic
///
/// `next_delta_ticks = inc.stabilize * stabphases * stabphases`
/// (`restart.cpp:73-74`). Each phase is longer than the last, so a long solve
/// spends its time in a few large phases rather than thrashing between two
/// policies — and the increment is *calibrated from the instance*: it is the
/// tick cost the first focused phase actually paid.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RestartPolicy {
    cfg: RestartConfig,
    mode: SearchMode,
    switches: u64,
    stable_phases: u64,
    /// The reference's `inc.stabilize`: ticks the first phase cost, and the
    /// unit every later interval is a multiple of. Zero until bootstrapped.
    increment: u64,
    /// The reference's `lim.stabilize`, applied to the **current** mode's own
    /// accumulated tick count.
    limit: u64,
    /// Total ticks at the moment the current mode was entered.
    entry_ticks: u64,
    /// Ticks charged to each mode by phases that have already ended.
    ticks_in_mode: [u64; 2],
    transitions: Vec<ModeTransition>,
    transitions_truncated: bool,
}

impl Default for RestartPolicy {
    fn default() -> Self {
        Self::new(RestartConfig::default())
    }
}

impl RestartPolicy {
    /// A policy from an explicit configuration.
    #[must_use]
    pub fn new(cfg: RestartConfig) -> Self {
        Self {
            cfg,
            mode: SearchMode::default(),
            switches: 0,
            stable_phases: 0,
            increment: 0,
            limit: 0,
            entry_ticks: 0,
            ticks_in_mode: [0, 0],
            transitions: Vec::new(),
            transitions_truncated: false,
        }
    }

    /// Luby restarts for the whole solve, no switching — the pre-2026-09
    /// behaviour, and still the default.
    #[must_use]
    pub fn luby() -> Self {
        Self::new(RestartConfig::default())
    }

    /// The Glucose glue-EMA schedule for the whole solve, no switching.
    ///
    /// **This is the production setter the EMA schedule never had.** The rule
    /// has been implemented, sound, `DRAT`-checked and deterministic since
    /// T1.3.2, and the only way to select it was to assign a private field from
    /// inside a `#[cfg(test)]` module, so no shipping caller could reach it.
    #[must_use]
    pub fn ema() -> Self {
        Self::new(RestartConfig {
            focused: RestartSchedule::Ema,
            stable: RestartSchedule::Ema,
            ..RestartConfig::default()
        })
    }

    /// The reference's arrangement: start focused with glue-EMA restarts,
    /// alternate into stable with reluctant doubling, on a tick budget that
    /// grows quadratically.
    #[must_use]
    pub fn mode_switching() -> Self {
        Self::mode_switching_after(RestartConfig::default().bootstrap_conflicts)
    }

    /// [`RestartPolicy::mode_switching`] with a different first interval.
    ///
    /// The bootstrap length is the one interval a caller might reasonably want
    /// to shorten: it is the only one not calibrated from the instance, and a
    /// test that needs several phases inside a small search cannot get them at
    /// the shipped 1000 conflicts.
    #[must_use]
    pub fn mode_switching_after(bootstrap_conflicts: u64) -> Self {
        Self::new(RestartConfig {
            bootstrap_conflicts,
            ..RestartConfig {
                switching: true,
                focused: RestartSchedule::Ema,
                stable: RestartSchedule::Luby,
                ..RestartConfig::default()
            }
        })
    }

    /// The restart rule in force right now.
    #[must_use]
    pub fn schedule(&self) -> RestartSchedule {
        match self.mode {
            SearchMode::Focused => self.cfg.focused,
            SearchMode::Stable => self.cfg.stable,
        }
    }

    /// The mode the search is in.
    #[must_use]
    pub fn mode(&self) -> SearchMode {
        self.mode
    }

    /// Whether the glue and trail moving averages have to be maintained.
    ///
    /// True whenever *either* mode runs [`RestartSchedule::Ema`], not just the
    /// current one: an average that stopped updating through a stable phase
    /// would re-enter focused mode stale and fire a burst of restarts off
    /// arithmetic from before the gap. The reference keeps both modes' averages
    /// live and swaps them (`restart.cpp:79`, `swap_averages ()`); one shared
    /// set kept always-current is the closest single-average equivalent.
    ///
    /// It is `false` for [`RestartPolicy::luby`], so the default search still
    /// executes no EMA arithmetic at all.
    #[must_use]
    pub fn tracks_emas(&self) -> bool {
        self.cfg.focused == RestartSchedule::Ema || self.cfg.stable == RestartSchedule::Ema
    }

    /// Whether this policy needs a tick reading at all. Only mode switching
    /// does, so a default search never pays for the meter.
    #[must_use]
    pub fn needs_ticks(&self) -> bool {
        self.cfg.switching
    }

    /// Whether a scheduled rephase may run now.
    ///
    /// Always true when switching is off — see
    /// [`RestartConfig::rephase_in_stable_only`] for why that is not an
    /// oversight.
    #[must_use]
    pub fn rephase_allowed(&self) -> bool {
        !self.cfg.switching || !self.cfg.rephase_in_stable_only || self.mode == SearchMode::Stable
    }

    /// Is a mode switch due?
    ///
    /// `conflicts` and `ticks` are both cumulative over the search. Returns
    /// `false` forever when switching is off, so the call costs one `bool` test
    /// on the default path.
    #[must_use]
    pub fn should_switch(&self, conflicts: u64, ticks: u64) -> bool {
        if !self.cfg.switching {
            return false;
        }
        if self.increment == 0 {
            // Bootstrap: no tick history yet, so the first phase is measured in
            // conflicts (`restart.cpp:41-45`).
            return conflicts > self.cfg.bootstrap_conflicts;
        }
        self.ticks_in(self.mode, ticks) > self.limit
    }

    /// Performs the switch and returns the mode now in force. Only call when
    /// [`RestartPolicy::should_switch`] returned `true`.
    pub fn switch(&mut self, conflicts: u64, ticks: u64) -> SearchMode {
        debug_assert!(self.cfg.switching);
        let phase_ticks = ticks.saturating_sub(self.entry_ticks);
        let closed = &mut self.ticks_in_mode[self.mode.index()];
        *closed = closed.saturating_add(phase_ticks);
        if self.increment == 0 {
            // `inc.stabilize = delta_ticks`, forced to at least 1 because a
            // phase can genuinely cost zero ticks (`restart.cpp:65-68`) and a
            // zero increment would make every later interval zero-length —
            // which is a live thrash, not a theoretical one, since a search
            // with counting disabled reports zero ticks forever.
            self.increment = phase_ticks.max(1);
        }
        // `stabphases = stats.stabphases + 1` is read BEFORE the flip, and
        // `stats.stabphases` is incremented after it and only when the entered
        // mode is stable (`restart.cpp:72-73`, `:82-83`). That is what makes the
        // multiplier sequence 1, 4, 4, 9, 9, 16, ... rather than 1, 4, 9, 16.
        let stabphases = self.stable_phases.saturating_add(1);
        let next_delta = self
            .increment
            .saturating_mul(stabphases.saturating_mul(stabphases));
        let next = self.mode.other();
        // The limit is on the ENTERED mode's own tick counter, as the
        // reference's `lim.stabilize = stats.ticks.search[next_stable] + ...`
        // is. A mode is budgeted against the work it has done itself, not
        // against the search total.
        let next_limit = self.ticks_in(next, ticks).saturating_add(next_delta);
        self.limit = next_limit;
        self.mode = next;
        self.entry_ticks = ticks;
        self.switches = self.switches.saturating_add(1);
        if next == SearchMode::Stable {
            self.stable_phases = self.stable_phases.saturating_add(1);
        }
        if self.transitions.len() < MAX_RECORDED_MODE_TRANSITIONS {
            self.transitions.push(ModeTransition {
                to: next,
                at_conflicts: conflicts,
                at_ticks: ticks,
                phase_ticks,
                budget_ticks: next_delta,
                next_limit_ticks: next_limit,
            });
        } else {
            self.transitions_truncated = true;
        }
        next
    }

    /// Mode switches performed.
    #[must_use]
    pub fn switches(&self) -> u64 {
        self.switches
    }

    /// A snapshot of what the schedule has done, at cumulative tick count
    /// `ticks`. This is what a caller reads after a solve, and what a later
    /// span-log lane would serialize.
    #[must_use]
    pub fn snapshot(&self, ticks: u64) -> ModeSchedule {
        ModeSchedule {
            mode: self.mode,
            switches: self.switches,
            stable_phases: self.stable_phases,
            focused_ticks: self.ticks_in(SearchMode::Focused, ticks),
            stable_ticks: self.ticks_in(SearchMode::Stable, ticks),
            transitions: self.transitions.clone(),
            transitions_truncated: self.transitions_truncated,
        }
    }

    /// Resets the schedule for a fresh solve (incremental use).
    pub fn reset(&mut self) {
        let cfg = self.cfg.clone();
        *self = Self::new(cfg);
    }

    /// A mode's accumulated ticks, including the phase in flight if it is the
    /// current one — the reference's `stats.ticks.search[mode]`.
    fn ticks_in(&self, mode: SearchMode, ticks: u64) -> u64 {
        let closed = self.ticks_in_mode[mode.index()];
        if mode == self.mode {
            closed.saturating_add(ticks.saturating_sub(self.entry_ticks))
        } else {
            closed
        }
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
