//! The solver's configuration surface: enumerable, recordable and dated
//! (ADR-1762).
//!
//! Dozens of caps, bounds, budgets and thresholds govern dispatch and the
//! theory/Boolean engines. Until this module they were private `const`s with no
//! list, no per-run record, and no date on their justifications. Each of those
//! three gaps has cost a lane in the last week:
//!
//! - **No list.** [`crate::nra`]'s admission gate metered in *cross-products*
//!   while the engine consuming its output meters in *atoms* and refuses above
//!   `lra_theory::MAX_ONLINE_LRA_ATOMS`. Two gates on one resource, 15x apart,
//!   in incommensurable units — visible only to someone reading both files at
//!   once. ADR-1751 made admission the consumer's own capacity.
//! - **No per-run record.** A run did not emit the configuration it used, so an
//!   experiment was not reproducible from its own output and a surprising result
//!   could not be traced back to a value. `AXEYUM_NRA_ADMISSION` alone selects
//!   between two admission policies that differ by 15x and left no trace.
//! - **No date.** `MAX_ONLINE_LRA_ATOMS = 1_024` rested on a measurement taken
//!   2026-08-03 (`e62086742`) of an 8 GiB abort. `MAX_LRA_CACHED_COEFFICIENTS`,
//!   the bound that caps exactly that cost, landed 2026-08-06 (`96ff85930`) —
//!   **three days later**. The number described a tree in which the thing it
//!   protected against was unbounded, and it stood for thirteen months.
//!
//! # What an entry is, and what it is not
//!
//! A **governing value** is a numeric constant or environment override compared
//! against a runtime-varying quantity — it appears in a `<`, `>`, `<=`, `>=`,
//! `.min(`, `.max(`, `saturating_sub`, or a loop/iteration budget — such that
//! changing it could change which route is taken, whether a query is admitted,
//! how much work is done before giving up, or whether the verdict is `unknown`.
//! Structural constants (bit widths, type-tied sizes, indices) are out of scope
//! and are listed as explicit exemptions by the coverage test rather than being
//! omitted silently.
//!
//! An entry is a **description**, never the value itself: `value` is the literal
//! as written at the definition site, and nothing in this module is read by the
//! code an entry describes. Registering a bound cannot change it, and a wrong
//! entry cannot make the solver behave differently — it can only fail this
//! module's own checks.
//!
//! # How much of this is measured
//!
//! **Most of it is not.** [`dated_count`] and [`undated_count`] are derived
//! from the table, `config_trace_line` prints both on every `--trace` run, and
//! `scripts/check-config-registry-staleness.py` leads with the ratio. As of the
//! 2026-09-08 coverage sweep it is roughly **five undated entries for every
//! dated one** — the sweep took the table from 114 entries to over 450 by
//! reading code, and reading code establishes what a bound DOES, never what its
//! value should BE.
//!
//! That is the honest state and not a defect to hide: an undated entry says
//! "nobody has measured this", which is strictly more than the silence it
//! replaced. What it must not do is get worse quietly, so `DATED_FLOOR` pins
//! the count of dated entries and `the_dated_count_only_rises` fails if a date
//! is ever lost — including the tempting loss, where an entry whose `rests_on`
//! went red is downgraded to `undated` instead of being re-derived.
//!
//! # How far to trust the judgement fields
//!
//! `name`, `module` and `value` are checked against the source, and
//! `Signal::None` iff `guarded_by` is enforced. **`protects` and `on_exceed`
//! are neither, and they are human judgement.** Read them as informed opinion
//! about the code, not as a verified property of it.
//!
//! There is a measurement rather than an assurance. The 2026-09-08 coverage
//! sweep had `quant_bool_model_sat.rs` read independently by two people: on
//! seven constants they agreed on those two fields **five times and disagreed
//! twice** (`Time`/`DeclineRoute` against `Soundness`/`RefuseUnknown`), both
//! resolved by hand at the call site. Three more constants
//! (`abv::MAX_ROW_ROUNDS`, `abv::MAX_ROW_SITES`,
//! `ufbv_online::MAX_INPUT_DAG_NODES`) were registered independently by two
//! lanes the same day and merged: **one agreed on both fields and two did
//! not.** Ten constants, seven agreements. Roughly **70 % independent
//! agreement**, on a small sample.
//!
//! That is not a reason to distrust the table — every disagreement above was
//! settled by reading the call site, and the wrong reading in each case was the
//! one that had not been measured firing. It is a reason to check the code
//! before quoting a `protects` or an `on_exceed` in an argument, and to
//! re-derive rather than inherit when one of them is load-bearing.
//!
//! # The ways this registry can be wrong, and what catches each
//!
//! A registry that cannot be wrong is worthless, so each failure mode has a
//! check that dies on it:
//!
//! | Failure | Caught by |
//! | --- | --- |
//! | An entry names a constant that no longer exists | `every_entry_names_a_live_constant` |
//! | A governing constant exists with no entry | `every_governing_constant_is_registered` |
//! | Two entries for one key, or an unsorted table | `registry_is_sorted_and_unique` |
//! | The table and its own source text disagree | `registry_len_matches_its_own_source` |
//! | A justification predates the code it protects | `scripts/check-config-registry-staleness.py` |
//!
//! The staleness check is the one that addresses the failure this module exists
//! for, and it is the one a Rust unit test cannot do: it asks `git` whether
//! anything an entry's justification **rests on** changed after the date that
//! justification was measured. See [`Justification::rests_on`].
//!
//! # Levers: what it costs to ASK about a value
//!
//! A registered value nobody can move is a value nobody measures. Measured
//! 2026-09-11, **74** entries protect [`Protects::Completeness`], refuse or
//! decline when crossed ([`OnExceed::RefuseUnknown`] / [`OnExceed::DeclineRoute`]
//! — these are the ones that can turn a decidable file into `unknown`), AND
//! carry an undated justification. Nearly every one had `env_override: None`,
//! so asking "does this bound decide the division?" cost a workspace rebuild.
//! That price is why none of them had been asked.
//!
//! 64 of those now carry a lever, wired through `axeyum_ir::config_lever`: the
//! compiled `const` is untouched and remains the value with nothing set, and
//! the decision sites read a cached accessor. The contract — unset is the
//! shipped value byte for byte, a malformed value is a hard error rather than a
//! silent fallback, and the read happens once per process — lives in that
//! module's docs.
//!
//! Two things this deliberately does NOT mean. It is **not** a licence to raise
//! a cap: of the three of these investigated on 2026-09-11, all three were
//! correct as shipped (`ABSOLUTE_CLAUSE_CEILING` rebuilt at 31x decided 4 of 4
//! refused files still `unknown`, burning 90 s instead of refusing in 30 s).
//! And a lever is **not** a date: an entry with an `env_override` and no
//! `measured_on` is still an unmeasured value, and [`undated_count`] still
//! counts it. The lever only makes the measurement cheap enough to take.
//!
//! `every_env_override_is_read_by_the_code` is what stops the field from
//! becoming decoration: an entry naming a variable no source reads is worse
//! than `None`, because an operator who sets it measures the shipped default
//! and reports it as the other arm.
//!
//! # Recording (off by default)
//!
//! [`ConfigTraceGuard`] follows the four opt-in, off-by-default guards this tree
//! already ships — `TheoryLayerStatsGuard`, [`crate::BvLayerStatsGuard`],
//! `DlOnlineStatsGuard`, `FrontDoorStatsGuard` — all wired to the single
//! existing `--trace` / `AXEYUM_TRACE=1` flag in `smtcomp_cli`. No new CLI
//! surface. With no guard constructed, [`note_consulted`] reads one thread-local
//! `Cell<bool>` and returns: nothing is allocated and no clock is read.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::sync::{Arc, Mutex, PoisonError};

/// What a bound is defending. Derived from what the **code** does when the
/// bound is crossed, never from what its comment says it is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Protects {
    /// Wall time: crossing it lets a search run longer, not allocate more.
    Time,
    /// Peak memory: crossing it allocates more.
    Memory,
    /// Crossing it could produce a wrong `sat`/`unsat`. Such a bound must be
    /// [`Signal::ToCaller`] or name a [`ConfigEntry::guarded_by`].
    Soundness,
    /// Crossing it forgoes a decision the solver could otherwise have made.
    Completeness,
    /// Crossing it lets a loop run forever on a pathological input.
    Termination,
}

/// What the code does when the bound is crossed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum OnExceed {
    /// Returns a first-class `Unknown` whose detail names the bound.
    RefuseUnknown,
    /// Declines this route; the dispatcher falls through to another.
    DeclineRoute,
    /// Caps the work and returns a result computed with less effort.
    Truncate,
    /// Drops constraints or changes mode, enlarging the model set. Read
    /// [`ConfigEntry::signal`] and [`ConfigEntry::guarded_by`] before assuming
    /// this is safe.
    Relax,
    /// An internal search event (restart, clause-database reduction) with no
    /// effect visible outside the search.
    SearchEvent,
}

/// Whether a caller can tell that the bound was crossed.
///
/// This field exists because `nia_linearize::MAX_CONGRUENCE_GROUPS` crosses
/// with **no branch and no signal**: `if infos.len() <= MAX_CONGRUENCE_GROUPS`
/// has no `else`, so the relaxed mode is indistinguishable from the closed one
/// at the call site. Its twin — same name, same value `48`, in `axeyum-rewrite`
/// — reports the same crossing as `ZeroDivisorCongruence::Omitted` and the
/// front door branches on it (ADR-1730). Two constants, one name, one value,
/// opposite signalling contracts, in two crates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Signal {
    /// The crossing is reported in the return type or the `Unknown` detail.
    ToCaller,
    /// The crossing changes behaviour with no branch and no signal. Legitimate
    /// only when [`ConfigEntry::guarded_by`] names what stops it becoming a
    /// wrong verdict.
    None,
    /// Crossing is the normal documented operating regime (a restart interval,
    /// a clause-database reduction), not an exceptional path.
    NotApplicable,
}

/// Something an entry's justification depends on: if this changed after the
/// justification was measured, the measurement describes a tree that no longer
/// exists.
///
/// # Do not check a dependency with `git log -G'fn <name>'`
///
/// It is the obvious command and it answers the wrong question. Measured
/// 2026-09-08 on `euf::MAX_ACKERMANN_CONGRUENCE_PAIRS`, the bound reported to
/// carry 52 of 58 `QF_UFLIA` losses: `git log -G'fn eliminate_functions'` over
/// the window since its 2026-06-24 measurement is **EMPTY**, while
/// `git log -G'eliminate_functions'` — the query
/// `scripts/check-config-registry-staleness.py` actually runs — finds **five**
/// commits, the last on 2026-09-07. The signature never moved; the body did,
/// and the body is what the measurement was of. A survey that asks about the
/// declaration line gets a clean bill of health on a justification that has
/// stopped describing the tree.
///
/// This is the field that would have caught `MAX_ONLINE_LRA_ATOMS`. Its
/// 2026-08-03 measurement named `AtomBuilder` normalization as the cost;
/// `MAX_LRA_CACHED_COEFFICIENTS` bounded that cost three days later. A
/// dependency naming that symbol turns thirteen months of silence into one
/// failing check.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Dependency {
    /// Repository-relative path whose history is queried.
    pub path: &'static str,
    /// A symbol within that path. `None` means the whole file counts.
    pub symbol: Option<&'static str>,
}

/// A concrete, resolvable thing an entry's justification **names**, whose
/// disappearance falsifies that justification even though no dependency's
/// history changed.
///
/// [`Dependency`] and `Basis` answer two different questions, and the
/// difference is the reason this type exists:
///
/// - `rests_on` asks *did the code this was measured against **change**?* —
///   a `git log -G<symbol>` question, which needs history and a date.
/// - `basis` asks *does the thing this reasoning **names** still exist?* — a
///   question about the tree as it is now, which needs neither.
///
/// The second question is the one that went unasked for a month.
/// `dpll_lia::MAX_PRE_SAT_ARITH_ATOMS` was justified, in prose, by "`BatSat`
/// allocate\[d\] past an 8 GiB process ceiling … before its cooperative
/// deadline poll" (`d599b682f`, 2026-08-08). ADR-1703 (`317be80fe`,
/// 2026-09-05) took `BatSat` off every shipping path and re-based
/// `IncrementalSat` — the exact object the bound protects — onto
/// `NativeIncrementalCdcl`. Not one line of `dpll_lia.rs` changed, so no
/// `rests_on` dependency could have fired; the justification simply stopped
/// describing anything. A `Basis::LiveSymbol` naming `batsat` inside
/// `crates/axeyum-cnf/src/lib.rs` would have gone red the day the ADR landed.
///
/// Each variant is checked by `scripts/check-admission-limit-basis.py`, which
/// exits 1 when any basis is gone.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Basis {
    /// An identifier the reasoning names, which must still occur in `in_path`.
    ///
    /// `in_path` is deliberately a **specific file or directory**, not the
    /// workspace: "`BatSat` exists somewhere in the tree" stays true forever
    /// behind an optional dev-dependency, while "`BatSat` is what
    /// `crates/axeyum-cnf/src/lib.rs`'s warm solver uses" is exactly the claim
    /// the bound rested on and exactly the claim that became false.
    LiveSymbol {
        /// The identifier as written at the site the reasoning points at.
        ident: &'static str,
        /// Repository-relative file or directory that must still contain it.
        in_path: &'static str,
    },
    /// A commit the reasoning cites, which must still exist and whose subject
    /// must still contain `subject_contains`.
    ///
    /// A rebased, amended or dropped commit turns a cited measurement into an
    /// unverifiable one, and a short sha silently resolving to a *different*
    /// commit is worse than a missing one.
    CommitSubject {
        /// The commit as cited, short or full.
        sha: &'static str,
        /// Text that must still appear in that commit's subject line.
        subject_contains: &'static str,
    },
    /// An ADR the bound implements, which must still exist and must not have
    /// been superseded, rejected or withdrawn.
    ///
    /// A bound whose deciding ADR was overturned is not automatically wrong,
    /// but it is automatically unjustified, and that is what this reports.
    AdrLive(&'static str),
    /// A document the measurement is written up in, which must still exist.
    DocPath(&'static str),
}

/// Where a bound's reasoning is written down, and when it was last measured.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Justification {
    /// An ADR id (`"ADR-1752"`), a doc path, or `"doc comment"`.
    pub location: &'static str,
    /// The date the cited measurement was **taken**, as `YYYY-MM-DD`. `None` is
    /// the honest answer for a value nobody has measured, and the count of
    /// `None`s is a headline number this registry reports.
    pub measured_on: Option<&'static str>,
    /// The commit the measurement was taken at, when the justification names one.
    pub measured_at_commit: Option<&'static str>,
    /// What the measurement rests on. A change to any of these after
    /// `measured_on` makes the justification stale, which
    /// `scripts/check-config-registry-staleness.py` reports.
    pub rests_on: &'static [Dependency],
    /// What the justification **names**, and what must therefore still exist
    /// for it to mean anything. Checked by
    /// `scripts/check-admission-limit-basis.py`; see [`Basis`] for why this is
    /// a different question from `rests_on`.
    ///
    /// Every dated entry carries at least one, enforced by
    /// `dated_justifications_declare_a_basis`. An undated entry carries none:
    /// there is no measurement for a basis to support.
    pub basis: &'static [Basis],
}

/// One governing value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConfigEntry {
    /// The exact identifier at the definition site. Unique across the registry
    /// only together with `module` — `MAX_CONGRUENCE_GROUPS` exists twice.
    pub name: &'static str,
    /// Repository-relative path of the definition site.
    pub module: &'static str,
    /// The literal exactly as written, so a reader can grep for it.
    pub value: &'static str,
    /// What the number counts. Stated literally ("atoms", "cross-products",
    /// "bytes"), because two gates metering one resource in different units is
    /// a defect this registry exists to make visible.
    pub unit: &'static str,
    /// What crossing it would endanger.
    pub protects: Protects,
    /// What the code does when it is crossed.
    pub on_exceed: OnExceed,
    /// Whether the caller can tell.
    pub signal: Signal,
    /// What stops an unsignalled crossing becoming a wrong verdict. Empty when
    /// `signal` is not [`Signal::None`].
    pub guarded_by: &'static str,
    /// Environment variable that overrides or switches this value at run time.
    pub env_override: Option<&'static str>,
    /// Where the reasoning lives and when it was measured.
    pub justification: Justification,
    /// Anything a reader needs that the fields above cannot carry.
    pub note: &'static str,
}

impl ConfigEntry {
    /// `module::name`, the registry's stable key. Sorting on this is what makes
    /// the emitted configuration deterministic — a public API promise this tree
    /// keeps everywhere, and the reason nothing here iterates a `HashMap`.
    #[must_use]
    pub fn key(&self) -> String {
        format!("{}::{}", self.module, self.name)
    }

    /// Whether this entry's justification carries a date at all.
    #[must_use]
    pub fn is_dated(&self) -> bool {
        self.justification.measured_on.is_some()
    }
}

/// A justification nobody has dated. The count of these is a headline number,
/// so the shorthand exists to make an undated entry as easy to write as a dated
/// one — an entry that is hard to write honestly gets written dishonestly.
const fn undated(location: &'static str) -> Justification {
    Justification {
        location,
        measured_on: None,
        measured_at_commit: None,
        rests_on: &[],
        basis: &[],
    }
}

/// A justification with a measurement date, the things that measurement rests
/// on, and the things it names.
///
/// `basis` is a required parameter rather than an optional field for the reason
/// the whole registry exists: a field that can be omitted is omitted. Every
/// dated entry states what its reasoning points at, and
/// `scripts/check-admission-limit-basis.py` asks whether that still exists.
const fn dated(
    location: &'static str,
    measured_on: &'static str,
    measured_at_commit: Option<&'static str>,
    rests_on: &'static [Dependency],
    basis: &'static [Basis],
) -> Justification {
    Justification {
        location,
        measured_on: Some(measured_on),
        measured_at_commit,
        rests_on,
        basis,
    }
}

/// The ADR a bound implements must still be live (not superseded or rejected).
const fn adr(id: &'static str) -> Basis {
    Basis::AdrLive(id)
}

/// The document a measurement is written up in must still exist.
const fn doc(path: &'static str) -> Basis {
    Basis::DocPath(path)
}

/// An identifier the reasoning names must still occur at the site it points at.
const fn live(ident: &'static str, in_path: &'static str) -> Basis {
    Basis::LiveSymbol { ident, in_path }
}

/// A cited commit must still exist and still say what it was cited for saying.
const fn commit(sha: &'static str, subject_contains: &'static str) -> Basis {
    Basis::CommitSubject {
        sha,
        subject_contains,
    }
}

/// A dependency on one symbol within a file.
///
/// The only constructor: every dependency in this registry is symbol-scoped.
/// A whole-file dependency ([`Dependency::symbol`] `None`) is representable and
/// the checker handles it, but no entry needs one, and a whole-file `git log`
/// on a 9,000-line dispatcher would report a change every day for reasons
/// unrelated to any single bound — so the constructor is deliberately absent
/// rather than available and untested.
const fn sym(path: &'static str, symbol: &'static str) -> Dependency {
    Dependency {
        path,
        symbol: Some(symbol),
    }
}

/// Every governing value this registry covers, sorted by [`ConfigEntry::key`].
///
/// The order is a public promise, not an accident: a run emits its
/// configuration from this slice, and a diff of two runs' output is only
/// meaningful if the order is fixed. Nothing here is derived from a `HashMap`,
/// so the emitted text does not depend on per-process hash seeding.
///
/// Coverage is per FILE, not global: `governed_files` lists the files this
/// registry claims to cover completely, and the coverage test requires every
/// constant in one of them to be registered here or named in `EXEMPT`. A file
/// absent from that list is simply not claimed — which is honest, where a
/// silently partial registry would not be.
pub static REGISTRY: &[ConfigEntry] = &[
    ConfigEntry {
        name: "INLINE_DEMAND_RANGES",
        module: "crates/axeyum-bv/src/lib.rs",
        value: "4",
        unit: "merged bit-demand ranges tracked inline before promoting to Full",
        protects: Protects::Time,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "promoting to `Full` only WIDENS which bits are treated as demanded (a conservative over-approximation of the whole width), so a lowered term is never missing a bit the search actually needs -- soundness is unaffected, only the width-narrowing optimization is forgone",
        env_override: None,
        justification: undated("doc comment"),
        note: "Doubles as the inline array size (`[BitRange; INLINE_DEMAND_RANGES]`) AND the promotion threshold (`if merged_len == INLINE_DEMAND_RANGES`) for `InlineBitDemand`'s small-vec-style range tracker. The two roles are the same field on purpose, but only the second is a policy choice.",
    },
    ConfigEntry {
        name: "MAX_GLUE_USED",
        module: "crates/axeyum-cnf/src/clause_db_policy.rs",
        value: "127",
        unit: "glue (LBD)",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Truncates the used-glue histogram [`TierEstimator`] computes tier1/tier2 percentile boundaries from; clauses above it land in the final bucket. A search-quality heuristic input, not an admission gate -- the SPEC's `SearchEvent`/`NotApplicable` class for CDCL tier bounds.",
    },
    ConfigEntry {
        name: "MAX_USED",
        module: "crates/axeyum-cnf/src/clause_db_policy.rs",
        value: "31",
        unit: "rounds of retained eligibility (saturating `used` counter)",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Per the module doc: \"it is the knob that decides how large the database grows.\" Both CaDiCaL and Kissat use the same reference value 31 (a 5-bit field).",
    },
    ConfigEntry {
        name: "TIER2_GRACE_USED",
        module: "crates/axeyum-cnf/src/clause_db_policy.rs",
        value: "MAX_USED - 1",
        unit: "used-counter value",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The \"one round of grace\" boundary for tier2 clauses, derived from MAX_USED rather than independently chosen.",
    },
    ConfigEntry {
        name: "DEFAULT_COVERING_CONFLICT_LIMIT",
        module: "crates/axeyum-cnf/src/cube.rs",
        value: "10_000",
        unit: "conflicts",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0543",
            "2026-08-22",
            None,
            &[sym(
                "crates/axeyum-cnf/src/cube.rs",
                "DEFAULT_COVERING_CONFLICT_LIMIT",
            )],
            &[adr("ADR-0543")],
        ),
        note: "Budget for the covering-formula proof step, which is small by construction.",
    },
    ConfigEntry {
        name: "DEFAULT_CUBE_CONFLICT_LIMIT",
        module: "crates/axeyum-cnf/src/cube.rs",
        value: "500_000",
        unit: "conflicts",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0543",
            "2026-08-22",
            None,
            &[sym(
                "crates/axeyum-cnf/src/cube.rs",
                "DEFAULT_CUBE_CONFLICT_LIMIT",
            )],
            &[adr("ADR-0543")],
        ),
        note: "Deliberately small: a cube that does not close within it is the signal that it needs re-splitting, not that the search failed.",
    },
    ConfigEntry {
        name: "MAX_PRODUCT_CUBE_SELECTORS",
        module: "crates/axeyum-cnf/src/cube.rs",
        value: "24",
        unit: "selector variables",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Caps 2^k cube expansion. Refuses with an error rather than declining, because reaching it means a caller mistake.",
    },
    ConfigEntry {
        name: "CACHE_DROP_INTERVAL_BYTES",
        module: "crates/axeyum-cnf/src/drat.rs",
        value: "64 * 1024 * 1024",
        unit: "bytes written between fadvise(DONTNEED) calls",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-15",
            Some("631c91e7a"),
            // NOT the constant itself. Named that way this entry reported
            // STALE against `b405da6ef`, a rustdoc-link fix that turned
            // ``[`CACHE_DROP_INTERVAL_BYTES`]`` into a plain code span in a doc
            // comment — a diff `git log -G` cannot tell from a code change.
            // `maybe_advise` is the batching this 2.9x measurement was of, and
            // it is what would have to change for the measurement to stop
            // describing the tree.
            &[sym("crates/axeyum-cnf/src/drat.rs", "fn maybe_advise")],
            &[commit(
                "631c91e7a",
                "drop written proof pages from page cache",
            )],
        ),
        note: "`self.written.saturating_sub(self.advised_through) >= CACHE_DROP_INTERVAL_BYTES` gates the page-cache-dropping writer's `fadvise` cadence. Doc cites a measurement: per-write-call granularity was 2.9x slower wall-clock on NFS. Keeps the worst-case resident footprint of a streamed proof write fixed rather than growing with proof size.",
    },
    ConfigEntry {
        name: "DRAT_CHECK_DEADLINE_INTERVAL",
        module: "crates/axeyum-cnf/src/drat.rs",
        value: "256",
        unit: "checked DRAT steps between wall-clock deadline reads",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Cadence, not a threshold that is itself crossed: a coarser interval lets the bounded DRAT checker overshoot the deadline by up to this many extra steps. Mirrors `proof_sat::DEADLINE_CHECK_INTERVAL`'s rationale (cited by name in this file's doc comment) at a 4x finer cadence.",
    },
    ConfigEntry {
        name: "MAX_STORED_VARIABLE_INDEX",
        module: "crates/axeyum-cnf/src/drat_backward.rs",
        value: "((u32::MAX - 1) / 2) as usize - 1",
        unit: "CNF variable index",
        protects: Protects::Soundness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`PlanBuilder::finish` returns `Err(DratError::Parse(..))` -- an Err that ends the route -- when `variable_count > MAX_STORED_VARIABLE_INDEX + 1`. Its own doc is explicit about the stakes: \"the failure it prevents -- a silently truncated literal ... would be a wrong answer, not a crash.\" Needs a proof over 2+ billion variables to reach.",
    },
    ConfigEntry {
        name: "DEFAULT_HEADROOM_DENOMINATOR",
        module: "crates/axeyum-cnf/src/drat_resource.rs",
        value: "5",
        unit: "denominator of the MemAvailable headroom fraction",
        protects: Protects::Memory,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0426",
            "2026-08-13",
            Some("8e84b2358"),
            &[sym(
                "crates/axeyum-cnf/src/drat_resource.rs",
                "DEFAULT_HEADROOM_DENOMINATOR",
            )],
            &[
                adr("ADR-0426"),
                commit("8e84b2358", "file-backed backward DRAT checking"),
            ],
        ),
        note: "With DEFAULT_HEADROOM_NUMERATOR forms the \"4/5 headroom fraction\" ADR-0426 names explicitly in its re-checkability table. `MemoryBudget::from_system` computes `mem_available_bytes / DENOMINATOR * NUMERATOR`, so this pair sets the effective budget `admits()` later compares against.",
    },
    ConfigEntry {
        name: "DEFAULT_HEADROOM_NUMERATOR",
        module: "crates/axeyum-cnf/src/drat_resource.rs",
        value: "4",
        unit: "numerator of the MemAvailable headroom fraction",
        protects: Protects::Memory,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0426",
            "2026-08-13",
            Some("8e84b2358"),
            &[sym(
                "crates/axeyum-cnf/src/drat_resource.rs",
                "DEFAULT_HEADROOM_NUMERATOR",
            )],
            &[
                adr("ADR-0426"),
                commit("8e84b2358", "file-backed backward DRAT checking"),
            ],
        ),
        note: "See DEFAULT_HEADROOM_DENOMINATOR (same pair, same ADR-0426 \"4/5 headroom fraction\").",
    },
    ConfigEntry {
        name: "FIXED_BYTES",
        module: "crates/axeyum-cnf/src/drat_resource.rs",
        value: "16 * 1024 * 1024",
        unit: "fixed per-run resident bytes",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0426",
            "2026-08-13",
            Some("8e84b2358"),
            &[sym("crates/axeyum-cnf/src/drat_resource.rs", "FIXED_BYTES")],
            &[
                adr("ADR-0426"),
                live(
                    "the_model_covers_what_the_file_backed_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
                live(
                    "the_model_covers_what_the_in_memory_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
            ],
        ),
        note: "One of `DratMemoryModel`'s per-route coefficients feeding `DratMemoryEstimate::estimated_bytes`, which `MemoryBudget::admits` compares against the budget and returns `Err(DratResourceDecline)` -- surfaced to callers as `BackwardCheckOutcome::Declined`, a first-class outcome, never confused with a refuted proof. `tests/drat_memory_model.rs` re-derives the whole model from live runs on every test invocation rather than trusting the constants.",
    },
    ConfigEntry {
        name: "LITERALS_PER_STEP",
        module: "crates/axeyum-cnf/src/drat_resource.rs",
        value: "15",
        unit: "literal occurrences per step",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0426",
            "2026-08-13",
            Some("8e84b2358"),
            &[sym(
                "crates/axeyum-cnf/src/drat_resource.rs",
                "LITERALS_PER_STEP",
            )],
            &[
                adr("ADR-0426"),
                live(
                    "the_model_covers_what_the_file_backed_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
                live(
                    "the_model_covers_what_the_in_memory_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
            ],
        ),
        note: "Measured at 12.7, 14.5, 16.0 and 15.2 on the four largest committed certificates; 15 (near the mean) is used. Feeds `DratProofShape::from_proof_bytes`, the coarsest (byte-length-only) shape estimate, which then feeds the same admission chain as FIXED_BYTES.",
    },
    ConfigEntry {
        name: "MINIMUM_SAMPLE_BYTES",
        module: "crates/axeyum-cnf/src/drat_resource.rs",
        value: "1 << 20",
        unit: "bytes",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-13",
            Some("8e84b2358"),
            &[sym(
                "crates/axeyum-cnf/src/drat_resource.rs",
                "MINIMUM_SAMPLE_BYTES",
            )],
            &[commit("8e84b2358", "file-backed backward DRAT checking")],
        ),
        note: "`fraction.max(Self::MINIMUM_SAMPLE_BYTES)` -- a literal `.max` call per the SPEC's own governing-value test. A floor, not a ceiling: ensures `recommended_sample_bytes` never samples too little of a small proof to be within the doc's stated error table. Feeds `DratShapeSource::Sampled { sampled_bytes }`, which is part of the returned shape's provenance.",
    },
    ConfigEntry {
        name: "PLAN_BYTES_PER_CLAUSE",
        module: "crates/axeyum-cnf/src/drat_resource.rs",
        value: "150",
        unit: "bytes per clause record in the backward checker's plan",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0426",
            "2026-08-13",
            Some("8e84b2358"),
            &[sym(
                "crates/axeyum-cnf/src/drat_resource.rs",
                "PLAN_BYTES_PER_CLAUSE",
            )],
            &[
                adr("ADR-0426"),
                live(
                    "the_model_covers_what_the_file_backed_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
                live(
                    "the_model_covers_what_the_in_memory_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
            ],
        ),
        note: "Doc cites `size_of::<ClauseRecord>() == 40` doubling to 80 plus the deletion index's 66, measured at 134 bytes/record actual fill on `PHP(8, 7)` against 146 worst-fill -- 150 is the worst-fill-rounded value used.",
    },
    ConfigEntry {
        name: "PLAN_BYTES_PER_LITERAL",
        module: "crates/axeyum-cnf/src/drat_resource.rs",
        value: "8",
        unit: "bytes per literal occurrence in the plan's clause arena",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0426",
            "2026-08-13",
            Some("8e84b2358"),
            &[sym(
                "crates/axeyum-cnf/src/drat_resource.rs",
                "PLAN_BYTES_PER_LITERAL",
            )],
            &[
                adr("ADR-0426"),
                live(
                    "the_model_covers_what_the_file_backed_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
                live(
                    "the_model_covers_what_the_in_memory_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
            ],
        ),
        note: "4 bytes per packed literal code with doubling slack, worst-fill 8. Measured 7.23 actual on `PHP(8, 7)` (458,752 bytes / 63,409 literals).",
    },
    ConfigEntry {
        name: "PLAN_BYTES_PER_STEP",
        module: "crates/axeyum-cnf/src/drat_resource.rs",
        value: "16",
        unit: "bytes per proof step in the plan's step-to-record maps",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0426",
            "2026-08-13",
            Some("8e84b2358"),
            &[sym(
                "crates/axeyum-cnf/src/drat_resource.rs",
                "PLAN_BYTES_PER_STEP",
            )],
            &[
                adr("ADR-0426"),
                live(
                    "the_model_covers_what_the_file_backed_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
                live(
                    "the_model_covers_what_the_in_memory_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
            ],
        ),
        note: "Measured at 65,536 bytes for 6,153 steps on `PHP(8, 7)` (4-byte map entries with doubling slack).",
    },
    ConfigEntry {
        name: "RECOMMENDED_SAMPLE_FRACTION",
        module: "crates/axeyum-cnf/src/drat_resource.rs",
        value: "0.05",
        unit: "fraction of proof bytes sampled",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-13",
            Some("8e84b2358"),
            &[sym(
                "crates/axeyum-cnf/src/drat_resource.rs",
                "RECOMMENDED_SAMPLE_FRACTION",
            )],
            &[commit("8e84b2358", "file-backed backward DRAT checking")],
        ),
        note: "`DratProofShape::sample`'s doc carries a 4-certificate error table by sample fraction; at 5% the max observed error was +11%. The bias is deliberately toward over-estimating: \"a 0.1% sample declines checks that would have fitted, rather than admitting checks that will not.\" Result carries `DratShapeSource::Sampled`, visible to the caller.",
    },
    ConfigEntry {
        name: "STEP_VECTOR_BYTES_PER_LITERAL",
        module: "crates/axeyum-cnf/src/drat_resource.rs",
        value: "12",
        unit: "bytes per literal held in a Vec<DratStep>",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0426",
            "2026-08-13",
            Some("8e84b2358"),
            &[sym(
                "crates/axeyum-cnf/src/drat_resource.rs",
                "STEP_VECTOR_BYTES_PER_LITERAL",
            )],
            &[
                adr("ADR-0426"),
                live(
                    "the_model_covers_what_the_in_memory_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
            ],
        ),
        note: "`size_of::<CnfLit>() == 8`; a `Vec` grown by `push` averages ~1.4x length over a uniform clause-size spread, giving ~12. Only the InMemoryBackward route (`Vec<DratStep>` resident) pays this.",
    },
    ConfigEntry {
        name: "STEP_VECTOR_BYTES_PER_STEP",
        module: "crates/axeyum-cnf/src/drat_resource.rs",
        value: "48",
        unit: "bytes per step held in a Vec<DratStep>",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0426",
            "2026-08-13",
            Some("8e84b2358"),
            &[sym(
                "crates/axeyum-cnf/src/drat_resource.rs",
                "STEP_VECTOR_BYTES_PER_STEP",
            )],
            &[
                adr("ADR-0426"),
                live(
                    "the_model_covers_what_the_in_memory_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
            ],
        ),
        note: "The enum itself (32 bytes: discriminant + Vec header) plus one heap allocation per clause at glibc's 16-byte bookkeeping cost. Only the InMemoryBackward route pays this.",
    },
    ConfigEntry {
        name: "TEXT_BYTES_PER_LITERAL",
        module: "crates/axeyum-cnf/src/drat_resource.rs",
        value: "4",
        unit: "bytes of textual DRAT per literal occurrence",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0426",
            "2026-08-13",
            Some("8e84b2358"),
            &[sym(
                "crates/axeyum-cnf/src/drat_resource.rs",
                "TEXT_BYTES_PER_LITERAL",
            )],
            &[
                adr("ADR-0426"),
                live(
                    "the_model_covers_what_the_file_backed_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
                live(
                    "the_model_covers_what_the_in_memory_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
            ],
        ),
        note: "Measured at 4.31, 4.30, 4.07 and 4.31 on the four largest certificates; 4 (an under-estimate of the true mean) is used deliberately because it over-estimates memory, \"which is the safe direction.\" Also used by `DratProofShape::of_steps`/`from_proof_bytes` for the byte-length-only estimate.",
    },
    ConfigEntry {
        name: "TEXT_BYTES_PER_STEP",
        module: "crates/axeyum-cnf/src/drat_resource.rs",
        value: "3",
        unit: "bytes of textual DRAT per step beyond its literals",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0426",
            "2026-08-13",
            Some("8e84b2358"),
            &[sym(
                "crates/axeyum-cnf/src/drat_resource.rs",
                "TEXT_BYTES_PER_STEP",
            )],
            &[
                adr("ADR-0426"),
                live(
                    "the_model_covers_what_the_file_backed_route_actually_holds",
                    "crates/axeyum-cnf/tests/drat_memory_model.rs",
                ),
            ],
        ),
        note: "The `0` terminator, its space, and the newline -- a fixed per-step text overhead, exact rather than measured.",
    },
    ConfigEntry {
        name: "DEFAULT_MAX_CLAUSES",
        module: "crates/axeyum-cnf/src/inprocess.rs",
        value: "16_000_000",
        unit: "clauses",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Admission bound on inprocessing; reports `stats.skipped_size = true` and returns the formula unchanged.",
    },
    ConfigEntry {
        name: "DEFAULT_MAX_VARIABLES",
        module: "crates/axeyum-cnf/src/inprocess.rs",
        value: "4_000_000",
        unit: "CNF variables",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Occurrence lists must fit one pass. Mirrors `sat_bv_backend`'s `INPROCESS_MAX_VARIABLES`; the two are not linked in code.",
    },
    ConfigEntry {
        name: "INTERNAL_AND_FLATTEN_NODE_LIMIT",
        module: "crates/axeyum-cnf/src/lib.rs",
        value: "64",
        unit: "AND-tree nodes admitted to one bounded flattening",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "declining the flattening leaves the AND-tree to the ordinary per-gate Tseitin encoding, which is always equisatisfiable -- skipping the optimization can only change clause count, never the verdict",
        env_override: None,
        justification: undated("no written justification"),
        note: "`if self.internal_and_nodes.len() >= INTERNAL_AND_FLATTEN_NODE_LIMIT { return None; }` inside the bounded internal-AND traversal `try_flatten_internal_positive_and` uses to admit a flattening. A pure clause-count optimization, not a correctness bound.",
    },
    ConfigEntry {
        name: "LRAT_ELABORATE_DEADLINE_INTERVAL",
        module: "crates/axeyum-cnf/src/lrat.rs",
        value: "64",
        unit: "processed DRAT steps between wall-clock deadline reads",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Deliberately finer than `crate::drat`'s analogous (private) DRAT_CHECK_DEADLINE_INTERVAL (256): \"a single elaboration step is typically far more expensive than a single DRAT check step, and a coarser cadence would let the deadline overshoot by more wall time per check.\"",
    },
    ConfigEntry {
        name: "BLOCKING_MARGIN",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "1.40",
        unit: "trail-length / slow-trail-EMA ratio",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Glucose blocking-restart threshold: `trail_len > BLOCKING_MARGIN * trail_slow` suppresses an otherwise-due restart. Search-quality heuristic only.",
    },
    ConfigEntry {
        name: "CLAUSE_DECAY",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "0.999",
        unit: "clause-bump growth divisor per conflict",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Clause-activity decay for the deletion tie-break. Duplicated (different value) in `lra_online.rs`'s registered `VSIDS_DECAY`-style entries; this module's own `xor_cdcl.rs` has no CLAUSE_DECAY analogue (it uses a constant CLAUSE_ACTIVITY_BUMP with no decay instead).",
    },
    ConfigEntry {
        name: "CLAUSE_RESCALE",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "1e-20",
        unit: "clause activity multiplier",
        protects: Protects::Soundness,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`Soundness` here is arithmetic soundness of the f64 heuristic (overflow avoidance), not of the sat/unsat verdict -- matching the precedent set by `lra_online::VSIDS_RESCALE`.",
    },
    ConfigEntry {
        name: "CLAUSE_RESCALE_LIMIT",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "1e20",
        unit: "clause activity score",
        protects: Protects::Soundness,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The trigger for the CLAUSE_RESCALE above, avoiding f64 overflow of clause activities on long runs.",
    },
    ConfigEntry {
        name: "DEADLINE_CHECK_INTERVAL",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "1_024",
        unit: "conflicts (or theory steps) between wall-clock deadline reads",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Cadence, not itself a crossed threshold: bounds how much a search can overshoot a deadline before the next check. Also read on an iteration cadence for CDCL(T) so a theory that propagates without ever conflicting still gets a bounded deadline check.",
    },
    ConfigEntry {
        name: "DEFAULT_PROOF_SAT_CONFLICT_LIMIT",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "2_000_000",
        unit: "conflicts",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`self.conflicts > max_conflicts` returns `ProofSolveOutcome::ResourceOut` (\"never a guessed verdict\"). This IS the shipping SAT engine's default budget since ADR-1703. `max_conflicts == 0` is the documented \"encode but do not solve\" convention used elsewhere in the tree.",
    },
    ConfigEntry {
        name: "EMA_RESTART_WARMUP",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "100",
        unit: "conflicts",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Conflict warmup before the glue-EMA restart rule engages, so the slow average is meaningful before it is trusted.",
    },
    ConfigEntry {
        name: "GLUE_EMA_FAST_ALPHA",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "0.031_25",
        unit: "EMA smoothing rate (2^-5)",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Glucose/CaDiCaL T1.3.2 EMA glue-restart fast average. Standard reference smoothing rate, not independently measured against this codebase's corpus.",
    },
    ConfigEntry {
        name: "GLUE_EMA_SLOW_ALPHA",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "6.103_515_625e-5",
        unit: "EMA smoothing rate (2^-14)",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Glucose/CaDiCaL T1.3.2 EMA glue-restart slow (baseline) average. Same numeric value as TRAIL_EMA_ALPHA in this file, spelled separately because they smooth different quantities.",
    },
    ConfigEntry {
        name: "LUBY_UNIT",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "100",
        unit: "conflicts",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Restart cadence unit. Duplicated (same value) in the registered `lra_online::LUBY_UNIT` entry, which already notes four independent copies across the workspace including this one and `xor_cdcl.rs`'s `RESTART_UNIT`.",
    },
    ConfigEntry {
        name: "MIN_RESTART_INTERVAL",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "50",
        unit: "conflicts",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Anti-thrash floor: minimum conflicts between two EMA-triggered restarts.",
    },
    ConfigEntry {
        name: "RESTART_MARGIN",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "1.25",
        unit: "fast-glue-EMA / slow-glue-EMA ratio",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Forces a restart when `glue_fast > RESTART_MARGIN * glue_slow` -- recent search is producing less-reusable clauses.",
    },
    ConfigEntry {
        name: "THEORY_STEP_BUDGET",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "16_000_000",
        unit: "theory search-loop iterations",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`if self.theory_steps > THEORY_STEP_BUDGET { return Ok(SearchOutcome::Interrupted); }`. Defense-in-depth ONLY when a theory is attached (`T::HAS_THEORY`): \"the theories this core will drive are incomplete and non-monotone ... and a theory that ... propagates ... on every round would otherwise loop with no conflict to count.\" Compiled out entirely for NullTheory.",
    },
    ConfigEntry {
        name: "TRAIL_EMA_ALPHA",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "6.103_515_625e-5",
        unit: "EMA smoothing rate (2^-14)",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Glucose blocking-restart trail-depth EMA. Same numeric value as GLUE_EMA_SLOW_ALPHA in this file (2^-14 is the shared long-run smoothing rate), spelled as a separate constant because it smooths a different quantity.",
    },
    ConfigEntry {
        name: "VSIDS_DECAY",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "0.95",
        unit: "activity multiplier per conflict",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "MiniSat-scheme VSIDS decay. Same value as the registered `lra_online::VSIDS_DECAY` and this workspace's `xor_cdcl::VSIDS_DECAY` -- three independent copies.",
    },
    ConfigEntry {
        name: "VSIDS_RESCALE",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "1e-100",
        unit: "activity multiplier",
        protects: Protects::Soundness,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`Soundness` is arithmetic soundness of the VSIDS heuristic (f64 overflow avoidance), not of the verdict -- same reasoning as the registered `lra_online::VSIDS_RESCALE`. Same value as `xor_cdcl::VSIDS_RESCALE`.",
    },
    ConfigEntry {
        name: "VSIDS_RESCALE_LIMIT",
        module: "crates/axeyum-cnf/src/proof_sat.rs",
        value: "1e100",
        unit: "activity score",
        protects: Protects::Soundness,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The trigger for VSIDS_RESCALE above. Same value as `xor_cdcl::VSIDS_RESCALE_LIMIT` and the registered `lra_online::VSIDS_RESCALE_LIMIT`.",
    },
    ConfigEntry {
        name: "SUBSUME_CLAUSE_LIMIT",
        module: "crates/axeyum-cnf/src/simplify.rs",
        value: "100",
        unit: "literals per clause",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "subsumption only deletes clauses, so the formula stays model-preserving whatever is skipped",
        env_override: None,
        justification: undated("doc comment"),
        note: "Mirrors CaDiCaL `subsumeclslim`. Longer clauses are kept but excluded from subsumption candidacy.",
    },
    ConfigEntry {
        name: "SUBSUME_MAX_ROUNDS",
        module: "crates/axeyum-cnf/src/simplify.rs",
        value: "32",
        unit: "fixpoint rounds",
        protects: Protects::Termination,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "stopping early leaves a still model-preserving formula",
        env_override: None,
        justification: undated("doc comment"),
        note: "Hard cap for pathological inputs; the fixpoint normally converges well below it.",
    },
    ConfigEntry {
        name: "SUBSUME_OCCURRENCE_LIMIT",
        module: "crates/axeyum-cnf/src/simplify.rs",
        value: "1_000",
        unit: "occurrence-list entries",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "an unconnected clause is simply not a subsumption candidate",
        env_override: None,
        justification: undated("doc comment"),
        note: "Mirrors CaDiCaL `subsumeocclim`.",
    },
    ConfigEntry {
        name: "CLAUSE_ACTIVITY_BUMP",
        module: "crates/axeyum-cnf/src/xor_cdcl.rs",
        value: "1.0",
        unit: "activity bump per conflict participation",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Constant bump with no decay, unlike `proof_sat.rs`'s decaying CLAUSE_DECAY scheme: \"keeps the policy deterministic and cheap; the dominant deletion key is LBD, with activity only the tie-break.\"",
    },
    ConfigEntry {
        name: "GLUE_LBD",
        module: "crates/axeyum-cnf/src/xor_cdcl.rs",
        value: "2",
        unit: "LBD",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Glucose glue-clause cutoff: clauses at or below this LBD are never deleted. Same value and role as the registered `lra_online::GLUE_LBD`.",
    },
    ConfigEntry {
        name: "MAX_CONFLICTS",
        module: "crates/axeyum-cnf/src/xor_cdcl.rs",
        value: "2_000_000",
        unit: "conflicts",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"Maximum conflicts before the solver gives up (safety valve -> Unknown)\": `if self.conflicts > MAX_CONFLICTS` returns `XorCdclResult::Unknown`. This route is documented as deliberately isolated from production dispatch (ADR-0035 XorGaussian trust hole) -- registered because the constant governs regardless of wiring status.",
    },
    ConfigEntry {
        name: "REDUCE_FIRST",
        module: "crates/axeyum-cnf/src/xor_cdcl.rs",
        value: "2_000",
        unit: "learned clauses",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Clause-database reduction schedule base. Same value as the registered `lra_online::REDUCE_FIRST`, which already notes duplication \"across four CDCL cores in this workspace\" -- this is one of them.",
    },
    ConfigEntry {
        name: "REDUCE_INCREMENT",
        module: "crates/axeyum-cnf/src/xor_cdcl.rs",
        value: "300",
        unit: "learned clauses",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Reduction schedule growth per reduce round. Same value as the registered `lra_online::REDUCE_INC`, which spells the identical concept under a different name -- same note applies: \"same value, different name, no link.\"",
    },
    ConfigEntry {
        name: "RESTART_UNIT",
        module: "crates/axeyum-cnf/src/xor_cdcl.rs",
        value: "100",
        unit: "conflicts",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Luby restart cadence unit. Same value as `proof_sat::LUBY_UNIT` and the registered `lra_online::LUBY_UNIT` under a different name -- a fourth copy of the workspace's restart-cadence constant.",
    },
    ConfigEntry {
        name: "VSIDS_DECAY",
        module: "crates/axeyum-cnf/src/xor_cdcl.rs",
        value: "0.95",
        unit: "activity multiplier per conflict",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Same value as `proof_sat::VSIDS_DECAY` and the registered `lra_online::VSIDS_DECAY`.",
    },
    ConfigEntry {
        name: "VSIDS_RESCALE",
        module: "crates/axeyum-cnf/src/xor_cdcl.rs",
        value: "1e-100",
        unit: "activity multiplier",
        protects: Protects::Soundness,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`Soundness` is arithmetic soundness of the heuristic, not of the verdict. Same value as `proof_sat::VSIDS_RESCALE` and the registered `lra_online::VSIDS_RESCALE`.",
    },
    ConfigEntry {
        name: "VSIDS_RESCALE_LIMIT",
        module: "crates/axeyum-cnf/src/xor_cdcl.rs",
        value: "1e100",
        unit: "activity score",
        protects: Protects::Soundness,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Same value as `proof_sat::VSIDS_RESCALE_LIMIT` and the registered `lra_online::VSIDS_RESCALE_LIMIT`.",
    },
    ConfigEntry {
        name: "STEP_BUDGET",
        module: "crates/axeyum-cnf/src/xor_dpll.rs",
        value: "2_000_000",
        unit: "propagation/decision steps",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"Reaching this cap yields `XorDpllResult::Unknown`, keeping the decider total and non-hanging.\" This module is explicitly the correctness-first (not production) decider for the CDCL(XOR) integration slice.",
    },
    ConfigEntry {
        name: "MAX_XOR_WIDTH",
        module: "crates/axeyum-cnf/src/xor_drat.rs",
        value: "16",
        unit: "variables in one XOR constraint of the conflict subset",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`xor_gauss_drat_refutation` returns `None` above the cap rather than build the `2^(k-1)`-clause encoding of a wide constraint. \"Declining is sound: it produces no false certificate, it simply leaves that query at the prior search-only assurance\" (the ADR-0035 XorGaussian trust hole). Not yet called from production dispatch (only tests), but governs the function's own contract regardless.",
    },
    ConfigEntry {
        name: "MAX_XOR_VARS",
        module: "crates/axeyum-cnf/src/xor_extract.rs",
        value: "8",
        unit: "variables in one candidate XOR gate",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "an un-recognized XOR gate's clauses remain ordinary CNF clauses in the formula, so a skipped gate can only forgo the extra propagation strength the XOR accelerator would have given it -- it can never remove a clause or produce a wrong verdict; the module doc states this directly: \"false negatives are safe, false positives would be a soundness bug\"",
        env_override: None,
        justification: undated("doc comment"),
        note: "Gates wider than this are \"simply not recognized.\" CryptoMiniSat caps its analogous search the same way, per the doc comment.",
    },
    ConfigEntry {
        name: "MAX_CANDIDATE_SUBSTITUTIONS",
        module: "crates/axeyum-egraph/src/lib.rs",
        value: "65_536",
        unit: "substitutions",
        protects: Protects::Memory,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "fewer matches means fewer instantiations, so at worst `unknown`; no refutation can be manufactured",
        env_override: None,
        justification: undated("doc comment"),
        note: "Bounds aggregate blow-up across many individually modest patterns, which the per-position frontier cap cannot see.",
    },
    ConfigEntry {
        name: "MAX_MATCH_FRONTIER",
        module: "crates/axeyum-egraph/src/lib.rs",
        value: "4096",
        unit: "e-graph nodes",
        protects: Protects::Memory,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "fewer matches means fewer instantiations, so at worst `unknown`",
        env_override: None,
        justification: undated("doc comment"),
        note: "From a production incident: an unbounded frontier drove one UFLIA query to 15.8 GB / 150 s where the capped run is 305 MB / 3.3 s. The incident file is named in the doc comment; the date is not.",
    },
    ConfigEntry {
        name: "MAX_MATCH_WORK_PER_BATCH",
        module: "crates/axeyum-egraph/src/lib.rs",
        value: "20_000_000",
        unit: "matching-work units",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "stopping early yields fewer matches, hence at worst `unknown`",
        env_override: None,
        justification: undated("doc comment"),
        note: "Bounds pathological FAILED matching, which an output cap structurally cannot catch: one batch spent 44 s against a 2 s budget while producing nothing.",
    },
    ConfigEntry {
        name: "ALPHA_EQUIVALENCE_STEP_BUDGET",
        module: "crates/axeyum-rewrite/src/alpha.rs",
        value: "100_000",
        unit: "node comparisons",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The comparison walk is exponential in the worst case over a DAG; exhausting the budget returns `false` directly (the function's own return value IS the signal) - 'a decline, never an accept ... can never trade away soundness' per the doc.",
    },
    ConfigEntry {
        name: "MAX_ARRAY_EQ_INDEX_BITS",
        module: "crates/axeyum-rewrite/src/arrays.rs",
        value: "8",
        unit: "index bits",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_MAX_ARRAY_EQ_INDEX_BITS"),
        justification: undated("doc comment"),
        note: "Bounds eager array-equality expansion over 2^iw indices and the O(n^2) Ackermann pairing behind it. Refuses as `ArrayElimError::Unsupported`.",
    },
    ConfigEntry {
        name: "AC_REBUILD_MAX_OPERANDS",
        module: "crates/axeyum-rewrite/src/canonical.rs",
        value: "64",
        unit: "AC operands",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the flatten/sort/rebuild step is skipped (not altered) above the cap, so the caller's original argument order is kept unchanged and denotation is preserved by construction - quoting commit d528b8926: \"a rewrite that is skipped, never one that is changed\"",
        env_override: None,
        justification: undated("doc comment"),
        note: "A real 2026-08-02 measurement exists (`d528b8926`: 16 ops solved `bench_6444` but lost `div3.c.50.smt2`'s 20.4s `sat`; 64 keeps both, deciding `div3.c.50` in 10.7s, plus a 200-file QF_BV parity sweep at zero verdict regressions) and this entry is deliberately NOT dated to it. `550b2c1f1` (2026-08-09) moved the bound from a post-hoc `flat.len() > AC_REBUILD_MAX_OPERANDS` check into an early abort inside `flatten_ac_bounded`, so the measurement describes a shape that no longer exists — the staleness checker said so, and re-dating it would have been moving the date rather than re-taking the measurement. Re-deriving it against `flatten_ac_bounded` is owed. Below the cap, wide `bvadd` AC chains keep their left-associated shape instead of being rebuilt balanced, which is what let unit propagation walk the shared-prefix relation.",
    },
    ConfigEntry {
        name: "DEFAULT_LOCAL_REWRITE_FUEL",
        module: "crates/axeyum-rewrite/src/canonical.rs",
        value: "8",
        unit: "local rule re-applications per node",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Exhausting it returns the exact partially canonicalized term (never a wrong one) and increments `RewriteReport::local_fuel_exhaustions`, a caller-visible counter.",
    },
    ConfigEntry {
        name: "DENOTATION_GUARD_MAX_BV_WIDTH",
        module: "crates/axeyum-rewrite/src/canonical.rs",
        value: "128",
        unit: "bit-vector width",
        protects: Protects::Soundness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Above this width a symbol is left unbound in the denotation-guard sample, which the audit explicitly counts as unchecked rather than checked-and-passed - the distinction is caller-visible, not silently dropped.",
    },
    ConfigEntry {
        name: "DENOTATION_GUARD_SAMPLES",
        module: "crates/axeyum-rewrite/src/canonical.rs",
        value: "4",
        unit: "concrete assignments per denotation check",
        protects: Protects::Soundness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The default `PreconditionPolicy::Denotational` tier: every committed rewrite is evaluated on both sides under this many concrete assignments by an independent evaluator path, and any disagreement is a refusal, not a rewrite. Two fixed corners (all-zero, all-ones) plus seeded pseudorandom fill; the doc is explicit the two corners alone cannot discriminate a confused application. Coverage is reported (see `denotation_guard_actually_covers_the_applications_it_reports`), satisfying the `Signal::ToCaller` requirement this file's own doc places on `Protects::Soundness`.",
    },
    ConfigEntry {
        name: "MAX_ROUNDS",
        module: "crates/axeyum-rewrite/src/elim_unconstrained.rs",
        value: "8",
        unit: "occurrence-graph rebuild rounds",
        protects: Protects::Termination,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the pass is a sound term-preserving simplification at every round; stopping early only leaves some unconstrained variables un-eliminated, never changes the term's denotation (a round that eliminates nothing already ends the pass through its own convergence check, so this cap is only a safety valve for a round that keeps eliminating without settling)",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"Z3 caps the equivalent loop at 3\" - this file's own comment gives a cross-solver reference point for the value 8.",
    },
    ConfigEntry {
        name: "FUNCTION_ABSTRACTION_WITNESS_SAMPLES",
        module: "crates/axeyum-rewrite/src/functions.rs",
        value: "8",
        unit: "concrete assignments sampled",
        protects: Protects::Soundness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The independent reference check (ADR-1721 section 7, consumed by `axeyum-solver/src/euf.rs`) that any `unsat` derived through Ackermann function abstraction is faithful; the doc states plainly \"any `unsat` derived through it is unsound\" if the abstraction disagrees with a sample. Result is a `FunctionAbstractionWitness` struct the caller reads to decide whether to trust the abstraction. `crates/axeyum-rewrite/tests/function_abstraction_witness.rs:33` pins `FUNCTION_ABSTRACTION_WITNESS_SAMPLES > 2` as a compile-time assertion, since the two deterministic corner samples alone cannot discriminate a confused application.",
    },
    ConfigEntry {
        name: "MAX_INT_BLAST_WIDTH",
        module: "crates/axeyum-rewrite/src/int_blast.rs",
        value: "64",
        unit: "bit-vector width (bits)",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Keeps signed model read-back inside `i128`. Declining decides `unknown` for the integer problem, never `unsat`.",
    },
    ConfigEntry {
        name: "MAX_CONGRUENCE_GROUPS",
        module: "crates/axeyum-rewrite/src/int_divmod.rs",
        value: "48",
        unit: "zero-divisor dividend groups",
        protects: Protects::Soundness,
        on_exceed: OnExceed::Relax,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-1730",
            "2026-09-07",
            None,
            &[sym(
                "crates/axeyum-rewrite/src/int_divmod.rs",
                "MAX_CONGRUENCE_GROUPS",
            )],
            &[adr("ADR-1730")],
        ),
        note: "THE SIGNALLED TWIN. Crossing it is reported as `ZeroDivisorCongruence::Omitted` and `auto::guard_zero_divisor_sat` turns the resulting `sat` into `unknown`. Same name and same value as `nia_linearize::MAX_CONGRUENCE_GROUPS`, which signals nothing — see that entry.",
    },
    ConfigEntry {
        name: "MAX_NARROW_BV_WIDTH",
        module: "crates/axeyum-rewrite/src/inverter.rs",
        value: "128",
        unit: "bit-vector width",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`invert_bv_cmp` returns `Ok(None)` above the cap, which only means this specific inversion rule does not fire for that term; the general rewrite/solve dispatch falls through to whatever else applies, which stays sound independently of whether this shortcut fired",
        env_override: Some("AXEYUM_MAX_NARROW_BV_WIDTH"),
        justification: undated("doc comment"),
        note: "The doc names an alternative that exists but these boundary rules don't build it (\"constants above 128 bits need the wide representation, which several of the boundary rules below do not construct\"), so this is a real coverage gap, not a hard structural wall - unlike `MAX_SET_WIDTH`/`SEQ_TOTAL_BITS_CAP` (out of scope, see report) it is not literally forced by `u128`, since a wide representation is documented to exist elsewhere in the tree.",
    },
    ConfigEntry {
        name: "CHAIN_INSTANCE_CAP",
        module: "crates/axeyum-rewrite/src/quantifiers.rs",
        value: "4096",
        unit: "cartesian-product instances",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "an uninstantiated chain can only leave the query undecided",
        env_override: None,
        justification: undated("doc comment"),
        note: "Caps prenex universal-chain instantiation.",
    },
    ConfigEntry {
        name: "MATCH_CAP",
        module: "crates/axeyum-rewrite/src/quantifiers.rs",
        value: "4096",
        unit: "E-match substitutions",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "fewer instantiations can only lose a refutation, never invent one",
        env_override: None,
        justification: undated("doc comment"),
        note: "Backstop against equivalence-class blow-up during E-matching.",
    },
    ConfigEntry {
        name: "MAX_EXPAND_INSTANCES",
        module: "crates/axeyum-rewrite/src/quantifiers.rs",
        value: "1 << 20",
        unit: "ground instances",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "commit 5439bcdfb",
            "2026-06-24",
            Some("5439bcdfb"),
            &[
                sym("crates/axeyum-rewrite/src/quantifiers.rs", "expand_counted"),
                sym(
                    "crates/axeyum-rewrite/src/quantifiers.rs",
                    "MAX_EXPAND_INSTANCES",
                ),
            ],
            &[
                commit("5439bcdfb", "bound nested-forall expansion"),
                live("expand_counted", "crates/axeyum-rewrite/src/quantifiers.rs"),
            ],
        ),
        note: "Caps the nested-quantifier finite-domain expansion product; declines as `UnsupportedDomain` so the caller degrades to a bounded `unknown`.",
    },
    ConfigEntry {
        name: "QUANT_EXPAND_BIT_LIMIT",
        module: "crates/axeyum-rewrite/src/quantifiers.rs",
        value: "10",
        unit: "bits per quantified variable",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_QUANT_EXPAND_BIT_LIMIT"),
        justification: undated("doc comment"),
        note: "Largest single-variable BV domain (2^10) the expander will enumerate.",
    },
    ConfigEntry {
        name: "DEFAULT_SOLVE_EQS_FUEL",
        module: "crates/axeyum-rewrite/src/solve_eqs.rs",
        value: "5_000_000",
        unit: "DAG-node visits",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Signalled through `EqSolution::bailed()`. The doc records ~1.2 s on a 17.6 MB / 340k-node input but no date, so the measurement cannot be compared against the code.",
    },
    ConfigEntry {
        name: "MAX_SAFE_INT_LITERAL",
        module: "crates/axeyum-smtlib/src/bounded_completeness.rs",
        value: "1 << 20",
        unit: "integer literal magnitude",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Prevents `is_bounded_complete` from classifying a query as bounded-complete when a large literal could wrap the width-32 int-blast mod 2^32 and FLIP a comparison, fabricating a spurious bounded-`unsat` - the doc names this failure mode explicitly. The `bool` return of `is_bounded_complete` is the caller-visible signal; a `false` here means the front door does not upgrade a bounded no-model to a real `unsat`.",
    },
    ConfigEntry {
        name: "STRING_MAX_LEN",
        module: "crates/axeyum-smtlib/src/bounded_completeness.rs",
        value: "12",
        unit: "bytes",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "DIVERGENT-TWIN RISK: this is a hand-maintained copy of `parse.rs::STRING_MAX_LEN` (\"mirrors parse.rs::STRING_MAX_LEN\", same value 12, but a different type - `i128` here vs `u32` in `parse.rs`). If it drifted from the real packed-encoding cap it could make `is_bounded_complete` classify a query as bounded-complete when the actual encoding truncates differently, i.e. fabricate a wrong `unsat`. No test pins the two together (contrast `string_length_cert.rs::MAX_CODE_POINT`, whose twin IS pinned by a test).",
    },
    ConfigEntry {
        name: "EXACT_BOOLEAN_ATOM_CAP",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "10",
        unit: "distinct Boolean atoms",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "declining only skips the exact-rewrite truth-table proof for this term (an optional `unsat`/contradiction shortcut); it never fabricates a result, per this module's stated invariant on `EXACT_REWRITE_WORK_BUDGET`'s doc: \"Declining a source fact only removes an optional unsat shortcut; it can never invent one\"",
        env_override: None,
        justification: undated("no written justification"),
        note: "Bounds `exact_boolean_constant`'s exhaustive 2^n truth-table check (2^10 = 1024 rows at the cap). No doc comment sits on the const itself; the reasoning is inferred from the function it gates.",
    },
    ConfigEntry {
        name: "EXACT_ITE_CASE_CAP",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "64",
        unit: "ITE cases enumerated",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "same module-wide invariant as `EXACT_BOOLEAN_ATOM_CAP`: a `false` return from `exact_collect_ite_cases` only skips the exact-rewrite ITE-tree comparison, never fabricates a contradiction",
        env_override: None,
        justification: undated("no written justification"),
        note: "No doc comment on the const itself.",
    },
    ConfigEntry {
        name: "EXACT_REWRITE_DEPTH_CAP",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "64",
        unit: "recursion depth",
        protects: Protects::Memory,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "`ExactRewriteTerm::Opaque` (or the unchanged input term at the two non-entry call sites) never spuriously equals a `Bool`/literal value the proof search is looking for, so truncating only ever loses a chance to simplify, never fabricates one - BUT NOTE: only the depth==0 entry path (via `exact_rewrite_charge`, work-budget exhaustion) sets `EXACT_REWRITE_EXHAUSTED`; the two direct `depth > EXACT_REWRITE_DEPTH_CAP` checks in `exact_rewrite_under_assignment_facts`/`exact_rewrite_under_equality_facts` (around lines 13515, 13602) do NOT set that flag. Flagging this asymmetry for review rather than asserting it is safe or unsafe - see report.",
        env_override: None,
        justification: undated("no written justification"),
        note: "No doc comment on the const itself (unlike this file's other `MAX_*_DEPTH` constants). Consistent in role with `WORD_ATOM_MAX_DEPTH`/`MAX_TRIGGER_DEPTH`, both of which ARE documented as native-stack guards, so `Protects::Memory` is inferred by analogy, not read from a comment here.",
    },
    ConfigEntry {
        name: "EXACT_REWRITE_WORK_BUDGET",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "250_000",
        unit: "node visits",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "sets the thread-local `EXACT_REWRITE_EXHAUSTED` flag on exhaustion; `exact_rewrite_contradiction` consults `exact_rewrite_work_exhausted()` before treating a normal form as a proof, so a truncated normal form is never read as one",
        env_override: None,
        justification: undated("doc comment"),
        note: "Charged per node visit via `exact_rewrite_charge()`, reset at each top-level (`depth == 0`) entry so no assertion's result depends on a previous one's spend (a determinism promise).",
    },
    ConfigEntry {
        name: "FROM_INT_MAX_DIGITS",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "10",
        unit: "decimal digits",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Derived by hand from `DEFAULT_INT_WIDTH = 32` (2^31 - 1 < 10^10), NOT computed from it in code - the two constants must be kept consistent manually. `str.from_int` declines (`Unsupported`) rather than truncate when the decimal expansion needs more digits, so it is never a wrong string, only a missed one.",
    },
    ConfigEntry {
        name: "MAX_CODE_POINT",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "0x2FFFF",
        unit: "Unicode code point",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "DIVERGENT TWIN of `SMTLIB_MAX_CODE_POINT` (this file) and `string_length_cert.rs::MAX_CODE_POINT` - THREE named copies of the SMT-LIB `UnicodeStrings` max code point across two crates. This one is a function-local const inside `string_from_code`. The doc names the exact P0 history: `(= (str.from_code 200) \"\")` was wrongly `sat` (Z3: `unsat`) when this window folded to the empty string instead of declining; task #46. A constant `str.from_code` argument in `256..=0x2FFFF` now declines (`Unsupported`) rather than risk a wrong string.",
    },
    ConfigEntry {
        name: "MAX_DEPTH",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "2_048",
        unit: "paren-nesting depth",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`word_only_fallback_within_stack_budget` returning `false` (depth cap crossed) and `parse_word_only` itself returning `None` (fallback genuinely fails) both fall through to `Err(error)` - the SAME, unchanged original `SmtError` - so a caller cannot distinguish declined-for-depth from fallback-tried-and-failed, and either way no result is ever upgraded incorrectly",
        env_override: None,
        justification: undated("doc comment"),
        note: "Local `const` inside `word_only_fallback_within_stack_budget`, guarding a byte-level nesting scan used to decide whether the word-only source-level retry (an optional completeness improvement over the bounded-encoding error) is safe to attempt without exhausting the native stack.",
    },
    ConfigEntry {
        name: "MAX_DISTINCT_EXPANSION_PAIRS",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "65_536",
        unit: "pairwise disequalities",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Caps the `n(n-1)/2` pairwise expansion of SMT-LIB `distinct`; `Err(SmtError::ResourceLimit)` ends the route before the first pair is built. \"Generous enough ... including 256-way applications.\"",
    },
    ConfigEntry {
        name: "MAX_EQRANGE_POINTS",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "1024",
        unit: "finite-expansion points",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("no written justification"),
        note: "No doc comment on the const; the error message names it as \"eqrange finite expansion is capped at {N} points\".",
    },
    ConfigEntry {
        name: "MAX_FF_PRIME_BITS",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "16",
        unit: "modulus bits",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`ff.mul` bit-blasts a `2*MAX_FF_PRIME_BITS`-bit product before `bvurem` reduction, so this caps QF_FF bit-blast cost. \"Declining crypto-sized primes whose bit-blasting would blow up\" - declines with `Unsupported` at three call sites (around lines 17098, 17175, 17334).",
    },
    ConfigEntry {
        name: "MAX_TRIGGER_DEPTH",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "32",
        unit: "trigger-term nesting depth",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`build_trigger_term` returns `None`, which the quantifier machinery treats identically to any other unbuildable `:pattern` - falling back to auto-selected triggers, a documented-sound fallback whenever a user pattern can't be built for any reason",
        env_override: None,
        justification: undated("doc comment"),
        note: "`build_trigger_term` is genuinely recursive (\"the frame machine is not usable here\"), so this guards the native Rust stack against a hostile deeply-nested `:pattern`.",
    },
    ConfigEntry {
        name: "SEQ_INT_WIDTH",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "16",
        unit: "bits",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Element bit-width for a packed `(Seq Int)` sort. A wider width would admit larger `Int` element literals but cost more of the `SEQ_TOTAL_BITS_CAP` total-width budget; 16 is a policy trade-off, not forced by any type. \"An `Int` element literal outside the signed range is declined.\"",
    },
    ConfigEntry {
        name: "SEQ_LEN_SOFT_CAP",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "8",
        unit: "sequence elements",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"The analogue of STRING_MAX_LEN\" for packed `Seq` sorts. `seq.++`/etc. return `Err(SmtError::Unsupported)` when the summed result length exceeds it (two call sites, around lines 17704 and 18368), together with the separate `SEQ_TOTAL_BITS_CAP` structural check.",
    },
    ConfigEntry {
        name: "SMTLIB_MAX_CODE_POINT",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "0x2_FFFF",
        unit: "Unicode code point",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "DIVERGENT TWIN of `MAX_CODE_POINT` (this file, function-local in `string_from_code`) and `string_length_cert.rs::MAX_CODE_POINT` - three named copies of the same SMT-LIB spec constant. Used by `decode_string_code_points`, the single literal-escape decoder shared by `lib.rs`, `bounded_completeness.rs`, `regex.rs`, and `regex_membership.rs`; returns `None` above the cap, which every caller treats as a decline (never a truncated/wrong character).",
    },
    ConfigEntry {
        name: "SOURCE_FP_MAX_FIXPOINT_ROUNDS",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "32",
        unit: "fact-derivation rounds",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("no written justification"),
        note: "Bounds the fact-derivation fixpoint loop inside `source_fp_prefix_monotonic_unsat`, whose `bool` result is stored verbatim as the public `Script::source_fp_prefix_monotonic_unsat` field. Stopping early just means fewer facts are derived - the loop is not itself gated by a decline branch, it simply stops after N rounds and continues with whatever it has.",
    },
    ConfigEntry {
        name: "SOURCE_FP_MAX_NORMALIZED_NODES",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "512",
        unit: "normalized s-expression nodes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("no written justification"),
        note: "`source_fp_prefix_monotonic_unsat` returns `false` (stored in `Script::source_fp_prefix_monotonic_unsat`) when a normalized assertion exceeds this node count; the fast source-level FP contradiction shortcut is simply not attempted, eager FP lowering remains the (complete) fallback.",
    },
    ConfigEntry {
        name: "SOURCE_FP_MAX_NORMALIZE_DEPTH",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "64",
        unit: "recursion depth",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("no written justification"),
        note: "`normalize_source_fp_expr` is directly recursive over nested `let`; returns `None` above this depth, propagating to `Script::source_fp_prefix_monotonic_unsat = false`.",
    },
    ConfigEntry {
        name: "SOURCE_FP_MAX_NORMALIZE_WORK",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "100_000",
        unit: "emitted nodes",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"Deliberately far above SOURCE_FP_MAX_NORMALIZED_NODES: charging covers intermediate substitutions as well as the final tree.\" `budget.checked_sub(1)?` underflow propagates `None` the same way as the depth cap, into `Script::source_fp_prefix_monotonic_unsat = false`.",
    },
    ConfigEntry {
        name: "SPLIT_REPLACE_REJOIN_PACKED_LIMIT",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "64",
        unit: "split/replace/rejoin terms",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`admit_split_replace_rejoin=false` leaves `proved_concat_bound` on the pre-existing source-level fallback, which the doc states is \"both faster and more robust\" - never a wrong verdict, only forgoes the correlated-width packed encoding",
        env_override: None,
        justification: undated("doc comment"),
        note: "Above this, even the correlated-width encoding creates a very large term DAG.",
    },
    ConfigEntry {
        name: "STRING_BOUND_CAP",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "512",
        unit: "bytes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Hard ceiling on any packed string's `max_len`; also the upper clamp on a caller-supplied string-bound `floor` (`floor.clamp(STRING_MAX_LEN, STRING_BOUND_CAP)`). `str.replace`/`str.++` return `Err(SmtError::Unsupported)` when the result's bounded length would exceed it.",
    },
    ConfigEntry {
        name: "STRING_LITERAL_MAX_LEN",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "256",
        unit: "bytes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Adaptive per-symbol/literal bound, wider than the default `STRING_MAX_LEN` window but independent of it so one long protocol-token literal doesn't widen every unrelated string variable's CNF. `pack_string_literal` returns `Err(SmtError::Unsupported)` above it (ADR-0029).",
    },
    ConfigEntry {
        name: "STRING_MAX_LEN",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "12",
        unit: "bytes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "adaptive per-symbol widening (via `inferred_string_symbol_bounds`/`STRING_LITERAL_MAX_LEN`) is exact - no truncation or wraparound - so it only ever admits scripts a fixed 12-byte window would have declined; \"scripts whose literals all fit the old 13-byte cap produce byte-identical encodings\" per the doc on `STRING_LITERAL_MAX_LEN`",
        env_override: None,
        justification: undated("doc comment"),
        note: "DIVERGENT TWIN of `bounded_completeness.rs::STRING_MAX_LEN` (same value 12, different type - `u32` here vs `i128` there - and that file's doc explicitly calls itself a mirror of this one). The default packed per-symbol string length window; also the ladder's implicit first rung (see `axeyum-solver/src/smtlib.rs::DEFAULT_STRING_BOUND`, a THIRD, undocumented-as-linked copy of this same value).",
    },
    ConfigEntry {
        name: "WORD_ATOM_MAX_DEPTH",
        module: "crates/axeyum-smtlib/src/parse.rs",
        value: "512",
        unit: "recursion depth",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "returns `None`/`false` at three call sites (around lines 2456, 2801, 4372), which callers treat as this-optional-word-side-channel-optimization-does-not-apply-to-this-term; the doc calls the resulting all-or-nothing decline explicitly \"sound\"",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"The only recursion is through top-level `and`\" - guards the native Rust stack, reachable now that long-literal scripts parse bounded rather than being rejected outright.",
    },
    ConfigEntry {
        name: "MAX_LOOP_EXPANSION",
        module: "crates/axeyum-smtlib/src/regex.rs",
        value: "256",
        unit: "materialized re.loop copies",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`expand_loop` desugars `R{lo,hi}` by materializing copies, linear in the repetition count; declines (`Unsupported`) past the cap rather than blow up the NFA (ADR-0029).",
    },
    ConfigEntry {
        name: "MAX_NFA_STATES",
        module: "crates/axeyum-smtlib/src/regex.rs",
        value: "256",
        unit: "NFA states",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "A regex compiling past this declines as `SmtError::Unsupported` (\"a sound `unknown`\") rather than building a giant `reach[pos][state]` formula or hanging.",
    },
    ConfigEntry {
        name: "MAX_REGEX_SEXPR_DEPTH",
        module: "crates/axeyum-smtlib/src/regex.rs",
        value: "1024",
        unit: "s-expression nesting depth",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"Past this cap the process would abort with a stack overflow ... the failure mode fixed in `fcc8760d`\" (a commit named in the doc, but with no date given, so this stays undated rather than guessed). Declines through the existing `Unsupported`/`None` route, never as the empty language.",
    },
    ConfigEntry {
        name: "MAX_CANDIDATES",
        module: "crates/axeyum-solver/src/abduct.rs",
        value: "4096",
        unit: "candidate abducts",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_ABDUCT_MAX_CANDIDATES"),
        justification: undated("doc comment"),
        note: "The enumerative `get-abduct` search's own honest give-up: past this many re-checked candidates, `abduct` returns `Ok(None)` directly (module doc: \"declining with None\"), which is this feature's analogue of `unknown`. Every candidate that IS tried is independently re-verified by `crate::auto::check_auto` before acceptance, so this bound can only cost completeness, never soundness. Same name, different module and value (256), as `quant_bool_model_sat.rs::MAX_CANDIDATES` — unrelated searches, not a divergent twin.",
    },
    ConfigEntry {
        name: "MAX_SYNTHESIZED_ATOMS",
        module: "crates/axeyum-solver/src/abduct.rs",
        value: "4096",
        unit: "synthesized atoms",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "every synthesized candidate is independently re-verified by `check_auto` (the trusted decider) before `abduct` accepts it; a truncated synthesis pool can only omit candidates, and the caller-visible `Ok(None)` give-up is governed by `MAX_CANDIDATES` in this same file, not by this bound.",
        env_override: None,
        justification: undated("doc comment"),
        note: "Caps the SyGuS-lite atom pool (and hence the O(n^2) conjunction phase) that feeds the MAX_CANDIDATES-bounded enumerative search; synthesis simply stops adding atoms past this bound rather than declining outright.",
    },
    ConfigEntry {
        name: "MAX_ARRAY_VALUE_REPAIR_DEPTH",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "8",
        unit: "array-definition substitution recursion depth",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the projected candidate is only accepted as sat after first_projected_replay_failure finds no violated conjunct against the ORIGINAL assertions; a truncated repair recursion can only fail to find an existing repair (forcing decline to unknown), never accept an unfaithful model",
        env_override: None,
        justification: undated("doc comment"),
        note: "`repair_projected_array_symbol_to_value_through_definitions` recurses through chained array-variable definitions to push a desired value back to its defining symbol; `visited` already prevents cycles, so this only bounds chain length, not termination.",
    },
    ConfigEntry {
        name: "MAX_BRANCH_BEAM_DEPTH",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "6",
        unit: "beam-search states expanded from the frontier",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the beam's best candidate is only kept if it fully replays; a shallower beam can only fail to find an existing repair, never accept an unfaithful one",
        env_override: None,
        justification: undated("doc comment"),
        note: "One of a same-named quadruple (DEPTH/WIDTH/EXPANSIONS/UPHILL_FALSE) shaping `repair_projected_replay_branch_beam`'s hill-climbing search over branch-disjunction repairs; a second, textually distinct quadruple with the same four names and values governs the sibling `MAX_MIXED_REPAIR_BEAM_*` search a few hundred lines away.",
    },
    ConfigEntry {
        name: "MAX_BRANCH_BEAM_EXPANSIONS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "64",
        unit: "beam-search frontier-state expansions",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the beam's best candidate is only kept if it fully replays; fewer expansions can only fail to find an existing repair, never accept an unfaithful one",
        env_override: None,
        justification: undated("doc comment"),
        note: "The `while !frontier.is_empty() && expansions < MAX_BRANCH_BEAM_EXPANSIONS` loop bound in `repair_projected_replay_branch_beam`. See MAX_BRANCH_BEAM_DEPTH's note on the twin MAX_MIXED_REPAIR_BEAM_* quadruple.",
    },
    ConfigEntry {
        name: "MAX_BRANCH_BEAM_UPHILL_FALSE",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "4",
        unit: "false literals worse than the baseline candidate",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the beam's best candidate is only kept if it fully replays; pruning a temporarily-worse candidate can only fail to find an existing repair that requires going uphill first, never accept an unfaithful one",
        env_override: None,
        justification: undated("doc comment"),
        note: "Sets `max_false = current_false + MAX_BRANCH_BEAM_UPHILL_FALSE`: how much worse (more false literals) a candidate is allowed to be than the search's baseline before it is pruned from the frontier. See MAX_BRANCH_BEAM_DEPTH's note on the twin MAX_MIXED_REPAIR_BEAM_* quadruple.",
    },
    ConfigEntry {
        name: "MAX_BRANCH_BEAM_WIDTH",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "8",
        unit: "beam frontier states retained",
        protects: Protects::Memory,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the beam's best candidate is only kept if it fully replays; a narrower frontier can only fail to find an existing repair, never accept an unfaithful one",
        env_override: None,
        justification: undated("doc comment"),
        note: "`frontier.truncate(MAX_BRANCH_BEAM_WIDTH)` after each expansion round. See MAX_BRANCH_BEAM_DEPTH's note on the twin MAX_MIXED_REPAIR_BEAM_* quadruple.",
    },
    ConfigEntry {
        name: "MAX_BRANCH_SCALAR_CHOICE_DEPTH",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "4",
        unit: "false literals already present in the branch",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "declining only skips this one repair helper; the projected candidate is still gated by full replay before acceptance, and other repair helpers in the schedule still run",
        env_override: None,
        justification: undated("doc comment"),
        note: "Despite the name, this does not bound a recursion or search depth: `repair_projected_branch_scalar_choice_candidate` declines outright (`return Ok(None)`) when the branch's CURRENT false-literal count exceeds this, before any search runs. It is an admission threshold on candidate quality, not a depth budget.",
    },
    ConfigEntry {
        name: "MAX_BRANCH_SCALAR_CHOICE_STATES",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "16",
        unit: "beam frontier states retained",
        protects: Protects::Memory,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the repaired candidate is only kept if it fully replays; a narrower frontier can only fail to find an existing repair, never accept an unfaithful one",
        env_override: None,
        justification: undated("doc comment"),
        note: "`frontier.truncate(MAX_BRANCH_SCALAR_CHOICE_STATES)` inside `repair_projected_branch_scalar_choice_candidate`.",
    },
    ConfigEntry {
        name: "MAX_BRANCH_SELECT_CYCLE_BRANCHES",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "8",
        unit: "disjunction branches considered",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the repaired candidate is only kept if it fully replays; considering fewer branches can only fail to find an existing repair, never accept an unfaithful one",
        env_override: None,
        justification: undated("doc comment"),
        note: "`branches.truncate(MAX_BRANCH_SELECT_CYCLE_BRANCHES)` in `repair_projected_replay_branch_select_cycle`, which pairs every kept branch against every other (O(branches^2)).",
    },
    ConfigEntry {
        name: "MAX_BRANCH_SELECT_CYCLE_CONJUNCTS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "64",
        unit: "conjuncts across all original assertions",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "declining only skips this one repair heuristic on large queries; the projected candidate is still gated by full replay before acceptance",
        env_override: None,
        justification: undated("doc comment"),
        note: "Query-size admission gate in `repair_projected_replay_branch_select_cycle`: `positive_replay_conjunct_count(...) > MAX_BRANCH_SELECT_CYCLE_CONJUNCTS` declines the whole O(branches^2) cycle search up front, checked before it starts.",
    },
    ConfigEntry {
        name: "MAX_BRANCH_SELECT_CYCLE_TRIALS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "32",
        unit: "repair trials",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the repaired candidate is only kept if it fully replays; fewer trials can only fail to find an existing repair, never accept an unfaithful one",
        env_override: None,
        justification: undated("doc comment"),
        note: "`*trials >= MAX_BRANCH_SELECT_CYCLE_TRIALS` bounds the trial loop in `repair_projected_replay_branch_select_cycle_after_select`.",
    },
    ConfigEntry {
        name: "MAX_BRANCH_SELECT_RESIDUAL_CHAIN_HOPS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "4",
        unit: "residual-chain repair hops",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the repaired candidate is only kept if it fully replays; fewer hops can only fail to find an existing repair, never accept an unfaithful one",
        env_override: None,
        justification: undated("doc comment"),
        note: "`for _ in 0..=MAX_BRANCH_SELECT_RESIDUAL_CHAIN_HOPS` in `repair_projected_replay_branch_select_residual_chain`.",
    },
    ConfigEntry {
        name: "MAX_DIFF_SKOLEMS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "256",
        unit: "diff-skolem witnesses (array (dis)equality atoms)",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_MAX_DIFF_SKOLEMS"),
        justification: undated("doc comment"),
        note: "The doc comment says crossing this means 'declining to unknown', but the code disagrees at its only external call site: `prepare_online_array_equalities` (`atoms.len() > MAX_DIFF_SKOLEMS` -> `Ok(None)`) is consumed by `ufbv_online.rs`'s `abstract_rows_for_online` caller, which turns that `None` into `Err(SolverError::Unsupported(...))` -- a hard Err, not `CheckResult::Unknown` -- even though a sibling `BuildFailure::Unknown` variant exists and is not used here. Separately, inside `abv/lazy_ext.rs::refine_extensionality`, the same constant throttles a per-round diff-witness counter (`*diff_skolems >= MAX_DIFF_SKOLEMS` -> `continue`, skipping one atom's witness for that round); that crossing only stalls CEGAR convergence, which surfaces as `unknown` via MAX_ROW_ROUNDS, never a wrong sat.",
    },
    ConfigEntry {
        name: "MAX_FOLLOWUP_OR_CYCLE_GUARD_CONJUNCTS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "64",
        unit: "conjuncts across all original assertions",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "declining only skips this one candidate-rejection heuristic on large queries, defaulting to NOT rejecting the candidate; the projected candidate is still gated by full replay before acceptance",
        env_override: None,
        justification: undated("doc comment"),
        note: "Query-size admission gate inside `scalar_closure_rejects_branch_candidate`: above the bound it returns `Ok(false)` (does not reject), skipping the expensive `scalar_closure_rejects_followup_or_cycle` check rather than running it.",
    },
    ConfigEntry {
        name: "MAX_MIXED_BEAM_FAILURE_VISITS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "2",
        unit: "revisits of the same failed conjunct ordinal",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the mixed beam's best candidate is only kept if it fully replays; pruning a repeatedly-revisited failure can only fail to find an existing repair, never accept an unfaithful one",
        env_override: None,
        justification: undated("doc comment"),
        note: "In `replay_repair_beam_expand_state`, a search branch that has already tried to fix the same `failure.conjunct_ordinal` this many times is pruned (`return Ok(())`), avoiding redundant re-expansion.",
    },
    ConfigEntry {
        name: "MAX_MIXED_REPAIR_BEAM_DEPTH",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "6",
        unit: "beam-search states expanded from the frontier",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the mixed beam's best candidate is only kept if it fully replays; a shallower beam can only fail to find an existing repair, never accept an unfaithful one",
        env_override: None,
        justification: undated("doc comment"),
        note: "Shapes `repair_projected_replay_mixed_beam`'s search (mixes select- and branch-repair moves in one beam), a textual twin of the `MAX_BRANCH_BEAM_*` quadruple with identical values.",
    },
    ConfigEntry {
        name: "MAX_MIXED_REPAIR_BEAM_EXPANSIONS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "64",
        unit: "beam-search frontier-state expansions",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the mixed beam's best candidate is only kept if it fully replays; fewer expansions can only fail to find an existing repair, never accept an unfaithful one",
        env_override: None,
        justification: undated("doc comment"),
        note: "Twin of MAX_BRANCH_BEAM_EXPANSIONS for the mixed select/branch beam in `repair_projected_replay_mixed_beam`.",
    },
    ConfigEntry {
        name: "MAX_MIXED_REPAIR_BEAM_UPHILL_FALSE",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "4",
        unit: "false literals worse than the baseline candidate",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the mixed beam's best candidate is only kept if it fully replays; pruning a temporarily-worse candidate can only fail to find an existing repair that requires going uphill first, never accept an unfaithful one",
        env_override: None,
        justification: undated("doc comment"),
        note: "Twin of MAX_BRANCH_BEAM_UPHILL_FALSE for the mixed select/branch beam in `repair_projected_replay_mixed_beam`.",
    },
    ConfigEntry {
        name: "MAX_MIXED_REPAIR_BEAM_WIDTH",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "8",
        unit: "beam frontier states retained",
        protects: Protects::Memory,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the mixed beam's best candidate is only kept if it fully replays; a narrower frontier can only fail to find an existing repair, never accept an unfaithful one",
        env_override: None,
        justification: undated("doc comment"),
        note: "Twin of MAX_BRANCH_BEAM_WIDTH for the mixed select/branch beam in `repair_projected_replay_mixed_beam`.",
    },
    ConfigEntry {
        name: "MAX_OR_MIXED_BEAM_CONJUNCTS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "64",
        unit: "conjuncts across all original assertions",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "declining only skips the mixed-beam repair route on large queries; the projected candidate is still gated by full replay before acceptance through whichever other repair route runs",
        env_override: None,
        justification: undated("doc comment"),
        note: "`mixed_replay_beam_admits_or_failure` returns `false` (do not admit the mixed beam) above this query-size bound.",
    },
    ConfigEntry {
        name: "MAX_PROJECTION_REPAIR_ROUNDS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "32",
        unit: "select/branch/scalar repair rounds",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the final projected candidate is only accepted as sat after `first_projected_replay_failure` finds no violated conjunct; fewer rounds can only fail to reach a fixpoint that would have replayed, forcing decline to unknown, never accepting an unfaithful model",
        env_override: None,
        justification: undated("doc comment"),
        note: "`repair_projected_ext_candidate`'s outer fixpoint loop (select-equality repair, branch-disjunction repair, scalar-equality repair, repeated to convergence or this cap).",
    },
    ConfigEntry {
        name: "MAX_RETURNED_OR_STABILIZATION_CONJUNCTS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "64",
        unit: "conjuncts across all original assertions",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "declining only skips this one stabilization pass on large queries; the projected candidate is still gated by full replay before acceptance",
        env_override: None,
        justification: undated("doc comment"),
        note: "Query-size admission gate before `stabilize_scalar_trial_after_returned_or_array_store` runs.",
    },
    ConfigEntry {
        name: "MAX_ROW_ROUNDS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "64",
        unit: "CEGAR refinement rounds",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "docs/research/12-performance/qf-abv-route-attribution-2026-09-08.md",
            "2026-09-08",
            Some("f24c61f91"),
            &[sym("crates/axeyum-solver/src/abv.rs", "MAX_ROW_ROUNDS")],
            &[doc(
                "docs/research/12-performance/qf-abv-route-attribution-2026-09-08.md",
            )],
        ),
        note: "Bounds the lazy ROW / extensionality CEGAR. IT, NOT THE CLOCK, is what refuses two files of the committed QF_ABV loss list: `dwp cat.next_line_num` reaches 64 rounds after 3.3 s of a 24 s budget and `dwp vdir.strcmp_size` after 14.6 s, and the message the caller then prints names an array SHAPE, not a round count. Registered undated-to-dated by that measurement; the value itself is unchanged and unjustified by anything but a doc comment.",
    },
    ConfigEntry {
        name: "MAX_ROW_SITES",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "4096",
        unit: "abstracted read sites",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "a refused site aborts the abstraction, so the route declines to `unknown` and never returns a verdict from a partial abstraction",
        env_override: None,
        justification: dated(
            "docs/research/12-performance/qf-abv-route-attribution-2026-09-08.md",
            "2026-09-08",
            Some("f24c61f91"),
            &[sym("crates/axeyum-solver/src/abv.rs", "MAX_ROW_SITES")],
            &[doc(
                "docs/research/12-performance/qf-abv-route-attribution-2026-09-08.md",
            )],
        ),
        note: "SIGNAL IS `None` ON PURPOSE, AND THAT IS THE PROBLEM IT IS REGISTERED FOR: the refusal is an `Ok(None)` the caller cannot tell apart from an unmodelled array shape, so the route reports \"an array read is outside the modelled store/variable/const-array fragment\" for a CAPACITY event. Fired on `brummayerbiere/fifo32ia04k08` (4,109 sites) and `wchains140se` (4,484) on 2026-09-08. `crate::AbvStats::row_site_cap_refusals` counts the refusals and, since 2026-09-08, `note_crossed` carries them with their numbers. AND IT IS TWO CONTRACTS, NOT ONE: the same `RowCtx` (hence the same site cap) is shared by `abstract_rows_for_online`, whose only caller (`ufbv_online.rs`) turns a declined abstraction into `SolverError::Unsupported` — an `Err`, not an unknown — so which of the two this bound produces depends on the entry point.",
    },
    ConfigEntry {
        name: "MAX_SCALAR_CLOSURE_STEPS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "4",
        unit: "scalar-choice closure steps",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the closure trial is only used to decide whether to prune a candidate during search; the final accepted candidate is separately gated by full replay before acceptance, so a truncated closure can only mis-prune toward MORE search, never accept an unfaithful model",
        env_override: None,
        justification: undated("doc comment"),
        note: "`replay_scalar_closure_from_trial`'s step loop. Despite living next to the diagnostics-only `MAX_SCALAR_CLOSURE_BRANCHES`/`MAX_SCALAR_CLOSURE_REPORTED_BRANCHES` (which only size a reported `Vec<...Diagnostic>`), this one also feeds `scalar_closure_rejects_branch_candidate`'s actual accept/reject decision during search, not just message text.",
    },
    ConfigEntry {
        name: "MAX_SCALAR_EQUALITY_REPAIRS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "64",
        unit: "scalar-equality repairs applied",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the final projected candidate is only accepted as sat after full replay; fewer repairs can only leave more conjuncts false, forcing decline to unknown, never accepting an unfaithful model",
        env_override: None,
        justification: undated("doc comment"),
        note: "`repairs >= MAX_SCALAR_EQUALITY_REPAIRS` bounds the repair count inside `repair_projected_scalar_equalities`'s multi-pass loop.",
    },
    ConfigEntry {
        name: "MAX_SCALAR_REPLAY_REPAIR_CONJUNCTS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "64",
        unit: "conjuncts across all original assertions",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "declining only skips this one repair helper on large queries; the projected candidate is still gated by full replay before acceptance",
        env_override: None,
        justification: undated("doc comment"),
        note: "Query-size admission gate in `repair_projected_replay_scalar_failure`, alongside MAX_SCALAR_REPLAY_REPAIR_FALSE.",
    },
    ConfigEntry {
        name: "MAX_SCALAR_REPLAY_REPAIR_FALSE",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "4",
        unit: "false literals in the current projected candidate",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "declining only skips this one repair helper when the candidate is already far from correct; the projected candidate is still gated by full replay before acceptance through whichever other repair route runs",
        env_override: None,
        justification: undated("doc comment"),
        note: "`current_false > MAX_SCALAR_REPLAY_REPAIR_FALSE` admission check in `repair_projected_replay_scalar_failure`, alongside MAX_SCALAR_REPLAY_REPAIR_CONJUNCTS.",
    },
    ConfigEntry {
        name: "MAX_STORE_CHAIN_READBACK_DEPTH",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "8",
        unit: "store-chain recursion depth",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the projected candidate is only accepted as sat after full replay; a truncated readback recursion can only fail to find an existing repair, never accept an unfaithful model",
        env_override: None,
        justification: undated("doc comment"),
        note: "`depth > MAX_STORE_CHAIN_READBACK_DEPTH` in `repair_projected_store_chain_readback`; a `visited` set already blocks cycles, so this only bounds chain length.",
    },
    ConfigEntry {
        name: "MAX_STRUCTURAL_ARRAY_REALIZATION_STEPS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "4_096",
        unit: "store/ite layers walked while realizing one array term",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_MAX_STRUCTURAL_ARRAY_REALIZATION_STEPS"),
        justification: undated("doc comment"),
        note: "`realize_structural_array_term`'s `for _step in 0..MAX_STRUCTURAL_ARRAY_REALIZATION_STEPS` loop returns `StructuralRealization::Incompatible` when exhausted. Unlike most bounds in this file, the CALLER treats a persistent `Incompatible` as a hard failure: `realize_structural_array_equalities` ends with `Err(SolverError::Backend(\"online ROW projection could not realize a bounded structural array equality\"))` -- an Err that ends the route, not a graceful `CheckResult::Unknown`.",
    },
    ConfigEntry {
        name: "MAX_TARGETED_REPLAY_REPAIRS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "8",
        unit: "targeted replay-repair rounds",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the loop's final state is only returned as `ExtReplay::Sat` when `first_projected_replay_failure` finds nothing false; exhausting the budget without convergence falls through to one last failure check and, on failure, returns `ExtReplay::Failed` (which the caller turns into `ext_unknown`), never an unfaithful sat",
        env_override: None,
        justification: undated("doc comment"),
        note: "`project_replay_ext_candidate`'s `for _ in 0..MAX_TARGETED_REPLAY_REPAIRS` loop, the outermost repair/replay cycle of the lazy-extensionality path.",
    },
    ConfigEntry {
        name: "SCALAR_LOCAL_SEARCH_PROBE_MS",
        module: "crates/axeyum-solver/src/abv.rs",
        value: "100",
        unit: "milliseconds",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "a `sat` found by the probe is verified by `replay_preprocessed_model`'s full replay before being trusted (crates/axeyum-solver/src/preprocess.rs), and an unsat/unknown probe result is simply discarded and the query still proceeds to the normal, complete `backend.check` call; so a too-short probe can only cost a missed shortcut, never a wrong or missing verdict",
        env_override: None,
        justification: undated("no written justification"),
        note: "Wall-clock budget for `check_scalar_abstraction`'s opportunistic pre-solve local-search probe (`crate::preprocess::check_with_preprocessing_and_local_search`) before falling back to the normal backend call. No doc comment explains why 100ms specifically.",
    },
    ConfigEntry {
        name: "MAX_ARRAY_ELIM_CONGRUENCE_PAIRS",
        module: "crates/axeyum-solver/src/abv/array_elim_certificate.rs",
        value: "256",
        unit: "select-congruence pairs",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_MAX_ARRAY_ELIM_CONGRUENCE_PAIRS"),
        justification: undated("doc comment"),
        note: "Gates evidence production only, not the verdict: `certify_array_elim_unsat` returns `Ok(None)` (no certificate) above this O(k^2) pairing bound; the underlying `Unsat` result (from the separate DRAT-checked QF_BV refutation) is unaffected either way. `Signal::ToCaller` because the crossing is literally the `Option::None` in the return type. Doc comment says this mirrors an 'eager bound in crate::euf' but gives no measurement for 256 itself.",
    },
    ConfigEntry {
        name: "READ_CONGRUENCE_MAX_SATURATION_WORK",
        module: "crates/axeyum-solver/src/array_axiom.rs",
        value: "1_000_000",
        unit: "dag_nodes * ite_count^2 (work proxy)",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "this is a checked add-on refutation route (a certified evidence shortcut for a query that is separately decided elsewhere, e.g. by a downstream structural certificate); declining it on cost-heavy inputs never changes a verdict, per the doc comment's own 'graceful decline ... never a changed verdict ... no lost certificate'",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-07-02",
            Some("e67f218f"),
            &[sym(
                "crates/axeyum-solver/src/array_axiom.rs",
                "saturate_contextual_ite_equality_facts",
            )],
            &[commit(
                "e67f218f",
                "work-gate the read-congruence contextual-ite saturation",
            )],
        ),
        note: "Introduced by e67f218f (2026-07-02) after `fifo_bc04` (~960 DAG nodes, 319 `ite`s) drove the read-congruence probe's contextual-`ite` saturation fixpoint past 600s; work-gating cut it to 3.2s. Hand-authored array-axiom rows score far below the cap; `ite`-free rows score 0.",
    },
    ConfigEntry {
        name: "BV_ABSTRACTION_TIMEOUT",
        module: "crates/axeyum-solver/src/array_bv_abs.rs",
        value: "Duration::from_secs(1)",
        unit: "wall-clock seconds",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "this is a checked add-on refutation route: `report.evidence.check(...)` independently re-verifies whatever the timed-out or completed solve produced before `bv_abstraction_refutation` trusts it, and a non-UNSAT-shaped or unverified evidence declines (`None`) rather than being trusted, leaving the query to whatever route already decides it",
        env_override: None,
        justification: undated("no written justification"),
        note: "Wall-clock budget on the `produce_qf_bv_evidence` sub-solve of the scalar-BV-abstraction over-approximation; no doc comment or measurement explains why 1s specifically. Ends a search inconclusively (`.ok()?` turns a timeout/Err into a declined `None`) with no doc comment naming the choice.",
    },
    ConfigEntry {
        name: "MAX_ABSTRACTED_NODES",
        module: "crates/axeyum-solver/src/array_bv_abs.rs",
        value: "512",
        unit: "reachable AIG-abstraction nodes",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "this is a checked add-on refutation route (see MAX_ABSTRACTION_VISITS); declining it above the size bound never changes a verdict, only whether this shortcut fires",
        env_override: None,
        justification: undated("no written justification"),
        note: "`reachable_node_count(...) > MAX_ABSTRACTED_NODES` in `bv_abstraction_refutation`; applied to the RESULT of `build_bv_abstraction`, not the walk that produces it (that walk is separately bounded by MAX_ABSTRACTION_VISITS).",
    },
    ConfigEntry {
        name: "MAX_ABSTRACTED_TERMS",
        module: "crates/axeyum-solver/src/array_bv_abs.rs",
        value: "64",
        unit: "abstracted scalar terms",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "this is a checked add-on refutation route (see MAX_ABSTRACTION_VISITS); declining it above the size bound never changes a verdict, only whether this shortcut fires",
        env_override: None,
        justification: undated("no written justification"),
        note: "`abstraction.abstracted_terms.len() > MAX_ABSTRACTED_TERMS` in `bv_abstraction_refutation`; like MAX_ABSTRACTED_NODES, applied after the walk completes.",
    },
    ConfigEntry {
        name: "MAX_ABSTRACTION_VISITS",
        module: "crates/axeyum-solver/src/array_bv_abs.rs",
        value: "1 << 22",
        unit: "AbstractionState::abstract_term invocations",
        protects: Protects::Termination,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "this refuter is a checked add-on evidence route, never the primary decision procedure; declining it (returning no certificate) is always sound, per the doc comment and the incident that introduced this bound",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-21",
            Some("4032bd66"),
            &[sym(
                "crates/axeyum-solver/src/array_bv_abs.rs",
                "abstract_term",
            )],
            &[
                live("abstract_term", "crates/axeyum-solver/src/array_bv_abs.rs"),
                commit(
                    "4032bd66",
                    "the array BV-abstraction walked a DAG as a tree",
                ),
            ],
        ),
        note: "Commit 4032bd66 (2026-08-21) found `abstract_term` unmemoized, self-recursing 'dozens of frames deep' on a 5,762-reachable-node QF_FP formula (`fp_misc`, 4,194,309 visits) and hanging `lean-reconstruction` past 124.7s of a 125s budget. The fix memoized `abstract_term` (bringing visits on that formula to 4,365) AND added this cap so a defeated memo fails fast (0.23s) instead of hanging; it is 'deliberately far above what a memoized walk needs' per the doc comment. If the memoization in `abstract_term` is ever removed, this cap becomes the primary defense again.",
    },
    ConfigEntry {
        name: "MAX_FINITE_ARRAY_EXT_READS",
        module: "crates/axeyum-solver/src/array_finite.rs",
        value: "16",
        unit: "concrete domain values (2^index_width)",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "this is a checked add-on refutation route; declining to match a wider-domain shape leaves the query to the general solver, and never accepts a wrong verdict since it only ever certifies a refutation it independently re-derives",
        env_override: None,
        justification: undated("doc comment"),
        note: "`finite_bv_domain_size` returns `None` (declining the finite-domain array-extensionality refuter) when `2^width > MAX_FINITE_ARRAY_EXT_READS`. Doc comment frames it as keeping the certificate 'small enough to be readable in Lean and cheap in dominance audits' -- an evidence-size rationale, not a search-cost one, though the effect is the same admission gate.",
    },
    ConfigEntry {
        name: "ABV_ONLINE_LADDER_RESERVE_SHARE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "4",
        unit: "divisor of the dispatcher's remaining deadline, held back for the array ladder",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_ABV_ONLINE_RESERVE"),
        justification: dated(
            "docs/research/12-performance/ladder-budget-discipline-2026-09-08.md",
            "2026-09-08",
            None,
            // The measurement is "on four QF_ABV files `abv-online-cdclt` spent
            // 24.009 s of a 24 s budget, declined, and `array-fast-path` then
            // decided the file in 0.007-0.174 s". It rests on the online route
            // still being the first thing an array query enters, on the array
            // fast paths still being what runs after it, and on the online
            // route still honouring the `timeout` it is handed -- change any of
            // the three and the numbers stop describing this tree.
            &[
                sym("crates/axeyum-solver/src/auto.rs", "dispatch_abv_online"),
                sym(
                    "crates/axeyum-solver/src/auto.rs",
                    "dispatch_array_fast_paths",
                ),
                sym(
                    "crates/axeyum-solver/src/ufbv_online.rs",
                    "check_qf_aufbv_online_cdclt",
                ),
            ],
            // The basis names the route the reserve is FOR. If
            // `dispatch_array_fast_paths` leaves auto.rs, this constant holds a
            // quarter of every array query's clock back for a ladder with no
            // rung left, and the reasoning above stops meaning anything --
            // while a basis naming the constant or the doc would keep passing.
            &[
                live(
                    "dispatch_array_fast_paths",
                    "crates/axeyum-solver/src/auto.rs",
                ),
                doc("docs/research/12-performance/qf-abv-route-attribution-2026-09-08.md"),
            ],
        ),
        note: "The slice of the budget held back from `abv-online-cdclt` -- the FIRST route every array query tries -- for the array ladder under it. Before this constant existed that route took `config.timeout` in FULL, so on any file it could not decide, `array-fast-path` ran only inside the harness watchdog's grace period (24 s spent above plus a fresh 24 s budget below is 48 s of a 24 s promise). Chosen against BOTH bounds the sweep gives, the method `UF_ARITH_LADDER_RESERVE_SHARE` paid four files to establish: 18 s left to the online route is above its slowest decision in the sweep (5.723 s, of 24 decisions), and 6 s to the ladder is twice its slowest decision (2.898 s) and 35x its median (168 ms). A route needing 99% of the clock is not recoverable by any reserve; none in this population does, unlike QF_UFLIA's `hash_uns_05_20`. The env override selects the whole policy (`off` restores the unreserved budget), not just this divisor.",
    },
    ConfigEntry {
        name: "DEFAULT_INT_LINEAR_PORTFOLIO_WORKERS",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "1",
        unit: "concurrent workers for the integer-linear fused group",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: Some("AXEYUM_PORTFOLIO_WORKERS"),
        justification: dated(
            "docs/research/12-performance/fused-portfolio-int-linear-2026-09-09.md",
            "2026-09-09",
            None,
            &[
                sym(
                    "crates/axeyum-solver/src/auto.rs",
                    "INT_LINEAR_PORTFOLIO_ARMS",
                ),
                sym(
                    "crates/axeyum-solver/src/auto.rs",
                    "dispatch_int_blast_width_ladder",
                ),
            ],
            &[
                doc("docs/research/12-performance/fused-portfolio-int-linear-2026-09-09.md"),
                doc("docs/research/12-performance/the-portfolio-answer-is-not-yet.md"),
            ],
        ),
        note: "The DEFAULT is 1, and 1 is not a tuning choice -- it is the switch that keeps the shipped ladder sequential. At 1 `dispatch_int_linear_refuters` does not construct a group at all, so the pre-portfolio path is not approximated, it is taken. Raising it is a RESOURCE decision (each arm wants a whole core for most of a competition budget), which is why it is an operator env var and not something the dispatcher reads off the formula. Measured effect at 2 on the committed lists, 2026-09-09: see the doc.",
    },
    ConfigEntry {
        name: "DL_EXTENDED_FALLBACK_RESERVE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "Duration::from_secs(3)",
        unit: "seconds of the caller's deadline",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`min(t/8, 3s)` withheld from the extended difference-logic probe so later routes keep budget. Unlike its sibling below it cites no measurement at all.",
    },
    ConfigEntry {
        name: "DL_EXTENDED_LADDER_RESERVE_SHARE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "8",
        unit: "divisor of the caller's deadline, held back for the routes below the probe",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The `/ 8` half of `min(t/8, 3s)`, given a name on 2026-09-08 when the four hand-rolled copies of this arithmetic were replaced by one `LadderSlice` policy. A divisor written as a literal at a call site cannot be found by name, and finding the four copies is what cost this lane's predecessors a division-sized measurement each. The VALUE is unchanged and, like its `DL_EXTENDED_FALLBACK_RESERVE` sibling, cites no measurement at all.",
    },
    ConfigEntry {
        name: "DL_FALLBACK_RESERVE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "Duration::from_secs(6)",
        unit: "seconds of the caller's deadline",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`min(t/4, 6s)` withheld from the difference-logic probe. The doc names a real regression (`QF_IDL/sal/lpsat/lpsat-goal-18`, decided unsat by lia-dpll in 4.2 s, turned `unknown` by an unreserved probe) but gives it no date.",
    },
    ConfigEntry {
        name: "DL_LADDER_RESERVE_SHARE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "4",
        unit: "divisor of the caller's deadline, held back for the routes below the probe",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The `/ 4` half of `min(t/4, 6s)`, named on 2026-09-08 alongside `ABV_ONLINE_LADDER_RESERVE_SHARE` and `UF_ARITH_LADDER_RESERVE_SHARE` -- three copies of the same quarter, in three ladders, none of which could be found from the others by name. The regression the reserve prevents is recorded on `DL_FALLBACK_RESERVE` (`QF_IDL/sal/lpsat/lpsat-goal-18`, decided unsat by lia-dpll in 4.2 s, turned `unknown` by an unreserved probe) and is undated there; naming this divisor does not date it. FINDING, measured 2026-09-08 and NOT acted on: on the first 50 QF_IDL files of the committed parity list, `dl-online` spends 421.9 s without deciding and the routes its reserve pays for decide ZERO of them -- the reserve's justification rests entirely on one file outside that sample.",
    },
    ConfigEntry {
        name: "INT_BLAST_DENSE_MAX_WIDTH",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "16",
        unit: "bit-vector width (bits)",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Top of the densely-tried range in the int-blast width ladder; above it widths are tried every 8 bits.",
    },
    ConfigEntry {
        name: "INT_BLAST_ESCALATION_MAX_WIDTH",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "INT_BLAST_MAX_WIDTH",
        unit: "bit-vector width (bits)",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_INT_BLAST_ESCALATION_MAX_WIDTH"),
        justification: undated("doc comment"),
        note: "Top of the int-blast width ladder's ESCALATION TAIL (ADR-1921), the rungs above `INT_BLAST_MAX_WIDTH` that a query reaches only after every cheaper rung failed to produce a replaying model. VALUE IS INDIRECT and deliberately EQUAL to `INT_BLAST_MAX_WIDTH`, so the shipped tail is EMPTY and the ladder is unchanged: this entry exists to make the escalation measurable (`AXEYUM_INT_BLAST_ESCALATION_MAX_WIDTH=64`), not to perform it. Measured 2026-09-12 (ADR-1921) the raise does not pay on QF_NIA. Clamped at the ladder to `axeyum_rewrite::MAX_INT_BLAST_WIDTH` (64) because `blast_integers` returns a hard `InvalidWidth` ERROR, not an `unknown`, above it - so 128 is unreachable without a bigint model read-back.",
    },
    ConfigEntry {
        name: "INT_BLAST_MAX_WIDTH",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "DEFAULT_INT_WIDTH",
        unit: "bit-vector width (bits)",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "VALUE IS INDIRECT: `DEFAULT_INT_WIDTH` (32) is defined in `lia.rs`, so this file's ladder top moves if that constant moves. The registry records the expression, not the resolved number, because the indirection is the fact worth knowing.",
    },
    ConfigEntry {
        name: "INT_BLAST_MIN_WIDTH",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "4",
        unit: "bit-vector width (bits)",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Ladder floor: narrower than this leaves no room for a genuine small witness.",
    },
    ConfigEntry {
        name: "INT_BOX_ENUM_FAST_CASES",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "10_000",
        unit: "enumeration cases",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "commit 4f27961eb",
            "2026-07-03",
            Some("4f27961eb"),
            &[sym(
                "crates/axeyum-solver/src/auto.rs",
                "INT_BOX_ENUM_FAST_CASES",
            )],
            &[
                commit("4f27961eb", "cap the pre-blast int-box enumeration probe"),
                live(
                    "decide_int_box_by_evaluation",
                    "crates/axeyum-solver/src/auto.rs",
                ),
            ],
        ),
        note: "Routes small proven integer boxes to ground evaluation ahead of bit-blasting. The doc records a measured regression (the `nia_unsat` frontier family fell 40 to 23, 20-30x slower per instance, when a 10^6-case probe ran ahead of the blast) but gives it NO DATE, so nothing can tell whether it still holds.",
    },
    ConfigEntry {
        name: "INT_REAL_RELAX_BUDGET_SHARE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "6",
        unit: "divisor of the caller's remaining deadline",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "nothing: see the note",
        env_override: None,
        justification: undated("doc comment"),
        note: "FINDING. Intended to hand the real-relaxation refuter one sixth of the budget. When the shrunk share underflows to zero the code returns the caller's config UNCHANGED — the full, unshrunk timeout — rather than skipping the refuter or clamping to a floor. The sharing policy is bypassed silently at exactly the small-budget end where starvation matters most. Recorded, not changed: this lane does not retune.",
    },
    ConfigEntry {
        name: "MAX_BOUND_PROP_ROUNDS",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "256",
        unit: "fixpoint iterations",
        protects: Protects::Termination,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "a looser box can only cause a sound decline downstream, never a wrong verdict",
        env_override: None,
        justification: undated("doc comment"),
        note: "FINDING. `for _ in 0..256 { .. if !changed { break } }` — reaching the cap without a fixpoint hands the caller partial bounds with no indication the fixpoint was not reached. The incompleteness is invisible.",
    },
    ConfigEntry {
        name: "MAX_COERCION_LINK",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "64",
        unit: "integer range width (hi - lo)",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "the weaker relaxation's `sat` is accepted only after model replay against the original assertions",
        env_override: None,
        justification: undated("doc comment"),
        note: "Decides whether an Int/Real coercion gets an exact finite case-split link or only the weaker relaxation.",
    },
    ConfigEntry {
        name: "MAX_DISJUNCTIVE_BRANCHES",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "32",
        unit: "case-split branches",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Bounds sub-solve fan-out from a finite-domain disjunctive case split.",
    },
    ConfigEntry {
        name: "MAX_EXP",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "62",
        unit: "bit exponent",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Keeps 2^exp inside `i128` in the interval table. A function-local `const` inside `interval_of`'s `Op::IntPow2` arm, so its name collides with nothing but is also invisible to a module-level scan.",
    },
    ConfigEntry {
        name: "MAX_FINITE_DOMAIN_BRANCHES",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "64",
        unit: "case-split branches",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "As `MAX_DISJUNCTIVE_BRANCHES`, doubled because equality-only branches are individually cheaper. Neither number is measured.",
    },
    ConfigEntry {
        name: "MAX_INT_BOX_ENUM_CASES",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "1_000_000",
        unit: "enumeration cases",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The post-decline fallback cap: once bit-blasting has declined, evaluation is the only remaining decider, so this is 100x looser than the pre-blast cap above.",
    },
    ConfigEntry {
        name: "MAX_MBQI_FREE_INT_SYMBOLS",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "2",
        unit: "free Int symbols",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0360",
            "2026-07-22",
            None,
            &[sym(
                "crates/axeyum-solver/src/auto.rs",
                "MAX_MBQI_FREE_INT_SYMBOLS",
            )],
            &[adr("ADR-0360")],
        ),
        note: "Gates the free-int model completion tried ahead of ordinary MBQI.",
    },
    ConfigEntry {
        name: "MAX_MBQI_FREE_INT_TUPLES",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "256",
        unit: "cartesian-product tuples",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0360",
            "2026-07-22",
            None,
            &[sym(
                "crates/axeyum-solver/src/auto.rs",
                "MAX_MBQI_FREE_INT_TUPLES",
            )],
            &[adr("ADR-0360")],
        ),
        note: "Bounds the exhaustive search over the free-int value pools.",
    },
    ConfigEntry {
        name: "MAX_MBQI_FREE_INT_VALUES",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "16",
        unit: "candidate values per symbol",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-0360",
            "2026-07-22",
            None,
            &[sym(
                "crates/axeyum-solver/src/auto.rs",
                "MAX_MBQI_FREE_INT_VALUES",
            )],
            &[adr("ADR-0360")],
        ),
        note: "Per-symbol value pool size for ADR-0360 completion.",
    },
    ConfigEntry {
        name: "MAX_MBQI_INSTANCES",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "4096",
        unit: "ground instances",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Bails to `unknown` past this many accumulated instances EVEN WITH NO WALL-CLOCK BUDGET, which is what makes it a termination bound rather than a time one.",
    },
    ConfigEntry {
        name: "MAX_MBQI_PROFILE_COMPLETION_INSTANCES",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "32",
        unit: "exact source instances",
        protects: Protects::Termination,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "a shorter instance list can only leave the candidate undecided",
        env_override: None,
        justification: dated(
            "ADR-0364",
            "2026-07-23",
            None,
            &[sym(
                "crates/axeyum-solver/src/auto.rs",
                "MAX_MBQI_PROFILE_COMPLETION_INSTANCES",
            )],
            &[adr("ADR-0364")],
        ),
        note: "Companion to the rounds cap; this one does branch explicitly where the rounds cap does not.",
    },
    ConfigEntry {
        name: "MAX_MBQI_PROFILE_COMPLETION_ROUNDS",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "32",
        unit: "candidate-solve rounds",
        protects: Protects::Termination,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the loop's result is a candidate model that is replayed before acceptance",
        env_override: None,
        justification: dated(
            "ADR-0364",
            "2026-07-23",
            None,
            &[sym(
                "crates/axeyum-solver/src/auto.rs",
                "MAX_MBQI_PROFILE_COMPLETION_ROUNDS",
            )],
            &[adr("ADR-0364")],
        ),
        note: "`for _ in 0..32` with no exceeded-signal at the loop site.",
    },
    ConfigEntry {
        name: "MAX_MBQI_ROUNDS",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "16",
        unit: "instantiation rounds",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Detail reads `MBQI did not converge within 16 rounds` — the bound names itself in the `unknown`, which is the pattern the unsignalled entries in this registry lack.",
    },
    ConfigEntry {
        name: "MAX_MILP_NODES",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "2_000",
        unit: "branch-and-bound nodes",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "On exhaustion the caller falls back to the sound coercion relaxation.",
    },
    ConfigEntry {
        name: "MAX_PRE_LIA_UF_PROBE_ASSERTIONS",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "256",
        unit: "assertions",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Records a `ResourceLimit` decline through the route recorder, so the decline is traceable even though the verdict is unaffected.",
    },
    ConfigEntry {
        name: "MBQI_FIRST_REFUSAL_SHARE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "8",
        unit: "divisor of the remaining deadline granted to the route",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The first-refusal MBQI rung's eighth of the remaining budget. A FRACTION, not a reserve: the route takes 1/8 and the rungs below keep 7/8, which is the opposite division from the `*_LADDER_RESERVE_SHARE` entries and the distinction the 2026-09-08 QF_UFLIA measurement paid four files to learn. Named on 2026-09-08; value unchanged and unmeasured.",
    },
    ConfigEntry {
        name: "MIN_LADDER_SLICE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "Duration::from_millis(1)",
        unit: "milliseconds, floor on any route's slice of a ladder's clock",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "docs/research/12-performance/ladder-budget-discipline-2026-09-08.md",
            "2026-09-08",
            None,
            &[
                sym("crates/axeyum-solver/src/auto.rs", "int_real_relax_budget"),
                sym(
                    "crates/axeyum-solver/src/auto.rs",
                    "pre_lia_uf_probe_budget",
                ),
            ],
            &[
                live("int_real_relax_budget", "crates/axeyum-solver/src/auto.rs"),
                doc("docs/research/12-performance/ladder-budget-discipline-2026-09-08.md"),
            ],
        ),
        note: "CLOSES A FINDING recorded against `INT_REAL_RELAX_BUDGET_SHARE`: a route asked for one sixth of the clock used to be handed ALL of it whenever `timeout / 6` rounded to zero, because the helper returned the caller's config unchanged. `pre_lia_uf_probe_budget` had the identical inversion at `timeout / 10`. Both now clamp here instead, so the sharing policy cannot invert at the small-budget end where starvation matters most; the behaviour differs from the old code only under 6 ms and 10 ms respectively. A millisecond rather than zero because a route handed no clock at all is a route DELETED, which is a different policy from a route shared, and this constant is not the place to choose it.",
    },
    ConfigEntry {
        name: "MIN_QUANTIFIED_CONJUNCTS",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "32",
        unit: "quantified top-level conjuncts",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "A FLOOR, not a ceiling: the ground-core accelerator fires only ABOVE it, so it gates where the accelerator's cost is repaid. The only lower-bound gate in this registry.",
    },
    ConfigEntry {
        name: "PRE_LIA_UF_PROBE_CEILING",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "Duration::from_millis(250)",
        unit: "milliseconds, ceiling on the slice granted to the route",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The `250 ms` half of `min(t/10, 250ms)` for the pre-LIA UF probe: a quick screen whose usefulness does not scale with the clock, so its slice is capped as well as divided. Named on 2026-09-08 when the budget arithmetic moved into one policy; value unchanged and unmeasured.",
    },
    ConfigEntry {
        name: "PRE_LIA_UF_PROBE_SHARE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "10",
        unit: "divisor of the caller's deadline granted to the route",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The `/ 10` half of `min(t/10, 250ms)`. Its helper carried the same inversion as `INT_REAL_RELAX_BUDGET_SHARE` -- a tenth that rounded to zero became the FULL timeout -- which `MIN_LADDER_SLICE` now closes. That defect was found by looking for a second instance of a registered FINDING, which is the argument for writing findings down rather than fixing one site quietly.",
    },
    ConfigEntry {
        name: "QINST_EGRAPH_RETRY_SHARE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "2",
        unit: "divisor of the remaining deadline granted to the route",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Half the remaining budget for the incremental e-graph quantifier retry, so the callers' later SAT-only stages are not starved. Was a bare `timeout / 2` inside the dispatch body until 2026-09-08; the doc comment beside it already stated the sharing INTENT, which is exactly the kind of policy a name-keyed registry cannot see while it is written as a literal.",
    },
    ConfigEntry {
        name: "TIMED_ARRAY_REFUTER_SLICE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "Duration::from_millis(250)",
        unit: "milliseconds",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Caps the fast-path array-refuter chain. One line of doc, no measurement.",
    },
    ConfigEntry {
        name: "UF_ARITH_LADDER_RESERVE_SHARE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "4",
        unit: "divisor of the dispatcher's remaining deadline, held back for the ladder",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_UF_ARITH_OVERBOUND"),
        justification: dated(
            "docs/research/12-performance/uf-arith-overbound-2026-09-08.md",
            "2026-09-08",
            None,
            // The measurement is "+9 files on the QF_UFLIA loss population, and
            // `probe` and `skip` decide the same nine". It rests on the routes
            // BELOW the decision point being what decides them — the nine are
            // all decided by `dispatch_uf_arith_online` — and on the CEGAR entry
            // still being the thing that fires above the eager bound. Change
            // either and the number stops describing this tree.
            &[
                sym(
                    "crates/axeyum-solver/src/auto.rs",
                    "dispatch_uf_arith_overbound",
                ),
                sym(
                    "crates/axeyum-solver/src/auto.rs",
                    "dispatch_uf_arith_online",
                ),
                sym(
                    "crates/axeyum-solver/src/euf.rs",
                    "try_lazy_arith_for_overbound",
                ),
            ],
            // The basis names the route the nine gained files are decided BY.
            // If `dispatch_uf_arith_online` leaves auto.rs, the reserve holds a
            // deadline back for a ladder with no rung left, and the +9 stops
            // describing this tree. Naming the constant or the doc would keep
            // passing in exactly that case -- the failure the sibling lane hit
            // in its OWN first basis, where "batsat" still occurred in prose
            // long after the thing the bound rested on had gone.
            &[live(
                "dispatch_uf_arith_online",
                "crates/axeyum-solver/src/auto.rs",
            )],
        ),
        note: "The slice of the budget held back from the lazy-Ackermann CEGAR for the routes \
               under it on an over-bound UF+arithmetic query. Before this constant existed the \
               CEGAR took the WHOLE budget and its `Unknown` was the dispatcher's final answer, \
               so `euf-online`, `euf-offline` and `dispatch_uf_arith_online` were unreachable \
               above 64 congruence pairs; on the 58-file QF_UFLIA loss list that was 52 of 58 \
               files. MEASURED, not copied: the first version halved the budget (mirroring \
               `probe_budget`) and cost FOUR previously-decided files on the 200-file list, all \
               needing more than half the budget (12.7 / 13.3 / 15.5 / 23.7 s), while the nine \
               files it unblocks need 307-625 ms of ladder -- so a reserve is the right shape \
               and a split is not. `4` clears both bounds: 18 s for the CEGAR (above three of \
               the four) and 6 s for the ladder (about ten times 625 ms). The fourth, at 23.7 s \
               of 24, is not recoverable by any reserve and is the named cost of the change. The env override selects the \
               whole policy (`terminal` restores the old behaviour, `skip` removes the CEGAR), \
               not just this divisor.",
    },
    ConfigEntry {
        name: "UF_ARITH_ONLINE_PROBE_SHARE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "2",
        unit: "divisor of the caller's deadline granted to the route",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The `QF_UFLIA`/`QF_UFLRA` online probe's half of the budget in `dispatch_uf_arith_online`. Deliberately left a HALF and not converted to a reserve: the eager fallback below it computes a FRESH deadline at entry, so this is a split across two clocks rather than a share of one, and the 2026-09-08 QF_UFLIA measurement that condemned a half-budget split was about two routes sharing ONE clock. Whether it is wrong here is STILL unmeasured -- this entry was split out of `UFBV_ONLINE_PROBE_SHARE` on 2026-09-10 and deliberately kept undated, because the measurement that motivated the split was on the pure-UF quantified ladder and says nothing about THIS route. Laundering that date onto this row is the exact error the split exists to prevent.",
    },
    ConfigEntry {
        name: "UF_FMF_PROBE_SHARE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "2",
        unit: "divisor of the remaining deadline granted to the route",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "docs/research/03-measurements/where-the-uf-clock-goes-2026-09-10.md",
            "2026-09-10",
            None,
            // The measurement is "retuning this decides nothing new on the 32
            // declared-unsat UF losses and costs a file on the 24 we win". It
            // rests on the finite-model producer being the thing this rung
            // calls, and on that producer ALSO running at a terminal placement
            // below the refuters -- which is why turning the probe down defers
            // the capability instead of removing it. Move either and the
            // measurement stops describing this tree.
            &[
                sym("crates/axeyum-solver/src/uf_fmf.rs", "find_uf_finite_model"),
                sym(
                    "crates/axeyum-solver/src/auto.rs",
                    "finish_quantified_solve",
                ),
            ],
            // The terminal placement is the load-bearing half: the "no verdict
            // is lost" arm holds because `q:uf-fmf-full` picks up what the
            // probe stops finding. `UF_FMF_FULL_SOLVE_ASSERTIONS` exists only
            // for that call site, so it goes when the placement goes.
            &[
                live(
                    "UF_FMF_FULL_SOLVE_ASSERTIONS",
                    "crates/axeyum-solver/src/uf_fmf.rs",
                ),
                live("find_uf_finite_model", "crates/axeyum-solver/src/uf_fmf.rs"),
            ],
        ),
        note: "The pure-UF finite-model PROBE rung's half of what is left, spent before the refutation family runs. MEASURED and deliberately NOT retuned. Three findings, any one of which makes the divisor the wrong lever: (1) it does not bound the rung -- the half grants ~12 000 ms of a 24 000 ms budget and the probe spends up to 19 478 ms, 162% of its grant, on 13 of 32 files; (2) the gain side is empty AT ITS OWN CEILING -- with the probe effectively off, which is strictly more clock than any larger divisor can hand the refuters, the 32 declared-unsat losses decide the same set; (3) the cost side is real -- at 1/16 all 24 axeyum-only wins still decide but PAR-2 goes 19.8 s to 36.1 s, and with the probe off one file is lost outright and PAR-2 goes to 241.6 s. Turning the probe down does not turn finite model finding off, it DEFERS it to the terminal `q:uf-fmf-full` rung, which is why the verdicts mostly survive and the clock does not. Split out of `UFBV_ONLINE_PROBE_SHARE` on 2026-09-10: that name governed no QF_UFBV route at all.",
    },
    ConfigEntry {
        name: "MAX_ATOMS",
        module: "crates/axeyum-solver/src/bool_euf.rs",
        value: "16",
        unit: "equality atoms",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the formula stays available to the other pure-EUF/general deciders; only this exhaustive Boolean-skeleton-enumeration checker declines",
        env_override: Some("AXEYUM_BOOL_EUF_MAX_ATOMS"),
        justification: undated("doc comment"),
        note: "Bounds 2^atoms exhaustive Boolean-skeleton enumeration for a checked Boolean-structured EUF refutation (`bool_euf_exhaustive_refutation`).",
    },
    ConfigEntry {
        name: "MAX_BLAST_WIDTH",
        module: "crates/axeyum-solver/src/bv2nat_blast.rs",
        value: "128",
        unit: "bit-vector result width (bits)",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The whole equivalence-preserving blast pass declines (`Ok(None)`) above this width. The doc ties it to `bv_const` taking a `u128`, but frames the guard as part of the module's soundness argument ('checked u128/i128; any overflow or a result width past MAX_BLAST_WIDTH declines. No wrong verdict is possible') rather than as incidental type plumbing, so it is registered rather than treated as purely structural.",
    },
    ConfigEntry {
        name: "MAX_BOUND_WIDTH",
        module: "crates/axeyum-solver/src/bv2nat_bound.rs",
        value: "62",
        unit: "bit-vector width (bits)",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "leaving a wider bv2nat(b) unabstracted keeps the original (still correct) formula unchanged; the range fact `0 <= n <= 2^W - 1` is only ever a helper toward decidability, so omitting it forgoes completeness, it cannot make a verdict wrong",
        env_override: None,
        justification: undated("doc comment"),
        note: "62 is chosen with margin ('2^62 - 1 fits comfortably in i128', doc) rather than forced by i128's actual ~2^127 range, so this is a discretionary policy choice, not a type-tied structural constant. Per-symbol: skipping one wide bv2nat term is not distinguishable in the return type from that term never being a candidate, hence Signal::None rather than ToCaller.",
    },
    ConfigEntry {
        name: "MAX_CASES",
        module: "crates/axeyum-solver/src/bv_defined_enum.rs",
        value: "20_000",
        unit: "enumerated independent assignments",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("no written justification"),
        note: "No doc comment at the definition site. Gates the whole `BvDefinedEnumRefutationCertificate` route: `cases = ...; if cases == 0 || cases > MAX_CASES { return None; }` (bv_defined_enum.rs:100) ends the certificate attempt entirely, propagated via `?` to the caller. The actual global admission gate on total enumerated work in this file.",
    },
    ConfigEntry {
        name: "MAX_RESTRICTION_DAG_NODES",
        module: "crates/axeyum-solver/src/bv_defined_enum.rs",
        value: "128",
        unit: "term DAG nodes",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("no written justification"),
        note: "No doc comment at the definition site. Per-constraint filter (bv_defined_enum.rs:373): a domain-restricting constraint over this DAG-node count is not used to shrink a symbol's finite domain (`return None` from `match_single_symbol_constraint_by_enumeration`). Does not end the whole certificate by itself — `MAX_CASES` is the actual global admission gate on total enumerated cases — but is a directly observed decline in this helper's own return type.",
    },
    ConfigEntry {
        name: "MAX_SYMBOL_WIDTH",
        module: "crates/axeyum-solver/src/bv_defined_enum.rs",
        value: "16",
        unit: "bit-vector/float width (bits)",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("no written justification"),
        note: "No doc comment at the definition site. Two roles: (1) a range-comparison recognizer declines to treat `x < c` / `x <= c` as a domain restriction above this width (bv_defined_enum.rs:472, `return None`); (2) `full_domain` (bv_defined_enum.rs:669-670) returns `None` for any BitVec/Float sort wider than this, so such a symbol gets no enumerable domain at all. `MAX_CASES` remains the actual global admission gate on total enumerated cases.",
    },
    ConfigEntry {
        name: "MAX_LOCAL_BV_WIDTH",
        module: "crates/axeyum-solver/src/bv_uf_local.rs",
        value: "8",
        unit: "bit-vector width (bits)",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "wider BV symbols are simply excluded from this local-certificate's candidate set (bv_uf_local.rs:171); equalities derived over the included symbols are still exhaustively evaluator-checked, so excluding a symbol can only miss a derivation, never validate a wrong one",
        env_override: Some("AXEYUM_MAX_LOCAL_BV_WIDTH"),
        justification: undated("no written justification"),
        note: "No doc comment at the definition site. Filters candidate symbols at collection; paired with MAX_LOCAL_ENUM_BITS, which bounds the resulting pairwise enumeration.",
    },
    ConfigEntry {
        name: "MAX_LOCAL_ENUM_BITS",
        module: "crates/axeyum-solver/src/bv_uf_local.rs",
        value: "12",
        unit: "bits (enumeration is 2^bits cases)",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("no written justification"),
        note: "No doc comment at the definition site. Bounds the exhaustive-enumeration case count (`1_u64.checked_shl(total_bits)`, up to 2^12 = 4096) at two sites (bv_uf_local.rs:199, :284); both `return None`/`continue`, propagated to the caller.",
    },
    ConfigEntry {
        name: "MAX_ATOMS",
        module: "crates/axeyum-solver/src/cas_certificate.rs",
        value: "512",
        unit: "opaque atoms",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`check_cas_identity_certificate`/`check_cas_int_units_certificate`/`check_cas_ideal_certificate` independently re-derive the refutation from the original assertions before any `CasOutcome::Refuted` is accepted; `expand` returning `None` past this bound can only decline the cas-* route (`CasOutcome::VerifierRejected`/`NotRefuted`), never accept an unverified one.",
        env_override: Some("AXEYUM_CAS_MAX_ATOMS"),
        justification: undated("doc comment"),
        note: "Shared by both halves of the CAS bridge: `cas_poly.rs`'s discovery routes (`cas_identity_refutation`, `cas_ideal_refutation`, ...) and this file's independent re-derivation checker both call `expand`/`to_poly` under this same cap (imported via `crate::cas_certificate::{MAX_ATOMS, ...}`), so crossing it declines the cas-* route on both the producer and checker side identically.",
    },
    ConfigEntry {
        name: "MAX_DEPTH",
        module: "crates/axeyum-solver/src/cas_certificate.rs",
        value: "256",
        unit: "recursion levels",
        protects: Protects::Termination,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "same as `MAX_ATOMS` in this file: the checker independently re-derives before accepting, so declining past this depth can only forgo a decision.",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"so a pathologically deep left-nested sum cannot exhaust the stack (`deep_nesting_no_abort` guards this class)\" — doc comment at the definition site.",
    },
    ConfigEntry {
        name: "MAX_MONOMIALS",
        module: "crates/axeyum-solver/src/cas_certificate.rs",
        value: "4096",
        unit: "monomials",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "same as `MAX_ATOMS` in this file: the checker independently re-derives before accepting, so declining past this bound can only forgo a decision.",
        env_override: Some("AXEYUM_CAS_MAX_MONOMIALS"),
        justification: undated("doc comment"),
        note: "\"A product of two dense polynomials multiplies term counts, so this bounds the whole expansion\" — doc comment. Same name, different module and value (16), as `nra_handelman_cert.rs::MAX_MONOMIALS` — unrelated engines (exact rational-polynomial expansion vs. Fourier-Motzkin monomial abstraction), not a divergent twin.",
    },
    ConfigEntry {
        name: "MAX_STEPS",
        module: "crates/axeyum-solver/src/cas_certificate.rs",
        value: "200_000",
        unit: "visited term nodes",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "same as `MAX_ATOMS` in this file: the checker independently re-derives before accepting, so declining past this bound can only forgo a decision.",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"the walk is bounded by a deterministic step count rather than a wall clock (determinism is a public API promise)\" — doc comment at the definition site.",
    },
    ConfigEntry {
        name: "MAX_IDEAL_ATOMS",
        module: "crates/axeyum-solver/src/cas_poly.rs",
        value: "8",
        unit: "opaque atoms",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`cas_ideal_refutation`'s candidate is independently re-checked by `check_cas_ideal_certificate` before any `CasOutcome::Refuted` is returned; exceeding this returns `CasOutcome::NotRefuted`, never an unverified accept.",
        env_override: Some("AXEYUM_MAX_IDEAL_ATOMS"),
        justification: undated("doc comment"),
        note: "\"Buchberger under lex is doubly exponential in the variable count in the worst case, so this is the ceiling that actually bounds the search; the step budget [`ideal_limits`] is the backstop\" — doc comment. `ideal_limits()` in this file also sets bare-literal step ceilings (`reduction_steps: 6_000`, `pair_iterations: 1_500`, `basis_size: 32`, `poly_terms: 256`) with a comment noting they are \"unchanged from before the order became a knob\" — these are struct-literal fields, not named constants, so `config_registry_scan.py` does not surface them; flagged here as bare-literal search guards at cas_poly.rs:552-557 (`fn ideal_limits`).",
    },
    ConfigEntry {
        name: "MAX_IDEAL_GENERATORS",
        module: "crates/axeyum-solver/src/cas_poly.rs",
        value: "8",
        unit: "asserted equations",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "same as `MAX_IDEAL_ATOMS` in this file: `check_cas_ideal_certificate` re-derives before acceptance.",
        env_override: Some("AXEYUM_MAX_IDEAL_GENERATORS"),
        justification: undated("doc comment"),
        note: "Ceiling on asserted equations used as Groebner-basis ideal generators for the multivariate CAS route (`cas_ideal_refutation`); exceeding it returns `CasOutcome::NotRefuted(\"nonlinear system exceeds the deterministic generator/atom/inequality ceilings\")`.",
    },
    ConfigEntry {
        name: "MAX_IDEAL_INEQUALITIES",
        module: "crates/axeyum-solver/src/cas_poly.rs",
        value: "8",
        unit: "asserted inequalities",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "same as `MAX_IDEAL_ATOMS` in this file: `check_cas_ideal_certificate` re-derives before acceptance.",
        env_override: Some("AXEYUM_MAX_IDEAL_INEQUALITIES"),
        justification: undated("doc comment"),
        note: "Ceiling on asserted inequalities considered as combination terms in `cas_ideal_refutation`; also used to `inequalities.truncate(MAX_IDEAL_INEQUALITIES)` after the admission check, so a query at exactly the cap keeps all its inequalities and one over it declines outright rather than being silently truncated.",
    },
    ConfigEntry {
        name: "MAX_POSITIVITY_CANDIDATES",
        module: "crates/axeyum-solver/src/cas_poly.rs",
        value: "24",
        unit: "candidate terms",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "`try_positivity_combination`'s output still passes through `check_cas_ideal_certificate` before any `CasOutcome::Refuted` is returned, so a truncated candidate list can only miss a refutation, never accept a wrong one.",
        env_override: None,
        justification: undated("doc comment"),
        note: "`build_candidates` does `sources.truncate(MAX_POSITIVITY_CANDIDATES)` after collecting single/product/square candidates — later candidates are silently dropped rather than the search declining.",
    },
    ConfigEntry {
        name: "MAX_POSITIVITY_SUBSET",
        module: "crates/axeyum-solver/src/cas_poly.rs",
        value: "3",
        unit: "candidates per combination",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "same as `MAX_POSITIVITY_CANDIDATES` in this file: `check_cas_ideal_certificate` re-derives before acceptance.",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"It is deliberately incomplete: general non-negative multipliers are a linear program over the residues, which is not wired. A refutation needing `2x^2 + 3y^2` is missed.\" — doc comment; the search only ever tries unit-coefficient subsets up to this size.",
    },
    ConfigEntry {
        name: "DEADLINE_CHECK_LITERALS",
        module: "crates/axeyum-solver/src/cdclt.rs",
        value: "256",
        unit: "trail literals between deadline polls",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Deadline-poll cadence, not an admission bound: too large widens the 'deadline-blind window' before a timeout is honoured; too small pays a clock read per propagated literal. Doc: 'Small enough that the deadline-blind window stays negligible next to a seconds-scale budget, large enough that the clock is not read once per propagated literal.'",
    },
    ConfigEntry {
        name: "DEFAULT_STEP_BUDGET",
        module: "crates/axeyum-solver/src/cdclt.rs",
        value: "16_000_000",
        unit: "main-loop iterations",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Defense in depth for a run with no wall-clock deadline. `lra_online.rs::DEFAULT_STEP_BUDGET` is already registered with an independent copy of the same name and value, and its own note anticipates this entry verbatim ('cdclt.rs holds an independent copy of the same name and value; the two are not linked') — this is that copy.",
    },
    ConfigEntry {
        name: "GLUE_LBD",
        module: "crates/axeyum-solver/src/cdclt.rs",
        value: "2",
        unit: "LBD",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Glucose's glue threshold, a search-quality heuristic (registered so a reader auditing this file's caps sees it is NOT an admission gate). Byte-identical value to `lra_online.rs::GLUE_LBD`, already registered there with the same classification and the same caveat; the two are independent copies, not linked.",
    },
    ConfigEntry {
        name: "LUBY_UNIT",
        module: "crates/axeyum-solver/src/cdclt.rs",
        value: "100",
        unit: "conflicts",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Restart cadence unit. `lra_online.rs::LUBY_UNIT`'s registered note already names this file: 'Duplicated in `cdclt.rs` and in `axeyum-cnf`'s two CDCL cores; four copies of the same number, none linked' — this is the `cdclt.rs` copy that note pointed at but did not itself register.",
    },
    ConfigEntry {
        name: "REDUCE_FIRST",
        module: "crates/axeyum-solver/src/cdclt.rs",
        value: "2_000",
        unit: "learned clauses",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Clause-database reduction schedule base. Same name AND value as `lra_online.rs::REDUCE_FIRST` (registered, whose note already says 'Duplicated across four CDCL cores in this workspace') — this is one of those four, independently defined.",
    },
    ConfigEntry {
        name: "REDUCE_INCREMENT",
        module: "crates/axeyum-solver/src/cdclt.rs",
        value: "300",
        unit: "learned clauses",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Reduction schedule increment. `lra_online.rs` spells the same constant `REDUCE_INC` (registered, same value 300, note: '`axeyum-cnf` spells the same constant `REDUCE_INCREMENT`; same value, different name, no link'). `axeyum-cnf/src/xor_cdcl.rs::REDUCE_INCREMENT` is that file — same spelling as HERE, same value, not itself registered (xor_cdcl.rs is not a GOVERNED_FILES entry). Three copies, two spellings, one value, none linked.",
    },
    ConfigEntry {
        name: "VSIDS_DECAY",
        module: "crates/axeyum-solver/src/cdclt.rs",
        value: "0.95",
        unit: "activity multiplier per conflict",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "One of four independent copies in the workspace (`lra_online.rs` — registered, note: 'Four independent copies exist in the workspace' —, `axeyum-cnf/src/xor_cdcl.rs`, `axeyum-cnf/src/proof_sat.rs`); this is the `cdclt.rs` copy that count already includes but does not itself register.",
    },
    ConfigEntry {
        name: "VSIDS_RESCALE",
        module: "crates/axeyum-solver/src/cdclt.rs",
        value: "1e-100",
        unit: "activity multiplier",
        protects: Protects::Soundness,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Prevents f64 overflow of activity scores on long runs. `Protects::Soundness` here means arithmetic soundness of the VSIDS heuristic, not of the verdict (matches `lra_online.rs::VSIDS_RESCALE`'s registered classification; same value, independent copy).",
    },
    ConfigEntry {
        name: "VSIDS_RESCALE_LIMIT",
        module: "crates/axeyum-solver/src/cdclt.rs",
        value: "1e100",
        unit: "activity score",
        protects: Protects::Soundness,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The trigger for the VSIDS_RESCALE above (`if self.activity[var] > VSIDS_RESCALE_LIMIT`). Independent copy of `lra_online.rs::VSIDS_RESCALE_LIMIT` (registered, same value).",
    },
    ConfigEntry {
        name: "MAX_SPLIT_PAIRS",
        module: "crates/axeyum-solver/src/combined_theory.rs",
        value: "64",
        unit: "interface case-split pairs",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "FINDING (four unlinked copies of one bound). `if pairs.len() > MAX_SPLIT_PAIRS { return decline(...) }`; `decline()` returns `CheckResult::Unknown` directly. This file's own doc comment says it 'mirrors the cold core's `MAX_SPLIT_DEPTH` decline so the warm and cold paths reject the same oversized splits identically' — but nothing in code links them: `uflia_online.rs::MAX_SPLIT_DEPTH` and `uflra_online.rs::MAX_SPLIT_DEPTH` are two more independent `= 64` copies carrying a byte-identical doc comment to EACH OTHER, and `combined_theory_lia.rs::MAX_SPLIT_PAIRS` is a fourth, with the same 'mirrors the cold core's MAX_SPLIT_DEPTH' claim as this file. Four names/files, one intended meaning, one value, zero code-level links.",
    },
    ConfigEntry {
        name: "DEFER_COMBINED_LIA_FEASIBILITY_ATOMS",
        module: "crates/axeyum-solver/src/combined_theory_lia.rs",
        value: "128",
        unit: "theory atoms",
        protects: Protects::Time,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "deferred mode reuses `lia_online::LiaTheory`'s own deferred-feasibility machinery (`new_with_opaque_apps_deferred_for_large_search`), which still performs one full feasibility check at the propagation boundary before a model is accepted (test: 'deferred feasibility conflict should surface as a propagation'), so deferring cannot ship a wrong verdict, only change when infeasibility is discovered",
        env_override: None,
        justification: undated("doc comment"),
        note: "Doc: 'Mirror the pure-LIA online large-query threshold' — same value (128) as `lia_online.rs::DEFER_LIA_FEASIBILITY_ATOMS`, independently defined, not linked in code beyond both routing through the same `LiaTheory` deferred mode.",
    },
    ConfigEntry {
        name: "MAX_SPLIT_PAIRS",
        module: "crates/axeyum-solver/src/combined_theory_lia.rs",
        value: "crate::uflia_interface::MAX_INTERFACE_PAIRS",
        unit: "interface case-split pairs",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Effective value 64, through `crate::uflia_interface::MAX_INTERFACE_PAIRS` since 2026-09-08 — this copy and `uflia_online.rs::MAX_SPLIT_DEPTH` are now ONE definition, so the \"mirrors the cold core\" claim below is enforced by the compiler instead of by prose. Byte-identical doc comment to `combined_theory.rs::MAX_SPLIT_PAIRS` ('mirroring the cold core's `MAX_SPLIT_DEPTH` decline...'), same value, independent definition — see that entry's note for the full four-copy chain across this file, `combined_theory.rs`, `uflia_online.rs::MAX_SPLIT_DEPTH`, and `uflra_online.rs::MAX_SPLIT_DEPTH`.",
    },
    ConfigEntry {
        name: "MAX_CYCLE_WALK",
        module: "crates/axeyum-solver/src/dl_online.rs",
        value: "1 << 20",
        unit: "parent-pointer steps",
        protects: Protects::Termination,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the caller then reports no conflict, which is always a legal under-approximation",
        env_override: None,
        justification: undated("doc comment"),
        note: "Defense in depth around cycle extraction.",
    },
    ConfigEntry {
        name: "MAX_DL_ATOMS",
        module: "crates/axeyum-solver/src/dl_online.rs",
        value: "1 << 20",
        unit: "distinct difference-logic atoms",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the query is routed to another theory engine, which decides it or returns `unknown`",
        env_override: None,
        justification: undated("doc comment"),
        note: "`atom()` returns `None` on size, which at the call site is INDISTINGUISHABLE from `this term is not difference-shaped` — one signal for a size refusal and a structural decline, the same class as the unit mismatch ADR-1751 fixed. The return value still cannot tell them apart; since 2026-09-08 a `note_crossed` call at the gate does, so a `--trace` run can attribute the route change even though the caller cannot.",
    },
    ConfigEntry {
        name: "MAX_PROPAGATION_PROBES",
        module: "crates/axeyum-solver/src/dl_online.rs",
        value: "64",
        unit: "unassigned-atom probes per call",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "propagation is an optimisation; per-assert cycle detection still runs",
        env_override: None,
        justification: undated("doc comment"),
        note: "Not a completeness bound — the pruning layer only offers literals the search could derive anyway.",
    },
    ConfigEntry {
        name: "MAX_PROPAGATION_VERTICES",
        module: "crates/axeyum-solver/src/dl_online.rs",
        value: "256",
        unit: "graph vertices",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "as above: propagation-only",
        env_override: None,
        justification: undated("doc comment"),
        note: "Above it the probing loop does not run at all.",
    },
    ConfigEntry {
        name: "MAX_SCALE",
        module: "crates/axeyum-solver/src/dl_online.rs",
        value: "1 << 40",
        unit: "LCM of bound denominators",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`scan_dl` returning `None` declines the whole difference-logic route, so the query is decided by another engine or reported `unknown`",
        env_override: None,
        justification: undated("doc comment"),
        note: "Keeps scaled path-sum weights inside `i128` headroom; the route declines rather than overflowing.",
    },
    ConfigEntry {
        name: "MAX_BELLMAN_FORD_DIFF_EDGES",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "256",
        unit: "difference-logic edges",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "no negative-cycle core is produced; the search continues without that lemma",
        env_override: Some("AXEYUM_MAX_BELLMAN_FORD_DIFF_EDGES"),
        justification: undated("doc comment"),
        note: "FINDING (ordering). This is TIGHTER than `MAX_TWO_EDGE_DIFF_EDGES` (512), the cheap pre-check that feeds it — so the cheap check admits inputs twice as large as the thorough fallback behind it. Neither number is measured and the relationship is undocumented. Recorded, not changed.",
    },
    ConfigEntry {
        name: "MAX_CERTIFIABLE_BOOLS",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "22",
        unit: "Boolean symbols",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "FINDING (divergent twin). Here it only SWITCHES the verification method — exhaustive enumeration below, `recheck_for_bool_terms` above — so a result stays checkable either way. In `dpll_t.rs` a constant of the same name and the same value `22` DECLINES the certificate outright. Same name, same number, different contract; nothing links them.",
    },
    ConfigEntry {
        name: "MAX_DPLL_ROUNDS",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "10_000",
        unit: "lazy-SMT refinement rounds",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Detail names the bound: `exceeded N refinement rounds`.",
    },
    ConfigEntry {
        name: "MAX_DYNAMIC_AFFINE_BOUND_CONFLICT_BATCH",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "1",
        unit: "conflicts per batch",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "fewer lemmas per call only slows convergence",
        env_override: None,
        justification: undated("doc comment"),
        note: "A batch size of exactly one: this pass yields at most one lemma per call.",
    },
    ConfigEntry {
        name: "MAX_DYNAMIC_BOUND_CONFLICT_BATCH",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "32",
        unit: "conflicts per batch",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "fewer lemmas per call only slows convergence",
        env_override: None,
        justification: undated("doc comment"),
        note: "Caps one batch's lemma yield.",
    },
    ConfigEntry {
        name: "MAX_DYNAMIC_LARGE_CORE_LITERALS",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "8_192",
        unit: "literals in unminimized wide cores",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The live SAT-solver memory guard. The doc names the incident file (`sal/tgc/tgc_io-safe-20.smt2`, 1.8 GB growing to an 8 GB abort, 24 cores of ~430 literals) but NO DATE, so it is exactly the shape that went stale for thirteen months elsewhere.",
    },
    ConfigEntry {
        name: "MAX_INITIAL_BOUND_IMPLICATION_ATOMS",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "512",
        unit: "atoms in the abstractor",
        protects: Protects::Time,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "the pass only ADDS valid lemmas, so skipping it cannot change a verdict",
        env_override: None,
        justification: undated("doc comment"),
        note: "Gates whether the implication-lemma pre-seeding pass runs at all; above it the whole pass is skipped silently.",
    },
    ConfigEntry {
        name: "MAX_INITIAL_BOUND_IMPLICATION_LEMMAS",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "4_096",
        unit: "implication bound lemmas",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the pass only adds valid lemmas",
        env_override: None,
        justification: undated("doc comment"),
        note: "Silent truncation of a pre-seeding pass.",
    },
    ConfigEntry {
        name: "MAX_INITIAL_BOUND_MUTEX_LEMMAS",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "8_192",
        unit: "mutex bound lemmas",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the pass only adds valid lemmas",
        env_override: None,
        justification: undated("doc comment"),
        note: "Silent truncation of a pre-seeding pass.",
    },
    ConfigEntry {
        name: "MAX_MODERATE_PRE_SAT_ARITH_ATOMS",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "10_240",
        unit: "arithmetic atoms",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "docs/research/12-performance/admission-limit-basis-2026-09-08.md",
            "2026-09-08",
            Some("317be80fe"),
            &[
                sym(
                    "crates/axeyum-solver/src/dpll_lia.rs",
                    "MAX_MODERATE_PRE_SAT_ARITH_ATOMS",
                ),
                sym("crates/axeyum-cnf/src/lib.rs", "IncrementalSat"),
            ],
            &[
                adr("ADR-1703"),
                live("NativeIncrementalCdcl", "crates/axeyum-cnf/src/lib.rs"),
                commit("317be80fe", "the native CDCL core is the SAT engine"),
                doc("docs/research/12-performance/admission-limit-basis-2026-09-08.md"),
            ],
        ),
        note: "THE ENVELOPE THAT ACTUALLY DECIDES ADMISSION; the pre-SAT trigger alone refuses nothing. Widened 1_280 -> 10_240 on 2026-09-08 by re-derivation against the native CDCL core: at 9,846 atoms the whole process peaks at 71 MiB, 1/115th of the 8 GiB ceiling the old BatSat-era justification cited, and 3 of 10 QF_LIA files it was refusing are decided when it is raised. Set to the largest point MEASURED safe, not extrapolated beyond it.",
    },
    ConfigEntry {
        name: "MAX_MODERATE_PRE_SAT_CNF_VARS",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "16_384",
        unit: "CNF variables",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "docs/research/12-performance/admission-limit-basis-2026-09-08.md",
            "2026-09-08",
            Some("317be80fe"),
            &[
                sym(
                    "crates/axeyum-solver/src/dpll_lia.rs",
                    "MAX_MODERATE_PRE_SAT_CNF_VARS",
                ),
                sym("crates/axeyum-cnf/src/lib.rs", "IncrementalSat"),
            ],
            &[
                adr("ADR-1703"),
                live("NativeIncrementalCdcl", "crates/axeyum-cnf/src/lib.rs"),
                commit("317be80fe", "the native CDCL core is the SAT engine"),
                doc("docs/research/12-performance/admission-limit-basis-2026-09-08.md"),
            ],
        ),
        note: "Joint partner to the moderate atom bound; both must hold. Widened 8_192 -> 16_384 with it on 2026-09-08. A query at 31,944 CNF variables still declines: that is 1.9x the measured region in a dimension nobody has measured above.",
    },
    ConfigEntry {
        name: "MAX_PRE_SAT_ARITH_ATOMS",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "1_024",
        unit: "arithmetic atoms",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "docs/research/12-performance/admission-limit-basis-2026-09-08.md",
            "2026-09-08",
            Some("317be80fe"),
            &[
                sym(
                    "crates/axeyum-solver/src/dpll_lia.rs",
                    "MAX_PRE_SAT_ARITH_ATOMS",
                ),
                sym("crates/axeyum-cnf/src/lib.rs", "IncrementalSat"),
            ],
            &[
                adr("ADR-1703"),
                live("NativeIncrementalCdcl", "crates/axeyum-cnf/src/lib.rs"),
                commit("317be80fe", "the native CDCL core is the SAT engine"),
                doc("docs/research/12-performance/admission-limit-basis-2026-09-08.md"),
            ],
        ),
        note: "A FLOOR, not the decision: a query crossing it is still admitted inside the moderate envelope, so nothing is refused on this number alone, and it has not moved. Its 2026-08-08 justification blamed BatSat's allocator on `pursuit-safety-16.smt2`; ADR-1703 took BatSat off this path on 2026-09-05, `IncrementalBatSat` occurs nowhere in `crates/`, and the cited file is QF_LRA and does not reach this gate. The founding case for `scripts/check-admission-limit-basis.py`.",
    },
    ConfigEntry {
        name: "MAX_PRE_SAT_CNF_VARS",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "4_096",
        unit: "CNF variables",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "docs/research/12-performance/admission-limit-basis-2026-09-08.md",
            "2026-09-08",
            Some("317be80fe"),
            &[
                sym(
                    "crates/axeyum-solver/src/dpll_lia.rs",
                    "MAX_PRE_SAT_CNF_VARS",
                ),
                sym("crates/axeyum-cnf/src/lib.rs", "IncrementalSat"),
            ],
            &[
                adr("ADR-1703"),
                live("NativeIncrementalCdcl", "crates/axeyum-cnf/src/lib.rs"),
                commit("317be80fe", "the native CDCL core is the SAT engine"),
                doc("docs/research/12-performance/admission-limit-basis-2026-09-08.md"),
            ],
        ),
        note: "Joint partner to the pre-SAT atom bound; a floor, not the decision.",
    },
    ConfigEntry {
        name: "MAX_TWO_EDGE_DIFF_EDGES",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "512",
        unit: "difference-logic edges",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the search continues without a difference core; the full LIA oracle has already said the conjunction is unsat, and any core that IS returned is still checked by the normal arithmetic lemma verifier",
        env_override: Some("AXEYUM_MAX_TWO_EDGE_DIFF_EDGES"),
        justification: undated("doc comment"),
        note: "See `MAX_BELLMAN_FORD_DIFF_EDGES` for the ordering finding.",
    },
    ConfigEntry {
        name: "MINIMIZATION_ORACLE_CALL_BUDGET",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "4 * MAX_DYNAMIC_LARGE_CORE_LITERALS",
        unit: "theory-oracle calls",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "a partially minimized core is still a valid conflict core",
        env_override: None,
        justification: dated(
            "docs/research/05-algorithms/, 2026-08-21 section 5.2",
            "2026-08-21",
            None,
            &[sym(
                "crates/axeyum-solver/src/dpll_lia.rs",
                "MINIMIZATION_ORACLE_CALL_BUDGET",
            )],
            &[doc("docs/research/05-algorithms/")],
        ),
        note: "Counted in oracle calls rather than wall clock DELIBERATELY, so the bound is deterministic. Derived from another registered constant, so it moves when that one does.",
    },
    ConfigEntry {
        name: "OVERSIZED_ADMISSION_PROBE_BUDGET",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "Duration::from_secs(10)",
        unit: "seconds",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "A bounded probe offered to an oversized query before it declines outright. The doc gives a measured floor of ~7-8 s on an idle taskset-pinned host, but no date.",
    },
    ConfigEntry {
        name: "WIDE_THEORY_CORE_ATOMS",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "128",
        unit: "atoms in a retained theory core",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-21",
            None,
            &[sym(
                "crates/axeyum-solver/src/dpll_lia.rs",
                "WIDE_THEORY_CORE_ATOMS",
            )],
            // The 2026-08-21 note's whole content is that this constant STOPPED
            // deciding whether minimization is attempted and became pure
            // accounting against the wide-core budget. Both halves of that
            // sentence must still name something.
            &[
                live(
                    "MAX_DYNAMIC_LARGE_CORE_LITERALS",
                    "crates/axeyum-solver/src/dpll_lia.rs",
                ),
                live(
                    "MINIMIZATION_ORACLE_CALL_BUDGET",
                    "crates/axeyum-solver/src/dpll_lia.rs",
                ),
            ],
        ),
        note: "ACCOUNTING, NOT ADMISSION. Until 2026-08-21 the same constant was an admission width-gate; the doc records why that was the wrong direction. It now only decides whether a retained core counts against `MAX_DYNAMIC_LARGE_CORE_LITERALS`. Registered because a reader who greps the name will otherwise assume the old contract.",
    },
    ConfigEntry {
        name: "MAX_CERTIFIABLE_BOOLS",
        module: "crates/axeyum-solver/src/dpll_t.rs",
        value: "22",
        unit: "Boolean symbols",
        protects: Protects::Soundness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "FINDING (two contracts, one file). `finish_certified_unsat` (dpll_t.rs:512): `bools.len() > MAX_CERTIFIABLE_BOOLS` returns `Ok(LraDpllOutcome::Unknown(UnknownReason{kind:Incomplete,..}))` — a soft decline, matches `RefuseUnknown`/`ToCaller`. `LraDpllRefutation::verify` (dpll_t.rs:576), called independently by `evidence.rs` to re-check ALREADY-PRODUCED evidence, hits the SAME check and instead returns `Err(SolverError::Unsupported(...))` — a hard error ending the route rather than a first-class `Unknown`. One constant, two crossing contracts, in the same file. Also the twin of `dpll_lia.rs::MAX_CERTIFIABLE_BOOLS` (registered; same name, same value 22) whose own note flags dpll_t.rs as a 'divergent twin' by name — but that note describes dpll_lia.rs's OWN contract (`DeclineRoute`, switches verification method only) and does not capture that dpll_t.rs itself carries two different contracts internally.",
    },
    ConfigEntry {
        name: "MAX_ROUNDS",
        module: "crates/axeyum-solver/src/dpll_t.rs",
        value: "100_000",
        unit: "lazy-SMT refinement rounds",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Backstop against a refinement-loop bug (doc: 'the loop is otherwise bounded by the number of distinct atom assignments'). Three call sites (dpll_t.rs:146, 256, 421) all format the bound into the `Unknown` detail. Distinct value from `dpll_lia.rs::MAX_DPLL_ROUNDS` (10_000, registered) — different file, different number, not a duplicate.",
    },
    ConfigEntry {
        name: "SKELETON_SOLVE_DEFAULT",
        module: "crates/axeyum-solver/src/dpll_t.rs",
        value: "SkeletonSolvePolicy::COLD",
        unit: "policy arm for the lazy-SMT propositional half",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::None,
        guarded_by: "both arms decide the SAME clause set in every round -- the warm solver holds the skeleton plus every blocking clause learned so far, which is exactly what the cold arm rebuilds from `skeleton + blocking` -- so the round's verdict cannot differ between them and only the cost can; `dpll_t::tests::the_warm_and_cold_arms_agree_round_by_round` drives a whole blocking sequence to exhaustion comparing the two rather than comparing one call, because a single-round comparison cannot see an assertion that diverges across rounds, which is the warm arm's only failure mode. A skeleton outside the warm arm's scope falls back to the cold arm (`skeleton_is_pure_boolean`), so an unsupported shape is never silently dropped",
        env_override: Some("AXEYUM_LAZY_SKELETON"),
        justification: dated(
            "docs/research/12-performance/qf-nra-loss-attribution-2026-09-09.md",
            "2026-09-09",
            None,
            // The measurement is "on the seven `LassoRanker` files of the
            // `QF_NRA` loss population the lazy-SMT loop spent 97-99% of a 24 s
            // budget in the propositional half and ~1% in the theory, with a
            // per-round histogram monotone in the round number". It rests on
            // the loops still rebuilding `skeleton + blocking` per round (the
            // thing the warm arm removes), on the warm solver still taking
            // monotone assertions, and on the counters that split a round into
            // its two halves. Change any of the three and the numbers stop
            // describing this tree.
            &[
                sym(
                    "crates/axeyum-solver/src/dpll_t.rs",
                    "check_with_nra_dpll_within",
                ),
                sym(
                    "crates/axeyum-solver/src/incremental.rs",
                    "IncrementalBvSolver",
                ),
                sym(
                    "crates/axeyum-solver/src/lazy_smt_counters.rs",
                    "record_skeleton",
                ),
            ],
            // The basis names the applicability guard and the warm solver the
            // arm is built on. If `skeleton_is_pure_boolean` leaves `dpll_t.rs`
            // the warm arm has no admission test and would take skeletons that
            // still carry theory content; a basis naming only the doc would
            // keep passing through exactly that change.
            &[
                live(
                    "skeleton_is_pure_boolean",
                    "crates/axeyum-solver/src/dpll_t.rs",
                ),
                live(
                    "IncrementalBvSolver",
                    "crates/axeyum-solver/src/incremental.rs",
                ),
                doc("docs/research/12-performance/qf-nra-loss-attribution-2026-09-09.md"),
            ],
        ),
        note: "Which arm the lazy-SMT loops use for the propositional half. The skeleton NEVER changes between rounds — only the learned blocking clauses grow, monotonically — so the pre-2026-09-09 `cold` arm re-bit-blasted an identical formula and reran CDCL from scratch over a strictly larger clause set every round, and the per-round cost rose with the round number (`polyrank4` reads `nra_hist=2:3,3:12,4:23,5:34,6:61,7:118,8:62`, `nra_max_round=306`: ~4 ms early, ~256 ms late). The `warm` arm asserts the skeleton once into an `IncrementalBvSolver` (ADR-0009) and appends each blocking clause. The DEFAULT is `cold`, set from the A/B and not from the mechanism: on the 16 skeleton-dominated QF_NRA parity losses (one binary, arms differing only in this env override) `warm` is a 3-4x speedup of the propositional half where that half is not already the whole budget (1,211 -> 263 ms, 1,674 -> 570 ms, 480 -> 122 ms) and DECIDED NOTHING NEW (cold 2 of 16, warm 2 of 16, the same two files); on the seven LassoRanker files it is a wash, because there the cost is the CDCL search over hundreds of whole-cube blocking clauses, not the re-encoding. This switch changes the propositional half of EVERY lazy-SMT query in the workspace, and 16 files of one division is not a basis for that; a division-wide A/B is now one binary and one env var. Both arms decide the SAME clause set in every round, so a verdict cannot differ between them; `the_warm_and_cold_arms_agree_round_by_round` drives a whole blocking sequence to hold that. The warm arm is only applicable to a pure propositional skeleton (`skeleton_is_pure_boolean`); anything else falls back to `cold`, which is also what `AXEYUM_LAZY_SKELETON=cold` selects, so the A/B is one binary. This is NOT a fix for the largest QF_NRA class — 14 files decline on an atom capacity they exceed by 11-36x, which no scheduling change reaches.",
    },
    ConfigEntry {
        name: "DECLARED_SORT_CEGAR_PAIRS_TERMINAL_RUNG",
        module: "crates/axeyum-solver/src/euf.rs",
        value: "16_384",
        unit: "congruence pairs",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "docs/research/11-design-review/2026-09-06-s11a-uf-ackermann-measured.md",
            "2026-09-06",
            None,
            &[sym(
                "crates/axeyum-solver/src/euf.rs",
                "DECLARED_SORT_CEGAR_PAIRS_TERMINAL_RUNG",
            )],
            &[doc(
                "docs/research/11-design-review/2026-09-06-s11a-uf-ackermann-measured.md",
            )],
        ),
        note: "The same gate as `MAX_ENCODED_DECLARED_SORT_CEGAR_PAIRS`, 256x looser because as the ladder's terminal rung there is no downstream search left to starve. Here the number bounds MEMORY (the O(pairs) preseed scan), not time, which the shared deadline already bounds.",
    },
    ConfigEntry {
        name: "MAX_ACKERMANN_CONGRUENCE_PAIRS",
        module: "crates/axeyum-solver/src/euf.rs",
        value: "64",
        unit: "congruence pairs",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "STALE, and the highest-cost bound in this table: it is reported to carry 52 of 58 QF_UFLIA losses through `try_lazy_arith_for_overbound`. A real measurement exists - `6233a7c98` (2026-06-24) gives the decidable frontier (40 pairs), the smallest observed hang (117), a k=60 run unbounded past 200s and a k=700 stack overflow - and this entry is deliberately NOT dated to it. `eliminate_functions`, the O(k^2) expansion the bound exists to keep bounded, has changed FIVE times since, most recently `7da79642f` on 2026-09-07, so the measurement describes a tree that is gone. The signature query `git log -G'fn eliminate_functions'` is EMPTY over the same window: the signature did not move, the body did, and only the wider query sees it. Re-deriving this against today's expansion is owed by the lane that owns the route; dating it now would be moving the date.",
    },
    ConfigEntry {
        name: "MAX_ENCODED_DECLARED_SORT_CEGAR_PAIRS",
        module: "crates/axeyum-solver/src/euf.rs",
        value: "64",
        unit: "congruence pairs",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "docs/research/11-design-review/2026-09-06-s11a-uf-ackermann-measured.md",
            "2026-09-06",
            None,
            // NOT the constant's own name: `8d5ba48f0` (2026-09-08) touched it
            // in a rustdoc-link fix, which `git log -G` cannot tell from a code
            // change. This names the function the measurement was of.
            &[sym(
                "crates/axeyum-solver/src/euf.rs",
                "check_qf_ufbv_lazy_with_pair_bound",
            )],
            &[doc(
                "docs/research/11-design-review/2026-09-06-s11a-uf-ackermann-measured.md",
            )],
        ),
        note: "The non-terminal caller's value: bounded so the route cannot steal an enclosing search's budget. 1.6x margin over a then-measured 40-pair frontier; the date of that measurement is not recorded.",
    },
    ConfigEntry {
        name: "MAX_LAZY_ACKERMANN_CONGRUENCE_PAIRS",
        module: "crates/axeyum-solver/src/euf.rs",
        value: "2_000_000",
        unit: "congruence pairs",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Refuses an astronomically large pair set before repeated per-candidate scanning; graceful rather than an OOM.",
    },
    ConfigEntry {
        name: "MAX_LAZY_DAG_NODES",
        module: "crates/axeyum-solver/src/euf.rs",
        value: "2_000_000",
        unit: "assertion-DAG nodes",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Bounds the memoized DAG-linear rewrite for the lazy route.",
    },
    ConfigEntry {
        name: "MAX_LAZY_DEPTH",
        module: "crates/axeyum-solver/src/euf.rs",
        value: "65_536",
        unit: "term-tree depth",
        protects: Protects::Soundness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "A stack-overflow guard: the recursive rewrite can overflow before any deadline check fires. The doc names the crash-report commit `6233a7c` — a commit, but still no date.",
    },
    ConfigEntry {
        name: "MAX_POST_CANDIDATE_SIBLING_LEMMAS",
        module: "crates/axeyum-solver/src/euf.rs",
        value: "1",
        unit: "sibling lemmas per candidate",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the pass only adds valid congruence lemmas",
        env_override: None,
        justification: undated("doc comment"),
        note: "Silent truncation, one line of doc. Same shape as `nia_linearize::MAX_CONGRUENCE_GROUPS`.",
    },
    ConfigEntry {
        name: "MAX_PRESEEDED_FUNCTION_CONSISTENCY_LEMMAS",
        module: "crates/axeyum-solver/src/euf.rs",
        value: "256",
        unit: "congruence lemmas",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the pass only adds valid congruence lemmas",
        env_override: None,
        justification: undated("doc comment"),
        note: "`if count >= MAX .. { return Ok(count) }` — silent truncation of the seeding loop, one line of doc.",
    },
    ConfigEntry {
        name: "EUF_ONLINE_ABSTRACT_CEILING",
        module: "crates/axeyum-solver/src/euf_egraph.rs",
        value: "Duration::from_secs(2)",
        unit: "seconds of the caller's remaining budget",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: Some("AXEYUM_EUF_ONLINE_ATOMS"),
        justification: dated(
            "docs/research/12-performance/euf-online-arith-atoms-2026-09-08.md",
            "2026-09-08",
            None,
            // The ceiling rests on `euf-online` remaining a cheap SCREEN on a
            // UF+arithmetic query rather than the ladder's main hope. If
            // `dispatch_uf_arith_online` -- the online model-based EUF+LIA
            // combination that runs after it -- leaves `auto.rs`, or if this
            // route stops being reached from `dispatch_uf_fast_paths`, then
            // capping it at two seconds is capping the only route left and the
            // reasoning inverts.
            &[
                sym("crates/axeyum-solver/src/auto.rs", "dispatch_uf_fast_paths"),
                sym(
                    "crates/axeyum-solver/src/auto.rs",
                    "dispatch_uf_arith_online",
                ),
                sym(
                    "crates/axeyum-solver/src/euf_egraph.rs",
                    "check_qf_uf_online_cdclt",
                ),
            ],
            &[
                live(
                    "dispatch_uf_arith_online",
                    "crates/axeyum-solver/src/auto.rs",
                ),
                doc("docs/research/12-performance/euf-online-arith-atoms-2026-09-08.md"),
            ],
        ),
        note: "The flat half of `min(remaining/4, 2s)`, applied ONLY on a query where the skeleton encoder had to abstract a Boolean-position subterm. WHAT THE MEASUREMENT ESTABLISHES, and what it does not. On the committed 200-file `QF_UFLIA` parity list, one binary and three arms (`scripts/euf-online-atoms-sweep.sh`, 2026-09-08): the route abstracted on 68 files, DECIDED 6 of them in 1-9 ms (max 9 ms), and on the other 62 spent a median of 8 ms and a maximum of 1,159 ms before declining. So this ceiling is 200x the slowest decision -- it cannot cost a decision -- and **it did not fire on any file in this population**: the SHARE binds first at the 24 s competition budget (the route receives ~6 s after the over-bound CEGAR, and 6/4 = 1.5 s < 2 s), and 1,159 ms is under both. It is insurance against a query outside this population, not a bound anything was measured against, and this note says so rather than implying a fit. It exists because abstracting turns a 1.3 ms decline into a route that SPENDS time on every UF+arithmetic query, and the routes below it -- `euf-offline`, `ufbv-online`, `uf-arith-online` -- run on what it leaves. A query that abstracted NOTHING keeps the caller's whole timeout under every arm, so pure `QF_UF` is unaffected in budget as well as in verdict. The env override selects the whole policy (`refuse` restores the pre-2026-09-08 behaviour, `whole` removes the slice), not just this ceiling.",
    },
    ConfigEntry {
        name: "EUF_ONLINE_ABSTRACT_SHARE",
        module: "crates/axeyum-solver/src/euf_egraph.rs",
        value: "4",
        unit: "divisor of the caller's remaining budget granted to the route",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: Some("AXEYUM_EUF_ONLINE_ATOMS"),
        justification: dated(
            "docs/research/12-performance/euf-online-arith-atoms-2026-09-08.md",
            "2026-09-08",
            None,
            &[
                sym("crates/axeyum-solver/src/auto.rs", "dispatch_uf_fast_paths"),
                sym(
                    "crates/axeyum-solver/src/euf_egraph.rs",
                    "check_qf_uf_online_cdclt",
                ),
            ],
            &[
                live(
                    "dispatch_uf_arith_online",
                    "crates/axeyum-solver/src/auto.rs",
                ),
                doc("docs/research/12-performance/euf-online-arith-atoms-2026-09-08.md"),
            ],
        ),
        note: "A FRACTION, not a reserve -- the fourth copy of this quarter and the first that GRANTS rather than withholds. `ABV_ONLINE_LADDER_RESERVE_SHARE`, `DL_LADDER_RESERVE_SHARE` and `UF_ARITH_LADDER_RESERVE_SHARE` each hold a quarter BACK from a route that is the ladder's main hope; this one hands a quarter TO a route that is a screen, because on a UF+arithmetic query the architecture's bet is `uf-arith-online` below it (the shape Z3's `setup_QF_UFLIA` registers). This is the operative half of `min(remaining/4, 2s)` at the 24 s competition budget: the route is entered with ~6 s left after the over-bound CEGAR, so this divisor yields 1.5 s and the ceiling (2 s) never binds. Same 2026-09-08 measurement as `EUF_ONLINE_ABSTRACT_CEILING`, and the same honest limit -- the largest spend observed on the 200-file list was 1,159 ms, UNDER the 1.5 s this grants, so neither bound actually truncated a run in the population that justified them. What the population does establish is the delta they made safe: 151 -> 156 decided, +5 / -0, with no verdict disagreement between the three arms.",
    },
    ConfigEntry {
        name: "PRE_SOLVE_ALETHE_MAX_NODES",
        module: "crates/axeyum-solver/src/evidence.rs",
        value: "2_000",
        unit: "term DAG nodes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_PRE_SOLVE_ALETHE_MAX_NODES"),
        justification: undated("doc comment"),
        note: "Used at TWO sites with opposite direction on the same constant. Definition-site use (`zero_trust_alethe_certificate`, ~line 3000): admits the pre-solve Alethe attempt only when the DAG is WITHIN this cap; standard DeclineRoute. Second use in `dl_decided_report` (~line 2602): the difference-logic fallback route is skipped for queries WITHIN the cap and ACTIVATES for queries above it, because (measured, doc comment) on a 200-file QF_RDL parity list \"the evidence front door decided 2 files while the solver front door decided 105\" when this fallback was absent — crossing the cap there converts what the doc calls an otherwise-`unknown` result into an honest bare `unsat`, hence `Signal::ToCaller`. No fallback exists below either direction of this gate other than the other route, so treat this as one admission threshold partitioning work between two complementary evidence strategies, not two independent bounds.",
    },
    ConfigEntry {
        name: "PRE_SOLVE_ARRAY_AXIOM_DAG_LIMIT",
        module: "crates/axeyum-solver/src/evidence.rs",
        value: "256",
        unit: "term DAG nodes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`produce_evidence`'s other routes (array elimination, the backend solve) still decide and attach evidence for the same query; this constant only skips a fast pre-solve array-axiom certificate attempt (`small_pre_solve_array_axiom_refutation` returns `None`).",
        env_override: Some("AXEYUM_PRE_SOLVE_ARRAY_AXIOM_DAG_LIMIT"),
        justification: undated("no written justification"),
        note: "A function-local `const` with no doc comment justifying the number, unlike its `PRE_SOLVE_ALETHE_MAX_NODES` neighbor in the same file.",
    },
    ConfigEntry {
        name: "MAX_BODY_ATOMS",
        module: "crates/axeyum-solver/src/horn.rs",
        value: "8",
        unit: "predicate atoms per clause body",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`if clause.body.len() > MAX_BODY_ATOMS { return HornOutcome::Unknown(...) }` (horn.rs:1064); detail names the bound. Doc: 'A wider body declines to `HornOutcome::Unknown` rather than risk a blow-up.'",
    },
    ConfigEntry {
        name: "MAX_SCC_MEMBERS",
        module: "crates/axeyum-solver/src/horn.rs",
        value: "16",
        unit: "SCC members",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Doc: 'Beyond this, the tagged-union state and clause count grow past a safe bound and the SCC declines to Unknown.' Detail names the bound (horn.rs:1858-1860).",
    },
    ConfigEntry {
        name: "MAX_SCC_STATE_WIDTH",
        module: "crates/axeyum-solver/src/horn.rs",
        value: "32",
        unit: "state columns (argument arity)",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Doc: 'A wider tuple declines rather than risk an engine blow-up.' Detail names the bound (horn.rs:1868-1870).",
    },
    ConfigEntry {
        name: "DEFAULT_MAX_PROBES",
        module: "crates/axeyum-solver/src/hypothesis_min.rs",
        value: "4000",
        unit: "solver probes",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Default for `MinimizeConfig::max_probes`, overridable per call. Exhausting it makes `minimize_hypotheses`/`split_goal_and_minimize` return `Ok(MinimizeOutcome::NotFound { probes })` — this module's own first-class \"gave up\" result, directly analogous to a solver `unknown`, for the separate hypothesis-minimisation search (not the main `Solver::check` dispatch).",
    },
    ConfigEntry {
        name: "DEFAULT_MAX_SUBSET_SIZE",
        module: "crates/axeyum-solver/src/hypothesis_min.rs",
        value: "4",
        unit: "hypotheses",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_DEFAULT_MAX_SUBSET_SIZE"),
        justification: undated("doc comment"),
        note: "Default for `MinimizeConfig::max_subset_size`, overridable per call. Caps the cardinality the ascending-size search enumerates; a sufficient subset larger than this is never found and the search reports `MinimizeOutcome::NotFound` rather than an unsound smaller result — soundness of any subset it DOES report comes from re-checking with `¬goal` present (module doc), unaffected by this bound.",
    },
    ConfigEntry {
        name: "DEFAULT_PROBE_BUDGET",
        module: "crates/axeyum-solver/src/hypothesis_min.rs",
        value: "Duration::from_millis(250)",
        unit: "wall-clock duration per probe",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Default for `MinimizeConfig::probe_budget`, overridable per call. A probe that times out contributes toward the search's own `MinimizeOutcome::NotFound` give-up. Doc comment cites a specific measurement (route-B session, `docs/plan/proof-approaches-2026-08-12/route-b/`) but does not date-stamp THIS value's derivation precisely enough to cite as a `dated()` basis without inventing a linkage.",
    },
    ConfigEntry {
        name: "MAX_REPLAY_SHARED_MEMO_ENTRIES",
        module: "crates/axeyum-solver/src/incremental.rs",
        value: "4_096",
        unit: "evaluator memo entries",
        protects: Protects::Memory,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "clearing the shared memo only forces re-evaluation of already-checked subterms; `eval_with_memo` recomputes correctly against a cleared cache, so this can only cost extra time, never affect the replay verdict",
        env_override: None,
        justification: undated("doc comment"),
        note: "In `IncrementalBvSolver::replay`, `memo.clear()` fires once the cross-root evaluator memo reaches this size; per the doc comment it bounds only what is retained BETWEEN replay roots, not what one root's evaluation may need.",
    },
    ConfigEntry {
        name: "MAX_WARM_ARRAY_UF_APPS_PER_ROOT",
        module: "crates/axeyum-solver/src/incremental.rs",
        value: "64",
        unit: "array-backed UF applications per replay root",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "an assertion whose warm-array admission budget is exceeded is deferred (`frame.deferred_assertions`) and folded into the ordinary (non-warm) check path instead of the incremental fast path; declining the fast path can only cost incrementality performance, never a wrong verdict",
        env_override: None,
        justification: undated("no written justification"),
        note: "Part of the same admission-check family as MAX_WARM_STRUCTURAL_ARRAY_NODES/_DEPTH (`record_warm_array_parent_limits`, `warm_array_parent_covers`); no doc comment on this one specifically.",
    },
    ConfigEntry {
        name: "MAX_WARM_STRUCTURAL_ARRAY_DEPTH",
        module: "crates/axeyum-solver/src/incremental.rs",
        value: "256",
        unit: "nested store/ite layers walked",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "an assertion whose warm-array admission budget is exceeded is deferred (`frame.deferred_assertions`) and folded into the ordinary (non-warm) check path instead of the incremental fast path; declining the fast path can only cost incrementality performance, never a wrong verdict",
        env_override: None,
        justification: undated("no written justification"),
        note: "`depth > MAX_WARM_STRUCTURAL_ARRAY_DEPTH` in `warm_array_parent_covers` (an iterative explicit-stack walk with its own `seen` cycle guard, so this bounds chain length, not infinite recursion) and as a loop bound inside `realize_warm_structural_array_term`'s store/ite chain walker, where exhausting it returns `WarmStructuralRealization::Incompatible` gracefully (unlike abv.rs's analogous MAX_STRUCTURAL_ARRAY_REALIZATION_STEPS, which ends in a hard Err via its caller).",
    },
    ConfigEntry {
        name: "MAX_WARM_STRUCTURAL_ARRAY_NODES",
        module: "crates/axeyum-solver/src/incremental.rs",
        value: "512",
        unit: "structural array nodes / prospective reads",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "an assertion whose warm-array admission budget is exceeded is deferred (`frame.deferred_assertions`) and folded into the ordinary (non-warm) check path instead of the incremental fast path; declining the fast path can only cost incrementality performance, never a wrong verdict",
        env_override: None,
        justification: undated("no written justification"),
        note: "Used three ways: (1) `prospective_reads <= MAX_WARM_STRUCTURAL_ARRAY_NODES` admission check in `warm_array_equality_observation_budget_holds`; (2) `structural_nodes > MAX_WARM_STRUCTURAL_ARRAY_NODES` in `warm_array_parent_covers`/`record_warm_array_parent_limits`; (3) a raw loop bound in `realize_warm_structural_array_term` (`for _step in 0..MAX_WARM_STRUCTURAL_ARRAY_NODES`), where exhaustion returns `WarmStructuralRealization::Incompatible` gracefully. Also the value that defines MAX_WARM_STRUCTURAL_REFINEMENT_ROUNDS (`= MAX_WARM_STRUCTURAL_ARRAY_NODES`); the two are NOT the same constant as abv.rs's MAX_ROW_ROUNDS/MAX_ROW_SITES despite similar names and this file's 512 vs abv.rs's 4096/64.",
    },
    ConfigEntry {
        name: "MAX_WARM_STRUCTURAL_REFINEMENT_ROUNDS",
        module: "crates/axeyum-solver/src/incremental.rs",
        value: "MAX_WARM_STRUCTURAL_ARRAY_NODES",
        unit: "warm structural CEGAR refinement rounds",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("no written justification"),
        note: "`refinement_rounds >= MAX_WARM_STRUCTURAL_REFINEMENT_ROUNDS` returns `IncrementalSolveOutcome::unknown(UnknownReason { kind: ResourceLimit, detail: \"warm structural refinement exceeded {MAX_WARM_STRUCTURAL_REFINEMENT_ROUNDS} candidate rounds\" })`, naming the bound in the detail. Defined AS `MAX_WARM_STRUCTURAL_ARRAY_NODES` (currently 512) rather than its own literal, so changing that node cap silently changes this round budget too -- a derived/twin value, not an independent one.",
    },
    ConfigEntry {
        name: "DEFAULT_INT_WIDTH",
        module: "crates/axeyum-solver/src/lia.rs",
        value: "32",
        unit: "bit-vector width (bits)",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "GAP FILL: this definition site itself was unregistered. `auto.rs::INT_BLAST_MAX_WIDTH` is already registered with `value: \"DEFAULT_INT_WIDTH\"` and a note explaining the indirection ('VALUE IS INDIRECT... defined in lia.rs, so this file's ladder top moves if that constant moves') — but hard rule 1 requires `module` to name the DEFINITION site, which had no entry of its own. Per the module doc, a bit-vector `sat` that fails integer replay, or a bit-vector `unsat`, both degrade to `Unknown` ('the bound is too small for this model' / 'no model *in range*') rather than a wrong verdict. This is also the DIRECT (non-ladder) default width used by `dpll_t.rs`, `euf.rs`, and `auto.rs`'s non-ladder call sites, independent of the `INT_BLAST_MAX_WIDTH` ladder.",
    },
    ConfigEntry {
        name: "DEFER_LIA_FEASIBILITY_ATOMS",
        module: "crates/axeyum-solver/src/lia_online.rs",
        value: "128",
        unit: "LIA atoms",
        protects: Protects::Time,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "the deferred theory still performs a full feasibility check at the propagation boundary before a model is accepted (`deferred_feasibility_conflict`), and any `Sat` model is independently re-verified by `replays_integer` before being returned, so deferring cannot ship a wrong verdict, only change when infeasibility is discovered",
        env_override: None,
        justification: undated("doc comment"),
        note: "Companion to `DEFER_LIA_FEASIBILITY_CLAUSES` (same file; `should_defer_online_lia_feasibility` ORs the two checks). Crossing either switches `check_qf_lia_online` from eager per-assignment feasibility checking to `LiaTheory::new_deferred_for_large_search`. Same value (128) as `combined_theory_lia.rs::DEFER_COMBINED_LIA_FEASIBILITY_ATOMS`, whose own doc calls this constant its mirror.",
    },
    ConfigEntry {
        name: "DEFER_LIA_FEASIBILITY_CLAUSES",
        module: "crates/axeyum-solver/src/lia_online.rs",
        value: "4096",
        unit: "Tseitin clauses",
        protects: Protects::Time,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "same mechanism as DEFER_LIA_FEASIBILITY_ATOMS: the deferred theory still performs a full feasibility check at the propagation boundary, and any Sat model is re-verified by replays_integer, so deferring cannot ship a wrong verdict",
        env_override: None,
        justification: undated("doc comment"),
        note: "Clause-count companion to `DEFER_LIA_FEASIBILITY_ATOMS`; doc: 'for generated Boolean skeletons with fewer theory atoms but a large Tseitin surface.'",
    },
    ConfigEntry {
        name: "BYTES_PER_FARKAS_MULTIPLIER",
        module: "crates/axeyum-solver/src/lra.rs",
        value: "32",
        unit: "bytes per retained Farkas multiplier",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_MEMORY_LIMIT_MB"),
        justification: dated(
            "docs/research/12-performance/span-log-sweep-2026-09-08.md",
            "2026-09-08",
            Some("5d406a12b"),
            &[
                sym(
                    "crates/axeyum-solver/src/lra.rs",
                    "BYTES_PER_FARKAS_MULTIPLIER",
                ),
                sym("crates/axeyum-solver/src/lra.rs", "MAX_FM_CONSTRAINTS"),
            ],
            // The value is STRUCTURAL, so what has to still exist is the shape
            // it counts (`Rational` is two `i128`s inside `LinExpr`'s home
            // crate) and the two gates that spend it, plus the sweep the
            // measurement is written up in.
            &[
                live("pub struct Rational", "crates/axeyum-ir/src/rational.rs"),
                live("fn fm_admission", "crates/axeyum-solver/src/lra.rs"),
                live(
                    "fn simplex_tableau_bytes",
                    "crates/axeyum-solver/src/lra.rs",
                ),
                live("fn reset_structure", "crates/axeyum-solver/src/simplex.rs"),
                doc("docs/research/12-performance/span-log-sweep-2026-09-08.md"),
            ],
        ),
        note: "The constant behind the 2026-09-08 kernel OOM. `decide_within` gave every collected constraint a dense unit multiplier vector of length `n`, so `32*n^2` bytes, allocated BEFORE `MAX_FM_CONSTRAINTS` -- the one bound that could have stopped it -- was consulted inside `eliminate`. At ~29 200 constraints that matrix is the kernel's own `anon-rss:26639452kB`. Unlike a divided peak-RSS figure this is a count of what the program allocates, so it cannot drift with corpus or host; the only thing that invalidates it is changing `Rational`'s representation, which is what the first `Basis` watches. `simplex_admission` charges the exact-rational simplex retry at the same rate deliberately -- two gates metering one resource in different units is the defect this registry exists to surface -- but on its TABLEAU and not on its input rows: `Tableau::reset_structure` builds `m` dense rows of `nvars + m` cells, so it is quadratic in the row count too. Pricing it as `n * nvars` was tried and let 11.8 GB through after the multiplier matrix was already gated; a stack sample found the real allocation inside `reset_structure`, 17x the projection. Related gap, reported and NOT closed here: `simplex::MAX_TABLEAU_CELLS` (4 000 000) is checked only in `Incremental::new`, so `feasible` -- the constructor this route calls -- consults no cell bound at all and reached 360 million cells on the measured file.",
    },
    ConfigEntry {
        name: "GOMORY_MAGNITUDE_LIMIT",
        module: "crates/axeyum-solver/src/lra.rs",
        value: "1 << 40",
        unit: "tableau coefficient numerator/denominator magnitude",
        protects: Protects::Soundness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Keeps Gomory tableau arithmetic 'well inside i128 even after repeated pivots/cuts' (doc). Checked at cut-generation and the coefficient-magnitude gate (lra.rs:1885, 1895, 1982-1983); part of the same 'graceful unknown, never OOM, never a loop, never a wrong verdict' family as the other three Gomory constants below.",
    },
    ConfigEntry {
        name: "LP_RELAXATION_CORE_MINIMIZE_LIMIT",
        module: "crates/axeyum-solver/src/lra.rs",
        value: "24",
        unit: "unsat-core atoms",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the caller re-verifies the (possibly unminimized) core is infeasible via `lp_relaxation_feasibility_with_options` immediately after `minimize_lp_relaxation_core` returns, erroring `'lia LP unsat-core self-check failed'` if it is not — skipping minimization cannot ship a wrong core, only a larger one",
        env_override: None,
        justification: undated("doc comment"),
        note: "`minimize_lp_relaxation_core` returns `()` (lra.rs:1651-1652): `if core.len() > LP_RELAXATION_CORE_MINIMIZE_LIMIT { return; }` — nothing in the return type reports whether minimization ran, hence `Signal::None` rather than `ToCaller`.",
    },
    ConfigEntry {
        name: "MAX_FM_CONSTRAINTS",
        module: "crates/axeyum-solver/src/lra.rs",
        value: "20_000",
        unit: "constraints from one elimination step",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "FINDING (independent duplicate, one already registered). `lra_online.rs::MAX_FM_CONSTRAINTS` is already registered (same name, same value 20_000, `protects: Memory`, `on_exceed: DeclineRoute`) but is a SEPARATE `const` definition in a separate file (lra_online.rs:79) governing a different code path (the online incremental driver) from this one (lra.rs:900, the offline exact-rational Fourier-Motzkin `eliminate`). Same name, same value, two files, unlinked. Here the doc frames it as a `Time`/uninterruptibility guard ('a tight loop with no theory callbacks... declines to unknown deterministically... reproducible regardless of machine speed'), not the memory guard the other entry documents ('the 7.8 GB abort on `danoint-266.smt2`'), so the two entries' `protects` genuinely differ even though the number matches.",
    },
    ConfigEntry {
        name: "MAX_GOMORY_COLS",
        module: "crates/axeyum-solver/src/lra.rs",
        value: "1024",
        unit: "tableau structural columns",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "'above this we decline (unknown)' — risk of 'a large dense pivot blow-up' (doc); checked at lra.rs:1859, 2081.",
    },
    ConfigEntry {
        name: "MAX_GOMORY_ROUNDS",
        module: "crates/axeyum-solver/src/lra.rs",
        value: "16",
        unit: "cut-and-re-solve rounds",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Cut-and-re-solve round cap (lra.rs:2205, `for _round in 0..MAX_GOMORY_ROUNDS`); exhausting it ends the Gomory cutting-plane loop with a graceful `unknown` rather than cutting forever.",
    },
    ConfigEntry {
        name: "MAX_GOMORY_ROWS",
        module: "crates/axeyum-solver/src/lra.rs",
        value: "256",
        unit: "tableau rows (constraints)",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "'above this we decline (unknown) rather than risk a large dense pivot blow-up' (doc); checked at lra.rs:1855, 2081.",
    },
    ConfigEntry {
        name: "MAX_LIA_BNB_NODES",
        module: "crates/axeyum-solver/src/lra.rs",
        value: "50_000",
        unit: "branch-and-bound nodes",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Node budget when the caller set NO wall clock (doc: 'the deterministic backstop for deadline-free callers... with no clock to bound the search, the node count is the only reproducible stop'). Companion to MAX_LIA_BNB_NODES_DEADLINED, used when a clock IS set.",
    },
    ConfigEntry {
        name: "MAX_LIA_BNB_NODES_DEADLINED",
        module: "crates/axeyum-solver/src/lra.rs",
        value: "20_000_000",
        unit: "branch-and-bound nodes",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Node budget when the caller DID set a wall clock — 400x looser than MAX_LIA_BNB_NODES because the deadline (polled at every node) is the meaningful bound here; this is a pure runaway-memory backstop. Doc quantifies a real finding with no date attached: on the QF_LIA CAV_2009_benchmarks family the tighter 50,000-node cap fired 'after 0.11-0.31 s of a 24 s budget - about 1% used', short-circuiting the remaining 99% of the caller's budget for nothing. No date or commit is given, so `undated` per rule 4 rather than inventing one.",
    },
    ConfigEntry {
        name: "TIGHTEN_COEFF_LIMIT",
        module: "crates/axeyum-solver/src/lra.rs",
        value: "1 << 62",
        unit: "coefficient/constant magnitude",
        protects: Protects::Soundness,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "leaving a large-coefficient constraint 'strict' (untightened) is exactly the constraint as originally derived; Fourier-Motzkin over the untightened form is still complete for LRA, so skipping the integer-tightening strengthening only forgoes an optimization, it cannot make the result wrong",
        env_override: None,
        justification: undated("doc comment"),
        note: "Guards `gcd`/`floor` arithmetic in the integer-tightening step against i128 overflow (doc: 'above this the constraint is left strict (sound, no tightening) so the gcd/floor arithmetic below cannot overflow i128'). No caller-visible branch: the tightened-count return value doesn't distinguish 'skipped for magnitude' from any other reason a constraint wasn't tightened.",
    },
    ConfigEntry {
        name: "DEFAULT_MAX_CACHED_LIA_LITERALS",
        module: "crates/axeyum-solver/src/lra/warm.rs",
        value: "1 << 16",
        unit: "cached literals (two per registered LIA atom)",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::None,
        guarded_by: "Nothing needs to guard it: crossing it declines no route and drops no \
                     constraint. The literal is collected per check instead of being cached, and \
                     the assembled system, the engines and the verdict are identical either way \
                     -- which is checked, not asserted, by \
                     `lra::warm::tests::an_evicted_literal_cache_changes_nothing_but_the_work`. \
                     `LiaCounters::warm_literal_cache_evicted` records that it fired.",
        env_override: Some("AXEYUM_LIA_WARM"),
        justification: undated("doc comment"),
        note: "Registered because `AXEYUM_LIA_WARM` governs which offline QF_LIA path runs, and an \
               A/B whose arms are not in the run's own output is not reproducible from it. The cap \
               itself is a runaway-memory backstop, not a tuning knob: the population is one \
               query's atom set, and the online LIA theory is only built below its own admission \
               bound, so it is not expected to fire on any query that theory accepts. The env \
               variable does not select this VALUE -- it selects the whole `LiaWarmPolicy` \
               (`off` = the pre-warm cold path, `nofilter` = warm with the rational filter \
               switched off, unset = warm with it kept, which is the shipped default) -- which is \
               why it is attached to the only registered constant the policy carries.",
    },
    ConfigEntry {
        name: "BYTES_PER_ADMITTED_ATOM",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "DEFAULT_ONLINE_LRA_BUDGET_BYTES / 1_024",
        unit: "bytes per atom",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-1752",
            "2026-09-08",
            Some("5d406a12b"),
            &[
                sym(
                    "crates/axeyum-solver/src/lra_online.rs",
                    "BYTES_PER_ADMITTED_ATOM",
                ),
                sym(
                    "crates/axeyum-solver/src/lra_theory.rs",
                    "MAX_ONLINE_LRA_ATOMS",
                ),
            ],
            // Re-derived 2026-09-08. The value is kept for the ONE property that
            // is checkable in the tree rather than in a corpus run -- it
            // reproduces `MAX_ONLINE_LRA_ATOMS` exactly at the default budget --
            // so `MAX_ONLINE_LRA_ATOMS` is a basis, not just a dependency. The
            // sweep is a basis because it is where the mis-attribution that the
            // re-derivation corrects is written down, and `fm_admission` is a
            // basis because it is the gate that now owns the bytes this
            // constant was blamed for.
            &[
                adr("ADR-1752"),
                live(
                    "MAX_ONLINE_LRA_ATOMS",
                    "crates/axeyum-solver/src/lra_theory.rs",
                ),
                live("fn fm_admission", "crates/axeyum-solver/src/lra.rs"),
                doc("docs/research/12-performance/span-log-sweep-2026-09-08.md"),
            ],
        ),
        note: "A SCREEN, explicitly not a cost model. RE-DERIVED 2026-09-08 and the value KEPT, but its evidence changed: the doc named `_sanfoundry_10_ground.i_6_3_3.bpl_13.smt2` aborting at 7.8 GB as the falsification of cost model 1, and a live stack sample at 4.4 GB on the way to a 26.6 GB kernel OOM put those bytes in `lra::decide_within` -- the OFFLINE Fourier-Motzkin route, which no cost model of the ONLINE construction could have predicted. The value survives on the property that is checkable in-tree (it reproduces the flat 1,024-atom cap byte-identically at the default budget) rather than on a corpus measurement that belonged to another route. The 8 GiB this screen derives 13,107 atoms from was ALSO not an enforced budget until 2026-09-08; it is one now.",
    },
    ConfigEntry {
        name: "BYTES_PER_LRA_COEFFICIENT",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "224",
        unit: "bytes per retained coefficient",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-1752",
            "2026-09-07",
            None,
            &[sym(
                "crates/axeyum-solver/src/lra_online.rs",
                "BYTES_PER_LRA_COEFFICIENT",
            )],
            &[adr("ADR-1752")],
        ),
        note: "Structural byte accounting, NOT an RSS measurement — the doc says so explicitly. Feeds `NormalizationLimits::for_budget`'s derived ceilings.",
    },
    ConfigEntry {
        name: "BYTES_PER_TABLEAU_CELL",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "32",
        unit: "bytes per dense-tableau cell",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-1752",
            "2026-09-07",
            None,
            &[sym(
                "crates/axeyum-solver/src/lra_online.rs",
                "BYTES_PER_TABLEAU_CELL",
            )],
            &[adr("ADR-1752")],
        ),
        note: "Two `i128`s. Subtracted from the budget before coefficients get their share.",
    },
    ConfigEntry {
        name: "DEFAULT_ONLINE_LRA_BUDGET_BYTES",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "640 * 1_024 * 1_024",
        unit: "bytes",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_MEMORY_LIMIT_MB"),
        justification: dated(
            "ADR-1752",
            "2026-09-07",
            None,
            // NOT the constant's own name, and not `MAX_ONLINE_LRA_ATOMS`. Both
            // were, and `79a7c5297` tripped this entry STALE on a single added
            // line: a rustdoc reference to `DEFAULT_ONLINE_LRA_BUDGET_BYTES`
            // inside a doc comment. `git log -G` cannot tell that from a code
            // change, and it should not try. These two name the MECHANISMS
            // ADR-1752's decision is about — the derivation of the coefficient
            // ceilings out of the budget, and the route that takes it — so a
            // change to either is a change to what was measured.
            &[
                sym("crates/axeyum-solver/src/lra_online.rs", "for_budget"),
                sym(
                    "crates/axeyum-solver/src/lra_theory.rs",
                    "check_qf_lra_online_cdclt",
                ),
            ],
            &[adr("ADR-1752")],
        ),
        note: "THE REPLACEMENT for the stale flat atom cap. Used when `SolverConfig::memory_limit_mb` is unset; when it is set, that is the budget instead — so this is the first bound in the registry that MOVES with a caller-supplied resource limit rather than being fixed at compile time. The 2026-09-07 date SURVIVES the 2026-09-08 re-derivation of `BYTES_PER_ADMITTED_ATOM` deliberately: that re-derivation changed which EVIDENCE the screen rests on (a 7.8 GB abort turned out to be on the offline Fourier-Motzkin route) and established that `memory_limit_mb` did not bind until 2026-09-08. Neither touches this value, which is chosen so `NormalizationLimits::for_budget`'s derived ceilings sit right and so the screen reproduces 1,024 exactly — a calibration identity checkable in the tree, not a corpus measurement.",
    },
    ConfigEntry {
        name: "DEFAULT_STEP_BUDGET",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "16_000_000",
        unit: "main-loop iterations",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::None,
        guarded_by: "the driver's `None` becomes a first-class `Unknown`, which is always a permitted verdict; crossing this can cost a decision, never produce one",
        env_override: None,
        justification: undated("doc comment"),
        note: "Defense in depth for a run with no wall-clock deadline (wasm32, or a config with no timeout). `cdclt.rs` holds an independent copy of the same name and value; the two are not linked.",
    },
    ConfigEntry {
        name: "GLUE_LBD",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "2",
        unit: "LBD",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Glucose's glue threshold. A search-quality heuristic, registered because a reader auditing this file's caps should see that it is NOT an admission gate.",
    },
    ConfigEntry {
        name: "LUBY_UNIT",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "100",
        unit: "conflicts",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Restart cadence unit. Duplicated in `cdclt.rs` and in `axeyum-cnf`'s two CDCL cores; four copies of the same number, none linked.",
    },
    ConfigEntry {
        name: "MAX_BOUND_PROPAGATIONS_PER_CALL",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "256",
        unit: "literals offered per call",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "NOT a completeness bound: the fixpoint resumes on the next call. The doc says it sits well above the per-call yield measured on the QF_LRA timeout population, without saying when.",
    },
    ConfigEntry {
        name: "MAX_FM_CONSTRAINTS",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "20_000",
        unit: "constraints from one elimination step",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-1752",
            "2026-09-07",
            None,
            &[sym(
                "crates/axeyum-solver/src/lra_online.rs",
                "MAX_FM_CONSTRAINTS",
            )],
            &[adr("ADR-1752")],
        ),
        note: "A COUNT that said nothing about the bytes behind it — the doc names the 7.8 GB abort on `danoint-266.smt2` it failed to catch. ADR-1752 added a byte gate ALONGSIDE it rather than replacing it, so the Fourier-Motzkin fallback now has two ceilings in two units, deliberately.",
    },
    ConfigEntry {
        name: "MAX_LRA_CACHED_COEFFICIENTS",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "262_144",
        unit: "cached coefficients",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-1752",
            "2026-09-07",
            Some("96ff85930"),
            &[sym(
                "crates/axeyum-solver/src/lra_online.rs",
                "MAX_LRA_CACHED_COEFFICIENTS",
            )],
            &[
                adr("ADR-1752"),
                commit("96ff85930", "Enforce shared arithmetic resource bounds"),
            ],
        ),
        note: "THE CONSTANT AT THE CENTRE OF THIS REGISTRY'S REASON TO EXIST. It bounds the linearization memo — the exact cost `MAX_ONLINE_LRA_ATOMS`'s 2026-08-03 measurement blamed for an 8 GiB abort. It landed 2026-08-06 (`96ff85930`), three days AFTER that measurement, which was never re-taken. Overridden per-budget by `for_budget`.",
    },
    ConfigEntry {
        name: "MAX_LRA_COEFFICIENT_WORK",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "4_000_000",
        unit: "coefficient-work units",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-1752",
            "2026-09-07",
            None,
            &[sym(
                "crates/axeyum-solver/src/lra_online.rs",
                "MAX_LRA_COEFFICIENT_WORK",
            )],
            &[adr("ADR-1752")],
        ),
        note: "Caps quadratic coefficient blow-up during normalization. This is the default; `for_budget` overrides it per budget, so the compiled literal is not the number a run uses.",
    },
    ConfigEntry {
        name: "MAX_LRA_NORMALIZATION_NODES",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "1_000_000",
        unit: "term-graph nodes walked",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Bounds normalization work independently of memory, so a wide-and-shallow query cannot spin inside a budget it fits.",
    },
    ConfigEntry {
        name: "REDUCE_FIRST",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "2_000",
        unit: "learned clauses",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Clause-database reduction schedule base. Duplicated across four CDCL cores in this workspace.",
    },
    ConfigEntry {
        name: "REDUCE_INC",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "300",
        unit: "learned clauses",
        protects: Protects::Memory,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Reduction schedule increment. `axeyum-cnf` spells the same constant `REDUCE_INCREMENT`; same value, different name, no link.",
    },
    ConfigEntry {
        name: "VSIDS_DECAY",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "0.95",
        unit: "activity multiplier per conflict",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The only f64 heuristic registered here. Four independent copies exist in the workspace.",
    },
    ConfigEntry {
        name: "VSIDS_RESCALE",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "1e-100",
        unit: "activity multiplier",
        protects: Protects::Soundness,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Prevents f64 overflow of activity scores on long runs. `Soundness` here means arithmetic soundness of the heuristic, not of the verdict.",
    },
    ConfigEntry {
        name: "VSIDS_RESCALE_LIMIT",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "1e100",
        unit: "activity score",
        protects: Protects::Soundness,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "The trigger for the rescale above.",
    },
    ConfigEntry {
        name: "SIMPLEX_FIRST_AT_CONSTRAINTS",
        module: "crates/axeyum-solver/src/lra_route.rs",
        value: "256",
        unit: "collected linear constraints in one conjunctive system",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::None,
        guarded_by: "neither engine is skipped: crossing the bound only swaps which of the two sound deciders runs FIRST, and whichever declines hands the identical system to the other, so the set of systems the pair decides is unchanged and no verdict can depend on the order",
        env_override: Some("AXEYUM_LRA_ROUTE"),
        justification: dated(
            "docs/research/12-performance/lra-route-and-cube-order-2026-09-08.md",
            "2026-09-08",
            None,
            &[
                sym("crates/axeyum-solver/src/lra.rs", "decide_within"),
                sym("crates/axeyum-solver/src/lra.rs", "simplex_fallback"),
                sym("crates/axeyum-solver/src/lra.rs", "MAX_FM_CONSTRAINTS"),
                sym("crates/axeyum-solver/src/lra_route.rs", "LraRoutePolicy"),
            ],
            &[
                doc("docs/research/12-performance/lra-route-and-cube-order-2026-09-08.md"),
                live(
                    "SIMPLEX_FIRST_AT_CONSTRAINTS",
                    "crates/axeyum-solver/src/lra_route.rs",
                ),
                live("MAX_FM_CONSTRAINTS", "crates/axeyum-solver/src/lra.rs"),
            ],
        ),
        note: "Set at the BOTTOM of the measured range, not lower. Fourier-Motzkin declined on 2,745 of 2,745 cubes across the 22 `QF_LRA` files bound by the offline lazy-SMT loop (265-1,736 constraints each), after consuming 96-99.9% of that loop's theory time reaching `lra.rs::MAX_FM_CONSTRAINTS`; the simplex then decided all 2,745 in 43-696 ms in total. Below 265 there is NO measurement, and the elimination is exact, so on a small system it yields the tightest refutation: dropping this to 0 measurably changed `nra_handelman_cert`'s pinned residual from -31/400 to -31/1580. `usize::MAX` (`AXEYUM_LRA_ROUTE=fm-first` or `legacy`) is the pre-2026-09-08 order.",
    },
    ConfigEntry {
        name: "DEFAULT_ONLINE_LRA_BUDGET_BYTES",
        module: "crates/axeyum-solver/src/lra_theory.rs",
        value: "crate::lra_online::DEFAULT_ONLINE_LRA_BUDGET_BYTES",
        unit: "bytes",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_MEMORY_LIMIT_MB"),
        justification: dated(
            "ADR-1752",
            "2026-09-07",
            None,
            &[sym(
                "crates/axeyum-solver/src/lra_theory.rs",
                "DEFAULT_ONLINE_LRA_BUDGET_BYTES",
            )],
            &[adr("ADR-1752")],
        ),
        note: "A re-export, not a second number. Registered so a reader who greps this file sees where the value actually lives.",
    },
    ConfigEntry {
        name: "MAX_ONLINE_LRA_ATOMS",
        module: "crates/axeyum-solver/src/lra_theory.rs",
        value: "1_024",
        unit: "distinct linear-real atoms",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-1752",
            "2026-09-07",
            Some("e62086742"),
            &[
                // `MAX_LRA_CACHED_COEFFICIENTS` names a CONSTANT on purpose, and
                // it is the only one here that does: it is this ADR's founding
                // example, the dependency whose absence let a 2026-08-03
                // measurement stand for thirteen months after the 2026-08-06
                // commit that falsified it. The other two named constants were
                // replaced — `DEFAULT_ONLINE_LRA_BUDGET_BYTES` tripped this
                // entry STALE on `79a7c5297`, whose only touch of that symbol
                // is a rustdoc link inside a doc comment.
                sym(
                    "crates/axeyum-solver/src/lra_online.rs",
                    "MAX_LRA_CACHED_COEFFICIENTS",
                ),
                // The screen that reproduces this value at the default budget.
                sym(
                    "crates/axeyum-solver/src/lra_theory.rs",
                    "check_qf_lra_online_cdclt",
                ),
                // The OTHER live consumer, and the reason 1,024 still governs
                // anything: `nra` projects its abstraction against this ceiling.
                sym("crates/axeyum-solver/src/nra.rs", "admission_fits_consumer"),
            ],
            &[
                adr("ADR-1752"),
                commit("e62086742", "the online theory decides on"),
            ],
        ),
        note: "THE WORKED EXAMPLE, and now a DIVERGENCE nobody has written down. It is no longer the LRA route's own admission gate — ADR-1752 replaced that with `budget_bytes / BYTES_PER_ADMITTED_ATOM`, which is 1,024 at the DEFAULT budget and 13,107 at `--memory-limit-mb 8192`. But `nra::admission_fits_consumer` still projects against this STATIC 1,024 and calls it that engine's capacity (ADR-1751). So above the default budget the two numbers are incommensurable again: the LRA consumer admits 13,107 atoms while the NRA gate refuses above 1,024. That is the same defect ADR-1751 existed to remove, reintroduced in a new form by ADR-1752, and it is recorded here rather than resolved — it needs a measurement, not an edit.",
    },
    ConfigEntry {
        name: "DEFAULT_REPAIR_CANDIDATE_CAP",
        module: "crates/axeyum-solver/src/mbqi_model_finder.rs",
        value: "256",
        unit: "cartesian repair candidates",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "a repaired model receives SAT credit only once `crate::quant_uf_model_sat_cert` independently checks every original universal (module doc); declining repair here can only miss a model, never certify a wrong one",
        env_override: Some("AXEYUM_DEFAULT_REPAIR_CANDIDATE_CAP"),
        justification: undated("doc comment"),
        note: "Running product of per-function default-value pool sizes, checked incrementally while assembling repairs.",
    },
    ConfigEntry {
        name: "DEFAULT_REPAIR_FUNCTION_CAP",
        module: "crates/axeyum-solver/src/mbqi_model_finder.rs",
        value: "8",
        unit: "functions needing repair",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "a repaired model receives SAT credit only once `crate::quant_uf_model_sat_cert` independently checks every original universal (module doc); declining repair here can only miss a model, never certify a wrong one",
        env_override: Some("AXEYUM_DEFAULT_REPAIR_FUNCTION_CAP"),
        justification: undated("doc comment"),
        note: "Admission gate on how many functions the repair search will attempt to fix at once.",
    },
    ConfigEntry {
        name: "DEFAULT_REPAIR_VALUE_CAP",
        module: "crates/axeyum-solver/src/mbqi_model_finder.rs",
        value: "32",
        unit: "candidate values per function",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "a repaired model receives SAT credit only once `crate::quant_uf_model_sat_cert` independently checks every original universal (module doc); declining repair here can only miss a model, never certify a wrong one",
        env_override: Some("AXEYUM_DEFAULT_REPAIR_VALUE_CAP"),
        justification: undated("doc comment"),
        note: "Per-function candidate-value pool size; exercised directly by the `oversized_value_pool_declines` test.",
    },
    ConfigEntry {
        name: "ENCODING_BYTES_PER_CLAUSE",
        module: "crates/axeyum-solver/src/memory_budget.rs",
        value: "384",
        unit: "bytes per bit-blasted CNF clause",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_MEMORY_LIMIT_MB"),
        justification: dated(
            "doc comment",
            "2026-08-21",
            None,
            &[sym(
                "crates/axeyum-solver/src/memory_budget.rs",
                "ENCODING_BYTES_PER_CLAUSE",
            )],
            // What makes this the best-justified entry is not the doc table but
            // the SHIPPED RE-MEASUREMENT TEST: the number can be re-taken rather
            // than re-argued. If that test is deleted the justification loses
            // exactly the property this note credits it with, so the test is the
            // basis, alongside the conversion site the byte budget flows into.
            &[
                live(
                    "clause_ceiling",
                    "crates/axeyum-solver/src/memory_budget.rs",
                ),
                live(
                    "a_budget_smaller_than_the_encoding_declines_as_a_memory_limit",
                    "crates/axeyum-solver/tests/memory_budget.rs",
                ),
            ],
        ),
        note: "THE BEST-JUSTIFIED ENTRY IN THIS REGISTRY, and the model for the rest: the doc carries a table of measured peaks over `bvmul` commutativity miters, names the host, gives the date, AND ships a re-measurement test (`crates/axeyum-solver/tests/memory_budget.rs`) so the number can be re-taken rather than re-argued. Converts a byte budget into `clause_ceiling()`.",
    },
    ConfigEntry {
        name: "WATCHDOG_IDLE_INTERVAL",
        module: "crates/axeyum-solver/src/memory_budget.rs",
        value: "Duration::from_millis(500)",
        unit: "milliseconds between wake-ups while NO budget is installed",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-09-08",
            Some("5d406a12b"),
            &[sym(
                "crates/axeyum-solver/src/memory_budget.rs",
                "WATCHDOG_IDLE_INTERVAL",
            )],
            &[live(
                "watchdog_loop",
                "crates/axeyum-solver/src/memory_budget.rs",
            )],
        ),
        note: "NOT an admission bound, which is why it carries the `SearchEvent`/`NotApplicable` class: it is the backstop period on a condvar wait, and crossing it means the sampler woke up, found no budget installed, and went back to sleep. It cannot delay the arming of a budget -- every install notifies the condvar -- so it only bounds how long a MISSED notification could go unnoticed, and even then no verdict changes, because the projection gates (`fm_admission`, `simplex_admission`, `clause_ceiling`) do not consult the sampler at all. The cost is two wake-ups a second in a process that has installed a budget at least once; a process that never sets `memory_limit_mb` never spawns the thread.",
    },
    ConfigEntry {
        name: "WATCHDOG_SAMPLE_INTERVAL",
        module: "crates/axeyum-solver/src/memory_budget.rs",
        value: "Duration::from_millis(20)",
        unit: "milliseconds between resident-set samples while a budget is installed",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_MEMORY_LIMIT_MB"),
        justification: dated(
            "docs/research/12-performance/span-log-sweep-2026-09-08.md",
            "2026-09-08",
            Some("5d406a12b"),
            &[sym(
                "crates/axeyum-solver/src/memory_budget.rs",
                "WATCHDOG_SAMPLE_INTERVAL",
            )],
            &[
                live("watchdog_tripped", "crates/axeyum-solver/src/lra.rs"),
                live(
                    "the_watchdog_samples_and_trips_on_an_over_limit_reading",
                    "crates/axeyum-solver/src/memory_budget.rs",
                ),
                doc("docs/research/12-performance/span-log-sweep-2026-09-08.md"),
            ],
        ),
        note: "Sets how far past `memory_limit_mb` a route can get before anything notices: at 20 ms a route allocating 1 GiB/s is at most ~20 MiB over when the flag is set. Derived from the module's own measured 9.4 us `/proc/self/status` read -- 0.047 % of one core -- which is also the reason this is a THREAD and not another inline probe: the inline probes cost 32 us per check and therefore could never go in a loop, which is exactly why the field did not bind on the route that reached 26.6 GB. The two `Basis` entries are the deepest consumer of the flag and the test that pins BOTH directions of the trip; a sampler that trips unconditionally is as useless as one that never does.",
    },
    ConfigEntry {
        name: "PROOF_LITERAL_BUDGET",
        module: "crates/axeyum-solver/src/native_cdclt.rs",
        value: "8_000_000",
        unit: "DRAT literals",
        protects: Protects::Memory,
        on_exceed: OnExceed::Truncate,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Doc: 'It bounds the RECORDING only: the search is unaffected either way, so no verdict depends on it' — crossing abandons DRAT-proof recording (the refutation verdict still returns, just without an artifact), matching `Truncate` (a result computed with less recording effort) rather than `RefuseUnknown`. The absent-artifact outcome is observable by the evidence layer, the only consumer, hence `ToCaller`.",
    },
    ConfigEntry {
        name: "MAX_CONGRUENCE_GROUPS",
        module: "crates/axeyum-solver/src/nia_linearize.rs",
        value: "48",
        unit: "variable-divisor div/mod groups",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "`check_with_nia` accepts a `sat` only after `replay_sat` re-evaluates the ORIGINAL assertions under the ground evaluator, which a model violating div/mod functionality cannot pass",
        env_override: None,
        justification: undated("doc comment"),
        note: "THE UNSIGNALLED TWIN, and the entry this registry's `Signal` field exists for. `if infos.len() <= MAX_CONGRUENCE_GROUPS { .. }` has NO `else`: above the cap the Ackermann congruence lemmas are simply never emitted, with no `unknown`, no counter and no trace entry. Its namesake in `axeyum-rewrite` — same name, same value 48 — reports the identical crossing as `ZeroDivisorCongruence::Omitted` and is branched on (ADR-1730). The direction is a RELAXATION, so `unsat` still transfers and only `sat` is at risk; here that risk is closed by model replay rather than by a signal, which is why this is a completeness cost and not a soundness hole. Recorded, not changed.",
    },
    ConfigEntry {
        name: "MAX_MCCORMICK_PRODUCTS",
        module: "crates/axeyum-solver/src/nia_linearize.rs",
        value: "8192",
        unit: "abstracted products",
        protects: Protects::Time,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "the envelope pass only adds valid lemmas, so skipping it cannot change a verdict",
        env_override: None,
        justification: undated("doc comment"),
        note: "Above it the McCormick envelope pass is skipped wholesale.",
    },
    ConfigEntry {
        name: "MAX_REFINED_PER_ROUND",
        module: "crates/axeyum-solver/src/nia_linearize.rs",
        value: "64",
        unit: "products refined per round",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "remaining products wait for a later round",
        env_override: None,
        justification: undated("doc comment"),
        note: "Stops thousands of products adding thousands of lemmas in one round.",
    },
    ConfigEntry {
        name: "MAX_REFINEMENT_ROUNDS",
        module: "crates/axeyum-solver/src/nia_linearize.rs",
        value: "64",
        unit: "tangent-plane refinement rounds",
        protects: Protects::Termination,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the wall-clock slice is the real bound; this is a backstop",
        env_override: None,
        justification: undated("doc comment"),
        note: "Backstop against a pathological spin.",
    },
    ConfigEntry {
        name: "MAX_SMALL_DOMAIN_PRODUCTS",
        module: "crates/axeyum-solver/src/nia_linearize.rs",
        value: "1024",
        unit: "products given an exact case split",
        protects: Protects::Time,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "products beyond it keep sign lemmas and envelopes, which are still valid",
        env_override: None,
        justification: undated("doc comment"),
        note: "Bounds total case-split expansion.",
    },
    ConfigEntry {
        name: "MAX_SMALL_DOMAIN_WIDTH",
        module: "crates/axeyum-solver/src/nia_linearize.rs",
        value: "4",
        unit: "integer interval width",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "as above: the weaker lemmas remain valid",
        env_override: None,
        justification: undated("doc comment"),
        note: "Decides when the exact case-split linearization applies.",
    },
    ConfigEntry {
        name: "MAX_TANGENT_ABS_VALUE",
        module: "crates/axeyum-solver/src/nia_linearize.rs",
        value: "1 << 40",
        unit: "absolute factor magnitude",
        protects: Protects::Soundness,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "the lemma is not emitted, and an unemitted valid lemma cannot be wrong",
        env_override: None,
        justification: undated("doc comment"),
        note: "Keeps `a_val * b_val` exact in `i128` for tangent-plane coefficients.",
    },
    ConfigEntry {
        name: "MCCORMICK_MAX_ABS_BOUND",
        module: "crates/axeyum-solver/src/nia_linearize.rs",
        value: "1 << 20",
        unit: "absolute endpoint magnitude",
        protects: Protects::Soundness,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "the envelope row is skipped; an unemitted lemma cannot be wrong",
        env_override: None,
        justification: undated("doc comment"),
        note: "Keeps the envelope's constant term inside `i128`.",
    },
    ConfigEntry {
        name: "NIA_MCCORMICK_BUDGET_SHARE",
        module: "crates/axeyum-solver/src/nia_linearize.rs",
        value: "3",
        unit: "divisor of the remaining budget",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: Some("AXEYUM_NIA_REFINEMENT"),
        justification: dated(
            "docs/research/12-performance/nia-refinement-round-2026-09-08.md",
            "2026-09-08",
            Some("5d406a12b"),
            &[sym(
                "crates/axeyum-solver/src/nia_linearize.rs",
                "NIA_MCCORMICK_BUDGET_SHARE",
            )],
            &[
                doc("docs/research/12-performance/nia-refinement-round-2026-09-08.md"),
                live(
                    "the_off_arm_reproduces_the_committed_slice_and_round_budget",
                    "crates/axeyum-solver/src/nia_linearize.rs",
                ),
            ],
        ),
        note: "MEASURED, AND THE MEASUREMENT DID NOT MOVE IT. First 50 files of the committed `QF_NIA` parity list, 24 s budget, one process per host on idle s6/s7. At 3 the loop gets a median 6.65 s slice, runs 1-15 rounds (median 1, 26 of 50 files exactly one) and emits 2,476 tangent lemmas. The `AXEYUM_NIA_REFINEMENT=1/1` arm hands it the whole remaining budget (median 19.96 s): 22 files get more rounds, 1,280 more tangent lemmas are emitted, and TWO files move `unknown` -> `sat` -- neither reproducibly (file 13 sat in 3 of 4 repeats, file 30 in 1 of 7). The inner search consumes whatever budget it is given rather than converging, exactly as `OVERSIZED_ADMISSION_PROBE_BUDGET`'s justification already records, so a larger slice moves which states are visited and not how deep the search goes. Left at 3; the lever ships OFF so the next A/B needs no rebuild.",
    },
    ConfigEntry {
        name: "NIA_SLICE_MS",
        module: "crates/axeyum-solver/src/nia_linearize.rs",
        value: "600",
        unit: "milliseconds",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: Some("AXEYUM_NIA_REFINEMENT"),
        justification: dated(
            "docs/research/12-performance/nia-refinement-round-2026-09-08.md",
            "2026-09-08",
            Some("5d406a12b"),
            &[sym(
                "crates/axeyum-solver/src/nia_linearize.rs",
                "NIA_SLICE_MS",
            )],
            &[
                doc("docs/research/12-performance/nia-refinement-round-2026-09-08.md"),
                live(
                    "the_off_arm_reproduces_the_committed_slice_and_round_budget",
                    "crates/axeyum-solver/src/nia_linearize.rs",
                ),
            ],
        ),
        note: "Default slice for the pre-ladder NIA relaxation so it cannot hang before the width ladder is reached. THE ARM THAT SELECTS IT IS NARROW: measured 2026-09-08 over the first 50 files of the committed `QF_NIA` parity list, only 3 of 50 top-level calls take this floor at all -- the other 47 have `McCormick` envelopes or exact splits and take `NIA_MCCORMICK_BUDGET_SHARE` instead. It bounds a hang, not a search, and `NiaRefinementPolicy` deliberately does not move it: raising the hang guard is a different decision from raising the search budget.",
    },
    ConfigEntry {
        name: "POW2_TABLE_MAX_CASES",
        module: "crates/axeyum-solver/src/nia_linearize.rs",
        value: "128",
        unit: "disjunct cases in one value table",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "the value table is a theorem the relaxation could have had; omitting it enlarges the model set, and every `sat` from the relaxed query is replayed against the ORIGINAL assertions by `check_with_nia`",
        env_override: None,
        justification: undated("doc comment"),
        note: "Caps a generated `x = k` value table.",
    },
    ConfigEntry {
        name: "POW2_TABLE_MAX_EXP",
        module: "crates/axeyum-solver/src/nia_linearize.rs",
        value: "62",
        unit: "exponent",
        protects: Protects::Soundness,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "as POW2_TABLE_MAX_CASES: an omitted value table only enlarges the model set, and `check_with_nia` replays every `sat`",
        env_override: None,
        justification: undated("doc comment"),
        note: "`pow2_value` returns `None` past it so `1 << k` stays inside `i128`.",
    },
    ConfigEntry {
        name: "ISQRT_HI",
        module: "crates/axeyum-solver/src/nia_square.rs",
        value: "1i128 << 51",
        unit: "binary-search ceiling for isqrt",
        protects: Protects::Soundness,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "FINDING (unenforced coupling). Binary-search ceiling for `isqrt`, derived from and coupled to `MAX_ABS_COEFF` (doc: 'The caller guards the coefficients below 2^40... giving floor(sqrt(D)) < 2^42 <= 2^51 = HI'). The coupling is asserted only in the doc comment, not checked at runtime or expressed as a `rests_on` dependency anywhere — if `MAX_ABS_COEFF` were ever raised without re-deriving this bound, `isqrt`'s search window could stop covering every admitted discriminant. Same unenforced-by-code pattern as `nra_real_root::ISOLATE_GRID` below.",
    },
    ConfigEntry {
        name: "MAX_ABS_COEFF",
        module: "crates/axeyum-solver/src/nia_square.rs",
        value: "1i128 << 40",
        unit: "coefficient magnitude",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Coefficient magnitude guard against i128 overflow in `b^2`, `4*a*c`, `isqrt`, and divisor enumeration (doc). Doc: 'Larger coefficients are left to the existing NIA dispatch (sound)' — an explicit `DeclineRoute`. `nra_real_root.rs::MAX_ABS_COEFF`'s doc explicitly says it 'mirrors `nia_square::MAX_ABS_COEFF`'; same value, two independent `const` definitions, no code-level link (no shared symbol, no import).",
    },
    ConfigEntry {
        name: "MAX_DEGREE",
        module: "crates/axeyum-solver/src/nia_square.rs",
        value: "64",
        unit: "polynomial degree",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "'decline (sound): an absurd degree... would otherwise let collection and Horner evaluation do unbounded work' (doc). `nra_real_root.rs::MAX_DEGREE` is a second independent `= 64` definition with near-identical doc wording ('Maximum polynomial degree the pass collects / decides; beyond it we decline') but no explicit cross-reference between the two files, unlike the `MAX_ABS_COEFF` pair above.",
    },
    ConfigEntry {
        name: "NE_SCAN",
        module: "crates/axeyum-solver/src/nia_square.rs",
        value: "(MAX_DEGREE as i128) + 8",
        unit: "integer steps outward from 0",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Bounded scan for a degree->=3 `!=` non-root witness; doc: 'cap it and decline on a miss (only reachable via overflow) - soundness first.' `decide_high_degree`'s `Cmp::Ne` arm returns `None` after exhausting the scan (nia_square.rs:505-513). Value is derived from `MAX_DEGREE` in the same file, so the two are linked in code (not an unenforced doc-only coupling like `ISQRT_HI`).",
    },
    ConfigEntry {
        name: "TAIL_SCAN",
        module: "crates/axeyum-solver/src/nia_square.rs",
        value: "64",
        unit: "integer steps outward from the vertex",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Outward witness scan for the quadratic 'always Sat' tail cases; doc: 'cap the scan and decline if no witness replays - soundness over reach.' `find_witness` returns `None` after exhausting the scan (nia_square.rs:645-653), reachable in practice only via overflow per its own doc.",
    },
    ConfigEntry {
        name: "LEGACY_ADMISSION_CROSS_PRODUCTS",
        module: "crates/axeyum-solver/src/nra.rs",
        value: "2",
        unit: "distinct-operand cross-products",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_NRA_ADMISSION"),
        justification: dated(
            "ADR-1751",
            "2026-09-07",
            Some("9a8b09220"),
            &[
                sym(
                    "crates/axeyum-solver/src/nra.rs",
                    "LEGACY_ADMISSION_CROSS_PRODUCTS",
                ),
                sym(
                    "crates/axeyum-solver/src/lra_theory.rs",
                    "MAX_ONLINE_LRA_ATOMS",
                ),
            ],
            &[
                adr("ADR-1751"),
                commit("9a8b09220", "deterministic cross-product admission bound —"),
            ],
        ),
        note: "THE UNIT-MISMATCH ENTRY, now retired from its gate role. It metered CROSS-PRODUCTS while the consuming engine meters ATOMS and refuses above 1,024 — two gates on one resource, 15x apart, in units with no constant conversion (the measured atoms-per-cross-product ratio spans 13.1 to 30.3 across four census files, so any single factor is wrong by up to 2.3x). ADR-1751 replaced it with `admission_fits_consumer`, which counts the consumer's own unit. The constant survives ONLY as the non-regression marker and as the `AXEYUM_NRA_ADMISSION=legacy` A/B lever. Lifting it cost +502 s over 62 files and bought 2 new `sat`; on 25 of those 62 it protects nothing at all.",
    },
    ConfigEntry {
        name: "MAX_BNB_DEPTH",
        module: "crates/axeyum-solver/src/nra.rs",
        value: "6",
        unit: "branch-and-bound depth",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Each level halves one variable's interval. Detail reads `branch-and-bound depth budget reached`.",
    },
    ConfigEntry {
        name: "MAX_REFINE_ROUNDS",
        module: "crates/axeyum-solver/src/nra.rs",
        value: "12",
        unit: "incremental-linearization rounds",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Distinguishes a round-bound `ResourceLimit` (retryable) from a fixpoint-without-deciding `Incomplete` — one of the few bounds here whose `unknown` says which kind of giving-up it was.",
    },
    ConfigEntry {
        name: "MCCORMICK_ATOMS_PER_TRIPLE",
        module: "crates/axeyum-solver/src/nra.rs",
        value: "4",
        unit: "atoms per abstracted triple",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-1751",
            "2026-09-07",
            None,
            &[
                sym(
                    "crates/axeyum-solver/src/nra.rs",
                    "MCCORMICK_ATOMS_PER_TRIPLE",
                ),
                sym(
                    "crates/axeyum-solver/src/lra_theory.rs",
                    "MAX_ONLINE_LRA_ATOMS",
                ),
            ],
            &[adr("ADR-1751")],
        ),
        note: "Headroom reserved in the admission projection for envelope atoms added per branch-and-bound node, which a pre-solve atom count cannot see. Four inequalities per product, so admission does not hand the consumer a system that only fits before the search starts.",
    },
    ConfigEntry {
        name: "RELAXATION_DEADLINE_SHARE_ABOVE_LEGACY",
        module: "crates/axeyum-solver/src/nra.rs",
        value: "2",
        unit: "divisor of the remaining deadline",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "ADR-1751",
            "2026-09-07",
            None,
            &[sym(
                "crates/axeyum-solver/src/nra.rs",
                "RELAXATION_DEADLINE_SHARE_ABOVE_LEGACY",
            )],
            &[adr("ADR-1751")],
        ),
        note: "SET FROM THE MEASUREMENT, NOT CHOSEN: the two new `sat` results were found 4.4 s and 1.0 s into the relaxation, so half of a 24 s budget leaves the larger 2.5x headroom while capping worst-case starvation of the `int_real_relax` and `dispatch_uf_nra` callers at half.",
    },
    ConfigEntry {
        name: "SIGN_REFUTE_BUDGET",
        module: "crates/axeyum-solver/src/nra.rs",
        value: "Duration::from_millis(500)",
        unit: "milliseconds",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Bounds the cheap sign/zero and threshold-1 pre-refutation passes so a capped instance declines promptly even with no global timeout. Only `Unsat` is acted on, so a timeout here can never produce a wrong verdict.",
    },
    ConfigEntry {
        name: "FBBT_DEFAULT",
        module: "crates/axeyum-solver/src/nra_fbbt.rs",
        value: "FbbtPolicy::DERIVED_BOUNDS",
        unit: "policy arm for the derived-bound refutation route",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the route can produce exactly ONE verdict and it is `unsat`. Its success type `nra_fbbt::Refutation` carries three `usize` counters and no model, has no `Sat` or `Unknown` variant to construct, and `Refutation::into_check_result` has a constant body -- so a decider's `ComponentOutcome::Sat` bindings have nowhere to go and reporting `sat` would take a new variant plus a new branch, not a forgotten `return`. Everything the route hands a decider is entailed by the query: the component's nonlinear atoms and the in-scope linear atoms are a SUBSET of it, and every derived bound carries a Farkas certificate that `nra_fbbt::verify` re-checks (`target - sum(lambda_j * p_j)` must be a nonnegative constant with every `lambda_j > 0`) against a pool whose every entry was itself checked before being appended. The seven guards in that checker are mutation-controlled as the `nra-fbbt-checker` suite (each deletion killed only its own tests, 7 of 7); the route's own adversarial test dies with `got Unsat` on a query satisfied by `x = 8, y = 5, z = 0` when the residual guard is deleted and the derivation made 20x too tight",
        env_override: Some("AXEYUM_NRA_FBBT"),
        justification: dated(
            "docs/research/12-performance/nra-fbbt-derived-bounds-2026-09-09.md",
            "2026-09-09",
            None,
            // The measurement is "37 of the 75 QF_NRA parity losses have every
            // nonlinear atom in one or two variables while declaring more, and
            // `decide_component` dispatches on the CONNECTED COMPONENT's variable
            // count while `connected_components` unions over the linear atoms
            // too". It rests on that dispatch still being by component variable
            // count, on the components still being built over every atom, and on
            // `extract_bounds` still being syntactic (which is why a transitive
            // bound is not already available). Change any of the three and the
            // numbers stop describing this tree.
            &[
                sym(
                    "crates/axeyum-solver/src/nra_real_root.rs",
                    "decide_component",
                ),
                sym(
                    "crates/axeyum-solver/src/nra_real_root.rs",
                    "connected_components",
                ),
                sym("crates/axeyum-solver/src/nra.rs", "extract_bounds"),
            ],
            // The basis names the checker the whole soundness argument runs
            // through and the decider the route re-offers its component to. If
            // `verify` leaves `nra_fbbt.rs` the derived bounds are unchecked and
            // this is an unguarded `unsat` producer; if `decide_component` leaves
            // `nra_real_root.rs` there is no cheap decider to re-offer to and the
            // measured gain describes nothing.
            &[
                live("verify", "crates/axeyum-solver/src/nra_fbbt.rs"),
                live(
                    "decide_component",
                    "crates/axeyum-solver/src/nra_real_root.rs",
                ),
                doc("docs/research/12-performance/nra-fbbt-derived-bounds-2026-09-09.md"),
                doc("docs/research/12-performance/qf-nra-loss-attribution-2026-09-09.md"),
            ],
        ),
        note: "Whether the derived-bound refutation route runs. `nra_real_root::decide_component` dispatches on the CONNECTED COMPONENT's variable count and `connected_components` unions over every atom, the linear ones included -- so a query whose nonlinear content sits inside the 1-variable sign-cell decider or the 2-variable resultant/CAD decider is handed to the >=3-variable CAD, which declines. Measured 2026-09-09 on the 75-file QF_NRA loss list: 37 of 75 have every nonlinear atom in one or two variables and ALL of them declare more, the extras occurring only in linear atoms. This route derives constant bounds on the nonlinear component's variables from those linear atoms (feasibility-based bound tightening -- TRANSITIVE, which `nra::extract_bounds` explicitly is not: its own doc says 'only syntactic operand-vs-constant bounds are recognised') and re-offers the component plus its bounds to the cheap deciders. DEFAULT is ON, from the A/B: on the 75-file list, one binary, arms differing only in this env override, `derived-bounds` decides 2 files `off` does not (`sqrt-1mcosq-8-chunk-0014`, `sqrt-1mcosq-8-chunk-0485`, both declared `:status unsat`, both in 0.1 s), with ZERO verdict regressions and total wall clock 819 s vs 822 s. The gain is 2, not 37: the other 35 are consulted and the derived bounds do not close them, which is a capability statement about the deciders, not about admission. `max_component_vars = 2` keeps the route on the cheap deciders -- 3 is the N-variable CAD that already declined. NOT a fix for the 14-file atom-capacity class, which is 11-36x past `lra_theory::MAX_ONLINE_LRA_ATOMS` and which no bound derivation reaches.",
    },
    ConfigEntry {
        name: "MAX_GENERATORS",
        module: "crates/axeyum-solver/src/nra_handelman_cert.rs",
        value: "48",
        unit: "generators",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`check_handelman_refutation` independently re-derives every accepted certificate from the original assertions (module doc: \"the checker never runs an LP\"); declining the search here can only forgo finding a Handelman/Positivstellensatz certificate, never accept a wrong one.",
        env_override: Some("AXEYUM_HANDELMAN_MAX_GENERATORS"),
        justification: undated("doc comment"),
        note: "`generators()` returns `None` past this bound; `produce_handelman_evidence` (evidence.rs) then falls through to other `QF_NRA` routes, per its own doc: \"Declines (None) ... for any nonlinear query whose combination the bounded search does not find.\"",
    },
    ConfigEntry {
        name: "MAX_MONOMIALS",
        module: "crates/axeyum-solver/src/nra_handelman_cert.rs",
        value: "16",
        unit: "monomials",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "same as `MAX_GENERATORS` in this file: `check_handelman_refutation` re-derives before accepting.",
        env_override: Some("AXEYUM_HANDELMAN_MAX_MONOMIALS"),
        justification: undated("doc comment"),
        note: "\"Fourier-Motzkin is doubly exponential in the variable count, so this is a budget, not a semantic limit\" — doc comment. Same name, different module and value (4096), as `cas_certificate.rs::MAX_MONOMIALS` — unrelated engines, not a divergent twin.",
    },
    ConfigEntry {
        name: "RELAXATION_DENOMINATOR_THRESHOLD",
        module: "crates/axeyum-solver/src/nra_handelman_cert.rs",
        value: "1_000_000_000_000",
        unit: "denominator magnitude",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "`check_case`/`check_handelman_refutation` re-derive and bounds-check the relaxed hypothesis from the original assertions before any certificate is accepted (module doc: \"the checker re-derives the weakened hypothesis rather than trusting it\"), so this threshold can only change whether a certificate is FOUND, never whether an accepted one is sound.",
        env_override: None,
        justification: undated("doc comment"),
        note: "Unusual direction: an atom's constant-term denominator ABOVE this threshold is what makes it a relaxation candidate (module doc's `RELAXATION_GRIDS` rounding), i.e. crossing it ENLARGES what the LP search can certify (e.g. the module doc's `2.0000000000000000000000000001` example) rather than declining a route.",
    },
    ConfigEntry {
        name: "COARSEN_MAX_EXP",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "40",
        unit: "dyadic denominator exponent (2^k)",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "'Beyond it we keep the original (and let field arithmetic decline if it must)' (doc) — the function itself returns `None` after exhausting the loop (nra_real_root.rs:5264-5282, `for _ in 0..=COARSEN_MAX_EXP`); a caller not shown at this site is what 'keeps the original' interval on that `None`.",
    },
    ConfigEntry {
        name: "COARSEN_SAMPLE_DEPTH",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "52",
        unit: "denominator doublings",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`coarsest_rational_in` returns `None` ('or if no dyadic is found within the bound', doc) after exhausting the doubling-denominator search (nra_real_root.rs:948-956); doc says the caller 'falls back to the exact midpoint' on that `None`.",
    },
    ConfigEntry {
        name: "ISOLATE_GRID",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "1 << 14",
        unit: "grid cells over the Cauchy interval",
        protects: Protects::Soundness,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "FINDING (unenforced coupling). No runtime check ties this grid density to `MAX_ABS_COEFF`/`MAX_DEGREE`, though the doc's separation argument ('comfortably separates the roots of any small-degree, i128-coefficient polynomial this pass admits') depends on both. Registered `SearchEvent`/`NotApplicable` because the loop (nra_real_root.rs:1461) always runs its full fixed range with no decline branch of its own — but the coupling is the same doc-only, not-code-enforced pattern as `nia_square::ISQRT_HI`, worth a reader's attention.",
    },
    ConfigEntry {
        name: "ISOLATE_REFINE_DEPTH",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "48",
        unit: "bisection steps",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the doc argues explicitly: 'a coarser-but-valid bracket still isolates exactly one root, and the replay check (sign_at(poly, alpha) = 0) does not depend on bracket width' — hitting the depth just stops refining and falls through to algebraic-number construction in the SAME function, which the doc calls sound",
        env_override: None,
        justification: undated("doc comment"),
        note: "Bisection-depth cap (nra_real_root.rs:1501, `for _ in 0..ISOLATE_REFINE_DEPTH`); doc explicitly documents the regression this guards against: 'Before this guard, the ? on an overflowed midpoint eval lost every degree->=3 root to a spurious decline.'",
    },
    ConfigEntry {
        name: "MAX_ABS_COEFF",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "1i128 << 40",
        unit: "coefficient magnitude",
        protects: Protects::Soundness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Doc: 'mirrors `nia_square::MAX_ABS_COEFF`' — same value, independent `const` definition; see that entry's note. No import or shared constant ties them.",
    },
    ConfigEntry {
        name: "MAX_CAD_CELLS",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "256",
        unit: "critical x-values / open x-cells",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "'Hard ceiling on the number of critical x-values... beyond it we decline (bounded - no OOM / hang)' (doc); checked at 5 sites, including a global per-recursion counter (`remaining: Cell::new(MAX_CAD_CELLS)`, nra_real_root.rs:3629) as well as local per-call checks (:3013, :3450, :4751, :4777).",
    },
    ConfigEntry {
        name: "MAX_COPRIME_SPLIT_ITERS",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "64",
        unit: "coprime-split fixpoint iterations",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "doc: 'Returning the current set is sound: every completed split preserves the zero-set arrangement, while an unfinished split can only make a later resultant decline on a shared factor' — exhausting the loop just returns the partially-split set, never a wrong one",
        env_override: None,
        justification: undated("doc comment"),
        note: "Fixpoint-iteration cap (nra_real_root.rs:4175); doc frames it as defense-in-depth ('this only defends against a surprise loop') since each successful split strictly lowers a polynomial's degree or removes one.",
    },
    ConfigEntry {
        name: "MAX_DEGREE",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "64",
        unit: "polynomial degree",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "'beyond it we decline' (doc); near-duplicate wording and identical value to `nia_square::MAX_DEGREE`, independently defined, no cross-reference in either doc comment.",
    },
    ConfigEntry {
        name: "MAX_GRID",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "64",
        unit: "candidate root pairs (|roots(Res_y)| x |roots(Res_x)|)",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "'Hard ceiling on the candidate grid size |roots(Res_y)| x |roots(Res_x)|... beyond it we decline' (doc); checked at nra_real_root.rs:5143.",
    },
    ConfigEntry {
        name: "MAX_MULTI_SYLVESTER_DIM",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "6",
        unit: "resultant dimension",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Doc: 'O(dim! * dim) ring multiplications, so the dimension must stay small. Beyond it we decline (bounded - no OOM / hang)'; checked at nra_real_root.rs:3979. Sibling of `MAX_SYLVESTER_DIM` (same file) for the multi-variable elimination path.",
    },
    ConfigEntry {
        name: "MAX_SUBST_ITERS",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "256",
        unit: "substitution fixpoint iterations",
        protects: Protects::Termination,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "doc: 'the substitution fixpoint is bounded by the number of distinct variables; this is a hard ceiling guarding against any non-termination' — a real run reaching the cap without converging signals a bug elsewhere, not a query property, and the loop simply stops accumulating substitutions rather than failing",
        env_override: None,
        justification: undated("doc comment"),
        note: "Two independent for-loops share this cap (nra_real_root.rs:2369, 6202), both defense-in-depth against the substitution fixpoint failing to converge.",
    },
    ConfigEntry {
        name: "MAX_SYLVESTER_DIM",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "24",
        unit: "resultant dimension",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Doc at the raise-from-6-to-24 commentary (nra_real_root.rs:2658-2660): 'stays a bounded-cost guard... raised from 6 to 24 so higher-degree coupled systems decide instead of declining, while a genuinely huge input still declines fast.' Checked at nra_real_root.rs:5581 (`if m + n > MAX_SYLVESTER_DIM { return None; }`).",
    },
    ConfigEntry {
        name: "RATIONALIZE_MAX_DIVISORS",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "256",
        unit: "divisors enumerated per endpoint",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Doc: 'A composite constant/leading coefficient with more divisors declines the rationality check (keeping the value as an algebraic - still sound, just not collapsed)' (nra_real_root.rs:5375).",
    },
    ConfigEntry {
        name: "RATIONAL_ROOT_BOUND",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "1 << 24",
        unit: "|a0| / |an| magnitude",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "'nothing to enumerate / too large - leave as algebraic' (nra_real_root.rs:1565); a secondary bound alongside MAX_ABS_COEFF that keeps trial-division divisor enumeration cheap.",
    },
    ConfigEntry {
        name: "SOS_MAX_SQUARE_WEIGHT",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "16",
        unit: "integer square weight",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_SOS_MAX_SQUARE_WEIGHT"),
        justification: undated("doc comment"),
        note: "Doc: 'A rational (non-integer) weight needs denominator-clearing - a later slice - so it declines... bounded to keep the (linear-in-d) proof size small' (nra_real_root.rs:6649-6652, `return None`). Declining here forgoes this particular SOS certificate construction, not the underlying verdict.",
    },
    ConfigEntry {
        name: "STURM_SUBDIVIDE_DEPTH",
        module: "crates/axeyum-solver/src/nra_real_root.rs",
        value: "60",
        unit: "bisection subdivision depth",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "'Hitting the bound => decline (fall back to the grid), never an incomplete result' (doc). Two sites both `return None` on `depth >= STURM_SUBDIVIDE_DEPTH` (nra_real_root.rs:1223, 1271); a higher-level caller not shown at either site is what falls back to the grid method.",
    },
    ConfigEntry {
        name: "MAX_PARETO_POINTS",
        module: "crates/axeyum-solver/src/optimize.rs",
        value: "256",
        unit: "Pareto front points",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Doc: 'Exceeding either yields a truncated / Unknown result rather than unbounded work.' Checked at two identical sites (optimize.rs:529, 903, `if front.len() >= MAX_PARETO_POINTS`), both producing `ParetoOutcome::Truncated`.",
    },
    ConfigEntry {
        name: "MAX_PARETO_PUSH",
        module: "crates/axeyum-solver/src/optimize.rs",
        value: "64",
        unit: "guided-improvement steps per point",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Companion to MAX_PARETO_POINTS: caps guided-improvement steps spent certifying one point as maximal (optimize.rs:551, 923, `for _ in 0..MAX_PARETO_PUSH`); also feeds `ParetoOutcome::Truncated`.",
    },
    ConfigEntry {
        name: "ARM_STACK_BYTES",
        module: "crates/axeyum-solver/src/portfolio.rs",
        value: "256 * 1024 * 1024",
        unit: "bytes of stack reserved per portfolio arm thread",
        protects: Protects::Termination,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "crossing it aborts the process rather than declining, so the guard cannot be a signal and has to be a test: `portfolio::tests::an_arm_gets_a_deep_stack_not_the_platform_default` runs an arm that consumes 6 MiB of stack and requires it to return a verdict. Setting this constant back to the platform default (2 MiB) kills that test and nothing else, which is the mutation that was actually run",
        env_override: None,
        justification: dated(
            "docs/research/12-performance/fused-portfolio-int-linear-2026-09-09.md",
            "2026-09-09",
            None,
            &[sym(
                "crates/axeyum-bench/examples/smtcomp_cli.rs",
                "WORKER_STACK_BYTES",
            )],
            &[doc(
                "docs/research/12-performance/fused-portfolio-int-linear-2026-09-09.md",
            )],
        ),
        note: "Crossing it is a stack-overflow ABORT, not a decline -- which is why `on_exceed` is the least honest field here and the note has to carry it. Measured 2026-09-09: with `std::thread::scope`'s platform default (2 MiB) the first raced run of `QF_IDL/queens_bench/super_queen/super_queen61-1.smt2` (19,501 DAG nodes) exited 134 with `fatal runtime error: stack overflow`, where the sequential ladder returned `unknown`. `smtcomp_cli::WORKER_STACK_BYTES` is 512 MiB for the same reason on the main solve; this is half of that because a group reserves it PER ARM and a competition run is commonly under an address-space ulimit. Reservation, not residency: two arms at 256 MiB is the same address space as the one 512 MiB worker the harness already creates.",
    },
    ConfigEntry {
        name: "MAX_PREPROCESS_ROUNDS",
        module: "crates/axeyum-solver/src/preprocess.rs",
        value: "8",
        unit: "preprocessing rounds",
        protects: Protects::Termination,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "`check_with_preprocessing` replays the reconstructed model against the ORIGINAL assertions after the backend solves (module doc), so a cap here can only leave more reduction work for the backend to do itself, never produce a wrong verdict.",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"the loop stops early at a fixpoint (a round that eliminates nothing). A small deterministic cap bounds the cost — fixpoints on real corpora converge in 2-3 rounds; this only guards a pathological oscillation.\" — doc comment.",
    },
    ConfigEntry {
        name: "FLOOD_EAGER_GENERATION_MAX",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "1",
        unit: "instantiation generation",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "an instance whose generation exceeds this waits for the deferred-pool admission budget rather than being dropped; it is re-materialized and re-classified every later round until admitted or the query decides (doc comment)",
        env_override: None,
        justification: dated(
            "docs/research/03-measurements/what-the-admission-filter-rejects-2026-09-10.md",
            "2026-09-10",
            Some("d1b4aa5df"),
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "FLOOD_EAGER_GENERATION_MAX",
            )],
            &[
                commit(
                    "8066e48be",
                    "flood-prevention admission for the UF e-graph instantiation loop",
                ),
                commit(
                    "d910fa590",
                    "instance SELECTION becomes a policy object, and the funnel that says whether it ran",
                ),
                doc(
                    "docs/research/03-measurements/what-the-admission-filter-rejects-2026-09-10.md",
                ),
            ],
        ),
        note: "RE-MEASURED 2026-09-10 on the 32-file UF parity-loss slice, post-`d910fa590`: `budget_flood_slice` classified 492,833 deferred candidates across 243 engaged slices, and 96,631 of them (19.6 %) sat at generation <= 1 and were kept eagerly. The eager exemption is protecting a fifth of the flood-regime traffic from the round cap, not a rounding error. Z3 `qi.eager_threshold` analogue. The doc comment's `x2015..1276224` example (a 418-candidate deferred dump carrying the refutation, lost when eagerness was capped tighter) is the measurement this value rests on.",
    },
    ConfigEntry {
        name: "FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "2048",
        unit: "accumulated ground terms",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-01",
            Some("8066e48be"),
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND",
            )],
            &[commit(
                "8066e48be",
                "flood-prevention admission for the UF e-graph instantiation loop",
            )],
        ),
        note: "Activation threshold for the generation-layered subset-first final check. Below it the plain final check runs; the doc comment measures a 26.7s wasted full check on `uf.1158058` at 8192 conjuncts as the wall this exists to avoid.",
    },
    ConfigEntry {
        name: "FLOOD_FINAL_SUBSET_MAX_GENERATION",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "1",
        unit: "instantiation generation",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-01",
            Some("8066e48be"),
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "FLOOD_FINAL_SUBSET_MAX_GENERATION",
            )],
            &[commit(
                "8066e48be",
                "flood-prevention admission for the UF e-graph instantiation loop",
            )],
        ),
        note: "Companion to FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND: scopes the subset-first attempt to sources plus purely source-derived instances. Missing the accelerated attempt only falls back to the ordinary full final check.",
    },
    ConfigEntry {
        name: "FLOOD_ROUND_ADMISSION_CAP",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "256",
        unit: "deferred instances admitted per round",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "an instance held back this round is re-materialized and re-classified next round -- possibly as a conflict by then -- and is never dropped (doc comment)",
        env_override: None,
        justification: dated(
            "docs/research/03-measurements/what-the-admission-filter-rejects-2026-09-10.md",
            "2026-09-10",
            Some("d1b4aa5df"),
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "FLOOD_ROUND_ADMISSION_CAP",
            )],
            &[
                commit(
                    "8066e48be",
                    "flood-prevention admission for the UF e-graph instantiation loop",
                ),
                commit(
                    "d910fa590",
                    "instance SELECTION becomes a policy object, and the funnel that says whether it ran",
                ),
                doc(
                    "docs/research/03-measurements/what-the-admission-filter-rejects-2026-09-10.md",
                ),
            ],
        ),
        note: "RE-MEASURED 2026-09-10 on the 32-file UF parity-loss slice, post-`d910fa590`: of 878 deferred-pool releases in the whole slice, 262 reached the throttle and 243 of those also exceeded this cap, so where the throttle engages the cap almost always acts (92.7 %). It truncated 18,576 candidate tuples belonging to universals that ended the run with nothing admitted. THE FINDING commit's headline measurement: `dl_copy_invariant_19_2` dumped a geometric 34->5957-candidate deferred pool per round, hitting MAX_GROUND_TERMS around round 9-15 on almost entirely inert traffic (8080 of 8164 derived-from-derived). Conflict/unit instances stay eager and unbudgeted; budgeting the unit pool the same way was measured net-negative and reverted.",
    },
    ConfigEntry {
        name: "FLOOD_THROTTLE_MIN_GROUND",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "2048",
        unit: "accumulated ground terms",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "below this ground-set size every release behaves exactly like the historical dump-everything admission; above it, held-back instances are still re-classified every round and never dropped (doc comment)",
        env_override: None,
        justification: dated(
            "docs/research/03-measurements/what-the-admission-filter-rejects-2026-09-10.md",
            "2026-09-10",
            Some("d1b4aa5df"),
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "FLOOD_THROTTLE_MIN_GROUND",
            )],
            &[
                commit(
                    "8066e48be",
                    "flood-prevention admission for the UF e-graph instantiation loop",
                ),
                commit(
                    "d910fa590",
                    "instance SELECTION becomes a policy object, and the funnel that says whether it ran",
                ),
                doc(
                    "docs/research/03-measurements/what-the-admission-filter-rejects-2026-09-10.md",
                ),
            ],
        ),
        note: "RE-MEASURED 2026-09-10 on the 32-file UF parity-loss slice, post-`d910fa590`: 878 deferred-pool releases, of which only 262 (29.8 %) happened at or past this threshold -- 70.2 % of this population's releases are below it and behave as the historical dump-everything admission. 25 of 32 files engage the throttle at some point. The threshold is not idle, but it sees under a third of the releases. Doc comment measures the risk of setting this too low: `uf.1001519`'s ~7000-candidate release at ground=1150 is what main refutes from in 4.4s, and throttling its deep tail changed which instances filled the cap and lost the file.",
    },
    ConfigEntry {
        name: "INVENTION_GROUND_CEILING",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "MAX_GROUND_TERMS / 2",
        unit: "accumulated ground terms",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "invented terms flow only through the unchanged instantiation-certificate admission gate (module doc); declining invention here can only omit a possible match, never certify a wrong one",
        env_override: None,
        justification: undated("doc comment"),
        note: "Deliberately tied to MAX_GROUND_TERMS by definition, so the two move together: invention must stop well before the flood-class ground cap so a fixpoint-free file cannot gain extra term traffic from this route.",
    },
    ConfigEntry {
        name: "MAX_CANDIDATE_APPLICATIONS",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "16_384",
        unit: "candidate application terms",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "candidate equalities are a bounded search hint, never a proof premise (ADR-0120); exceeding this cap declines scoped candidate matching only, and the established fresh-QF route remains live (doc comment)",
        env_override: None,
        justification: dated(
            "ADR-0120",
            "2026-07-11",
            None,
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "MAX_CANDIDATE_APPLICATIONS",
            )],
            &[adr("ADR-0120")],
        ),
        note: "Paired with MAX_CANDIDATE_EQUALITIES for the ADR-0120 scoped SAT-candidate equality e-matching accelerator.",
    },
    ConfigEntry {
        name: "MAX_CANDIDATE_EQUALITIES",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "4096",
        unit: "candidate equalities",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "candidate equalities are a bounded search hint, never a proof premise (ADR-0120); exceeding this cap declines scoped candidate matching only, and the established fresh-QF route remains live (doc comment)",
        env_override: None,
        justification: dated(
            "ADR-0120",
            "2026-07-11",
            None,
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "MAX_CANDIDATE_EQUALITIES",
            )],
            &[adr("ADR-0120")],
        ),
        note: "Paired with MAX_CANDIDATE_APPLICATIONS for the ADR-0120 scoped SAT-candidate equality e-matching accelerator.",
    },
    ConfigEntry {
        name: "MAX_DIRECT_INSTANCES_PER_UNIVERSAL_STEP",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "8",
        unit: "direct staged instances per universal per step",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "direct instances flow only through the unchanged instantiation-certificate admission gate (doc comment); truncating this step can only omit a possible tuple, never certify a wrong one",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-01",
            Some("1584a6236"),
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "MAX_DIRECT_INSTANCES_PER_UNIVERSAL_STEP",
            )],
            &[commit(
                "1584a6236",
                "term invention for the term-starved UF refutation class",
            )],
        ),
        note: "Measured on `Arrow_Order/uf.616692`: a 4-var universal's 9^4 cartesian join consumed the whole shared per-round join budget every round, so a starved 6-var universal emitted zero tuples across 12 rounds (`starved_joins=12, admitted=0`). Direct staging bypasses that starvation.",
    },
    ConfigEntry {
        name: "MAX_DIRECT_INSTANCES_TOTAL",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "1024",
        unit: "direct staged instances",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "direct instances flow only through the unchanged instantiation-certificate admission gate (doc comment); truncating this step can only omit a possible tuple, never certify a wrong one",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-01",
            Some("1584a6236"),
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "MAX_DIRECT_INSTANCES_TOTAL",
            )],
            &[commit(
                "1584a6236",
                "term invention for the term-starved UF refutation class",
            )],
        ),
        note: "Total budget across all universals for the direct-staging fallback (`Arrow_Order/uf.616692` join-starvation class).",
    },
    ConfigEntry {
        name: "MAX_DIRECT_TUPLE_VISITS_PER_UNIVERSAL_STEP",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "512",
        unit: "visited seed tuples per universal per step",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "direct instances flow only through the unchanged instantiation-certificate admission gate (doc comment); truncating this step can only omit a possible tuple, never certify a wrong one",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-01",
            Some("1584a6236"),
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "MAX_DIRECT_TUPLE_VISITS_PER_UNIVERSAL_STEP",
            )],
            &[commit(
                "1584a6236",
                "term invention for the term-starved UF refutation class",
            )],
        ),
        note: "Bounds re-enumeration cost on wide prefixes independently of how many tuples are new.",
    },
    ConfigEntry {
        name: "MAX_DISCOVERED_REGISTRATIONS",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "256",
        unit: "discovered universal registrations",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "a discovered registration is only scanned once it is `trusted` -- asserted, or its derivation already passed `check_quantifier_ground_derivation` at admission (`NestedDiscovery::is_trusted`, qinst_egraph.rs:713-719); truncating discovery can only omit a registration, never trust an unchecked one",
        env_override: None,
        justification: undated("doc comment"),
        note: "LIVE in the shipped configuration -- gated on `AXEYUM_NESTED_QUANT`, whose default is ON, so only an explicit `AXEYUM_NESTED_QUANT=0` disables it (Slice-3 lazy-discovery caps, doc comment at qinst_egraph.rs:129); zero effect only under an explicit opt-out, since nothing is then discovered or appended.",
    },
    ConfigEntry {
        name: "MAX_DISCOVERY_REBUILDS",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "8",
        unit: "matcher rebuilds",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "a rebuild only re-compiles patterns and re-ingests the already-admitted ground set; stopping further rebuilds can only forgo picking up new discovered terms sooner, never admit anything unchecked",
        env_override: None,
        justification: undated("doc comment"),
        note: "LIVE in the shipped configuration -- gated on `AXEYUM_NESTED_QUANT`, whose default is ON, so only an explicit `AXEYUM_NESTED_QUANT=0` disables it (Slice-3 lazy-discovery caps); a rebuild re-compiles patterns and re-ingests the ground set, so this is what bounds discovery's overhead.",
    },
    ConfigEntry {
        name: "MAX_EXTENDED_INSTANTIATION_ROUNDS",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "512",
        unit: "instantiation rounds",
        protects: Protects::Termination,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "the loop falls through to `finish_quantified_ground_check` with whatever ground instances are already accumulated, which is independently checked; this hard ceiling exists only so the loop is deterministic (\"never hang\") when neither the wall clock nor MAX_GROUND_TERMS is what stops it (doc comment)",
        env_override: None,
        justification: undated("doc comment"),
        note: "Hard ceiling on `for round in 0..MAX_EXTENDED_INSTANTIATION_ROUNDS`. The wall-clock deadline and MAX_GROUND_TERMS are the practical bounds in ordinary operation; this is the backstop when neither is configured.",
    },
    ConfigEntry {
        name: "MAX_GROUND_TERMS",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "8192",
        unit: "accumulated ground terms",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_QINST_GROUND"),
        justification: dated(
            "docs/research/12-performance/uf-quantified-loss-attribution-2026-09-09.md",
            "2026-09-09",
            None,
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "GroundBudget",
            )],
            &[
                doc("docs/research/12-performance/uf-quantified-loss-attribution-2026-09-09.md"),
                live("GroundBudget", "crates/axeyum-solver/src/qinst_egraph.rs"),
                live(
                    "floodprobe_cap_census",
                    "crates/axeyum-solver/src/qinst_egraph.rs",
                ),
            ],
        ),
        note: "The \"never hang\" ceiling: `egraph_ground_limit()` returns `CheckResult::Unknown` with detail \"e-matching: ground-term count budget exhausted\" even with no wall-clock budget configured. It is now the `ceiling` of `GroundBudget::SHIPPED`, and the use sites read `ground_budget()`, so the value is A/B-able through `AXEYUM_QINST_GROUND=<n>` without a patch; `MAX_JOINED_SUBSTITUTIONS_PER_ROUND` (`= ceiling`) and `INVENTION_GROUND_CEILING` (`= ceiling / 2`) move with it, which `shipped_ground_budget_is_the_scaled_shipped_ceiling` pins. MEASURED 2026-09-09 on `bench-results/parity-losses-20260908/UF.txt` (32 files, 24 s / 8 GiB, s4): 24 of 32 reach an e-matching fixpoint at exactly this ceiling, so it IS the operative stop for the division -- and note the exit, because the `ground.len() > ceiling` branch fires ZERO times: the ceiling acts through the admission gate one step earlier, so these files never print `egraph_ground_limit()`'s message at all. Raising it is still the wrong lever. `AXEYUM_FLOODPROBE=1`'s census over the 25 files whose fixpoint sits here reports 200,781 admitted instances of which ZERO are conflicting clauses (0 on every file), 0.3% are units (present on 6 of the 25), 67.6% are already TRUE under the current congruence and 82.8% are generation >= 2. The ceiling is full of instances that decide nothing; a bigger ceiling holds more of them. The bound this division needs is on instance SELECTION, which no value of this field expresses.",
    },
    ConfigEntry {
        name: "MAX_INSTANTIATION_ROUNDS",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "8",
        unit: "instantiation rounds",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Former hard round budget, now purely the cadence anchor for interleaved refutation checks (every round inside the window, power-of-two rounds beyond it -- `interleaved_check_due`, qinst_egraph.rs:1677-1682): every refutation the historical budget found is still found at the same cost.",
    },
    ConfigEntry {
        name: "MAX_INVENTED_TERMS_PER_PATTERN_STEP",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "4",
        unit: "invented terms per pattern per fixpoint step",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "invented terms flow only through the unchanged instantiation-certificate admission gate (module doc); truncating invention can only omit a possible match, never certify a wrong one",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-01",
            Some("1584a6236"),
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "MAX_INVENTED_TERMS_PER_PATTERN_STEP",
            )],
            &[commit(
                "1584a6236",
                "term invention for the term-starved UF refutation class",
            )],
        ),
        note: "Term-invention caps for the term-starved fixpoint class, measured on `Arrow_Order/uf.616692` (doc comment at qinst_egraph.rs:158-172): e-matching alone reaches its fixpoint in microseconds with ground=2 because every application sits under a binder, so terms must be built, not found.",
    },
    ConfigEntry {
        name: "MAX_INVENTED_TERMS_PER_STEP",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "32",
        unit: "invented terms per fixpoint step",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "invented terms flow only through the unchanged instantiation-certificate admission gate (module doc); truncating invention can only omit a possible match, never certify a wrong one",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-01",
            Some("1584a6236"),
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "MAX_INVENTED_TERMS_PER_STEP",
            )],
            &[commit(
                "1584a6236",
                "term invention for the term-starved UF refutation class",
            )],
        ),
        note: "Deliberately small: a measured one-step run of 64 blasted the joined-instance admission from 2 to 4098 ground terms in a single round on `Arrow_Order/uf.616692`, drowning the roughly nine refuting instances (doc comment).",
    },
    ConfigEntry {
        name: "MAX_INVENTED_TERMS_TOTAL",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "2048",
        unit: "invented terms",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "invented terms flow only through the unchanged instantiation-certificate admission gate (module doc); truncating invention can only omit a possible match, never certify a wrong one",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-01",
            Some("1584a6236"),
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "MAX_INVENTED_TERMS_TOTAL",
            )],
            &[commit(
                "1584a6236",
                "term invention for the term-starved UF refutation class",
            )],
        ),
        note: "Total budget across all fixpoint steps for the term-starved-class invention mechanism (`Arrow_Order/uf.616692`).",
    },
    ConfigEntry {
        name: "MAX_INVENTION_SEEDS_PER_SORT",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "12",
        unit: "seed terms per sort",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "invented terms flow only through the unchanged instantiation-certificate admission gate (module doc); truncating invention can only omit a possible match, never certify a wrong one",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-01",
            Some("1584a6236"),
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "MAX_INVENTION_SEEDS_PER_SORT",
            )],
            &[commit(
                "1584a6236",
                "term invention for the term-starved UF refutation class",
            )],
        ),
        note: "Seed terms considered per sort, constants first then existing ground application representatives, both in deterministic term order.",
    },
    ConfigEntry {
        name: "MAX_INVENTION_TUPLE_VISITS_PER_PATTERN_STEP",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "512",
        unit: "visited seed tuples per pattern per fixpoint step",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "invented terms flow only through the unchanged instantiation-certificate admission gate (module doc); truncating invention can only omit a possible match, never certify a wrong one",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-08-01",
            Some("1584a6236"),
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "MAX_INVENTION_TUPLE_VISITS_PER_PATTERN_STEP",
            )],
            &[commit(
                "1584a6236",
                "term invention for the term-starved UF refutation class",
            )],
        ),
        note: "Bounds re-enumeration cost on wide prefixes independently of how many tuples are new -- companion to MAX_DIRECT_TUPLE_VISITS_PER_UNIVERSAL_STEP for the invention (rather than direct-staging) mechanism.",
    },
    ConfigEntry {
        name: "MAX_JOINED_SUBSTITUTIONS_PER_ROUND",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "MAX_GROUND_TERMS",
        unit: "joined substitution tuples per round",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "fewer joined substitutions can only lose an instantiation this round, never fabricate one; the public one-shot witness API (`witness_tuples_via_egraph`) remains complete (doc comment)",
        env_override: None,
        justification: undated("doc comment"),
        note: "Internal tuple-join cap per retained matching round, preventing a multi-pattern Cartesian product from allocating beyond the solver's own accumulated-ground budget. Defined as `= MAX_GROUND_TERMS`, so the two always move together.",
    },
    ConfigEntry {
        name: "MAX_POSITIVE_INSTANCES",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "4096",
        unit: "positive replacements",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "a positive replacement is trusted only via the same `is_trusted`/`check_quantifier_ground_derivation` admission path as MAX_DISCOVERED_REGISTRATIONS (qinst_egraph.rs:713-719); truncating this can only omit a replacement, never trust an unchecked one",
        env_override: None,
        justification: undated("doc comment"),
        note: "LIVE in the shipped configuration -- gated on `AXEYUM_NESTED_QUANT`, whose default is ON, so only an explicit `AXEYUM_NESTED_QUANT=0` disables it; total positive replacements admitted or promoted over one attempt.",
    },
    ConfigEntry {
        name: "MAX_POSITIVE_TUPLES_PER_ROUND",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "256",
        unit: "positive tuples per round",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "a positive tuple is trusted only via the same `is_trusted`/`check_quantifier_ground_derivation` admission path as MAX_DISCOVERED_REGISTRATIONS (qinst_egraph.rs:713-719); truncating this can only omit a tuple, never trust an unchecked one",
        env_override: None,
        justification: undated("doc comment"),
        note: "LIVE in the shipped configuration -- gated on `AXEYUM_NESTED_QUANT`, whose default is ON, so only an explicit `AXEYUM_NESTED_QUANT=0` disables it. Discovery adds formulas, not just terms, so it is budgeted separately from MAX_GROUND_TERMS: a join emitting ten thousand tuples must not convert the whole budget into positive replacements before the ordinary schedules get a round.",
    },
    ConfigEntry {
        name: "MAX_PREDECESSOR_RECURRENCE_INDEX",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "64",
        unit: "recurrence index",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "declining only forgoes this closed-form sign-contradiction shortcut; the query proceeds through the ordinary e-matching instantiation loop, which is independently sound",
        env_override: Some("AXEYUM_MAX_PREDECESSOR_RECURRENCE_INDEX"),
        justification: undated("doc comment"),
        note: "Caps the matched `f(x-index)` recurrence index in `predecessor_recurrence_sign_refutation`'s pattern match; above it the shortcut simply does not fire.",
    },
    ConfigEntry {
        name: "MAX_PROMOTED_UNIVERSALS",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "64",
        unit: "promoted universals",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "a promoted universal is trusted only via the same `is_trusted`/`check_quantifier_ground_derivation` admission path as MAX_DISCOVERED_REGISTRATIONS (qinst_egraph.rs:713-719); truncating this can only omit a promotion, never trust an unchecked one",
        env_override: None,
        justification: undated("doc comment"),
        note: "LIVE in the shipped configuration -- gated on `AXEYUM_NESTED_QUANT`, whose default is ON, so only an explicit `AXEYUM_NESTED_QUANT=0` disables it. Universals promoted from a positive replacement that kept binders.",
    },
    ConfigEntry {
        name: "MAX_QUANTIFIER_PROVENANCE_DEPTH",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "16",
        unit: "provenance-chain depth",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`check_propagation` returns `false` past this depth, which makes `collect_ground_derivations` decline (return `None`) rather than emit an unreplayable certificate (qinst_egraph.rs:3014-3016, 3040)",
        env_override: Some("AXEYUM_MAX_QUANTIFIER_PROVENANCE_DEPTH"),
        justification: undated("doc comment"),
        note: "Admission cap on the `QuantifierProvenanceChecker` that validates a retained-CDCL(T) checked-clause derivation is replayable from anchor/ground assertions before it is trusted.",
    },
    ConfigEntry {
        name: "MAX_QUANTIFIER_PROVENANCE_NODES",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "4096",
        unit: "provenance-checker node visits",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the checker's `take_node` budget exhausting makes `check_propagation` return `false`, so `collect_ground_derivations` declines (returns `None`) rather than emit an unreplayable certificate (qinst_egraph.rs:3014-3016)",
        env_override: Some("AXEYUM_MAX_QUANTIFIER_PROVENANCE_NODES"),
        justification: undated("doc comment"),
        note: "Sibling cap to MAX_QUANTIFIER_PROVENANCE_DEPTH on the same provenance-checker walk.",
    },
    ConfigEntry {
        name: "MID_LOOP_CHECK_BUDGET_DIVISOR",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "4",
        unit: "divisor of the remaining shared deadline",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Mid-loop (extended-cadence) ground checks run under `remaining / divisor` of the shared budget via `fractional_deadline`, so one large mid-loop check cannot starve later rounds or the final check.",
    },
    ConfigEntry {
        name: "ONLINE_QUANTIFIER_LIMITS",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "variables 65_536 / clauses 262_144 / literals 262_144",
        unit: "Boolean variables, clauses, and literals in the retained CDCL(T) session",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the accelerator is an OPTIMIZATION: `OnlineQuantifierClauseSession::new` returns `None` past any of the three and the caller falls back to the established fresh quantifier-free refutation check, which decides the same conjunction -- so a silent crossing costs a warm session, never a verdict (ADR-0119)",
        env_override: None,
        justification: undated("doc comment + ADR-0119"),
        note: "Found UNREGISTERED on 2026-09-09 while attributing the `UF` loss population. It is the only constant in `qinst_egraph.rs` (31 of them) that this registry did not carry, and the reason is mechanical rather than an oversight: it is a STRUCT-valued constant (`OnlineQuantifierLimits`), and the coverage scanner in this file matches only scalar and `Duration` types, so `every_governing_constant_is_registered` could never have named it even had the file been in `GOVERNED_FILES`. That blind spot is the finding; this entry closes the instance. Exceeding any of the three disables only the retained-CDCL(T) accelerator (ADR-0119) -- the established fresh-QF route stays live, so a crossing costs speed and never a verdict.",
    },
    ConfigEntry {
        name: "RELEVANCE_EVICT_MIN_GROUND",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "FLOOD_THROTTLE_MIN_GROUND",
        unit: "accumulated ground terms",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::None,
        guarded_by: "the sweep it gates only DROPS ground conjuncts the congruence already entails, and only ones that are not themselves a top-level positive equality -- so `ground \\ dropped` still entails every dropped clause and the two sets are equisatisfiable; not reaching this threshold therefore costs nothing but the sweep",
        env_override: Some("AXEYUM_QINST_RELEVANCE"),
        justification: dated(
            "docs/research/12-performance/uf-instance-selection-2026-09-09.md",
            "2026-09-09",
            None,
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "RelevancePolicy",
            )],
            &[
                doc("docs/research/12-performance/uf-instance-selection-2026-09-09.md"),
                live(
                    "evict_entailed_instances",
                    "crates/axeyum-solver/src/qinst_egraph.rs",
                ),
            ],
        ),
        note: "NOT A SHIPPED BOUND: `RelevancePolicy::SHIPPED` sets `evict_entailed: false`, so this threshold is never consulted unless an A/B arm (`evict`, `full`) is selected. Tied to FLOOD_THROTTLE_MIN_GROUND by definition and for its reason: below it the loop is not under ceiling pressure and every release behaves like the historical dump-everything admission, so a sweep over the retained pool is pure overhead on the files that refute from the dump. Measured 2026-09-09 on the 32-file UF loss population: the sweep examined 846,617 eligible retained instances and evicted 1,368 of them (0.16 %), and decided 0 additional files.",
    },
    ConfigEntry {
        name: "RELEVANCE_NARROW_RESIDUAL_WIDTH",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "3",
        unit: "open (not-yet-falsified) literals in a candidate clause",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "a declined candidate is never DROPPED: the retained matcher re-materializes and re-classifies the whole deferred pool on every later round, so a candidate this width filter passes over is re-offered (and may be a conflict or a unit by then, in which case it is admitted eagerly and unbudgeted)",
        env_override: Some("AXEYUM_QINST_RELEVANCE"),
        justification: dated(
            "docs/research/12-performance/uf-instance-selection-2026-09-09.md",
            "2026-09-09",
            None,
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "RelevancePolicy",
            )],
            &[
                doc("docs/research/12-performance/uf-instance-selection-2026-09-09.md"),
                live(
                    "clause_residual_width",
                    "crates/axeyum-solver/src/qinst_egraph.rs",
                ),
            ],
        ),
        note: "NOT A SHIPPED BOUND: `RelevancePolicy::SHIPPED` sets `max_residual_width: usize::MAX`, so nothing is declined by width unless an A/B arm (`narrow`, `full`) is selected. The value is the first band above a unit clause. Measured 2026-09-09 on the 32-file UF loss population, and the measurement is the reason the arm is not shipped: the residual band of the whole population is 1 to 4, so this declines only the width-4 tail (8,259 of 290,116 scored candidates, 2.8 %) and decides 0 additional files. 85.6 % of the scored candidates carry a literal the congruence classifier cannot value at all, which is the ceiling on what any width-based bound can do here.",
    },
    ConfigEntry {
        name: "ROUND_GROWTH_HEADROOM",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "8",
        unit: "multiple of the previous round's duration",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "breaking early only skips further instantiation rounds; the final ground check still runs over whatever instances are already accumulated, and any accepted instance is independently checked",
        env_override: None,
        justification: undated("doc comment"),
        note: "A new round starts only when the remaining budget is at least this multiple of the last round's duration: per-round work has grown 10x+ round-over-round on real corpora with an e-matcher that carries no internal deadline, so starting a round without this headroom risks a deadline overshoot as large as the round itself.",
    },
    ConfigEntry {
        name: "SHIPPED_RELEVANCE_POLICY",
        module: "crates/axeyum-solver/src/qinst_egraph.rs",
        value: "rank_by_residual false / max_residual_width usize::MAX / evict_entailed false / criterion EqualityOnly / throttle_min_ground 2048 / round_admission_cap 256 / eager_generation_max 1",
        unit: "instance-selection levers and the thresholds they are gated by",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::None,
        guarded_by: "every lever is off in the shipped arm, and `budget_flood_slice`'s shipped branch is the historical body verbatim -- so the shipped configuration of this object is not a bound at all, it is the absence of one; the three thresholds are aliases of FLOOD_THROTTLE_MIN_GROUND, FLOOD_ROUND_ADMISSION_CAP and FLOOD_EAGER_GENERATION_MAX, each registered in its own right, and the shipped criterion is what the shipped admission classifier already knows",
        env_override: Some("AXEYUM_QINST_RELEVANCE"),
        justification: dated(
            "docs/research/12-performance/uf-instance-selection-2026-09-09.md",
            "2026-09-09",
            None,
            &[sym(
                "crates/axeyum-solver/src/qinst_egraph.rs",
                "RelevancePolicy",
            )],
            &[
                doc("docs/research/12-performance/uf-instance-selection-2026-09-09.md"),
                live(
                    "relevance_policy",
                    "crates/axeyum-solver/src/qinst_egraph.rs",
                ),
            ],
        ),
        note: "REGISTERED BY HAND, and that is the entry's second purpose. `RelevancePolicy` is STRUCT-valued, and this file's coverage scanner matches only scalar and `Duration` types -- the same blind spot recorded on ONLINE_QUANTIFIER_LIMITS on 2026-09-09, which is not closed by either entry. A struct-valued governing constant anywhere in a governed file is still invisible to `every_governing_constant_is_registered`, so it is registered here because someone chose to, not because a gate would have caught its absence. The object itself is the selection policy of the quantifier instantiation loop, the counterpart to GroundBudget's volume policy; `shipped_relevance_policy_is_the_shipped_selection` pins that no arm moves one of the three thresholds instead of one of the three levers, which is what would make an A/B on a lever not an A/B on that lever.",
    },
    ConfigEntry {
        name: "MAX_BOUND_BOOL_BRANCHES",
        module: "crates/axeyum-solver/src/quant_bool_model_sat.rs",
        value: "131_072",
        unit: "bound-Boolean branches (CheckBudget work-meter units)",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "an exhausted walk marks the block unproved (\"exhausted\" is sticky, so every later sub-result is `Unknown` rather than a value derived from a truncated traversal\" -- doc comment); the module's own contract is that this \"blocks that complete Boolean assignment or declines; it never produces a verdict\"",
        env_override: None,
        justification: undated("doc comment"),
        note: "One of the two `CheckBudget`/`WorkMeter` resource caps for the structural certificate re-check walk (the independent checker, not the search).",
    },
    ConfigEntry {
        name: "MAX_CANDIDATES",
        module: "crates/axeyum-solver/src/quant_bool_model_sat.rs",
        value: "256",
        unit: "candidate ground assignments tried",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the search returns `Declined`; `decide_quantified_by_bool_model` maps that to `Ok(None)` and the front-door dispatcher falls through to other quantifier routes, reporting `unknown` only if none succeed",
        env_override: None,
        justification: undated("doc comment"),
        note: "Loop budget on `search_quantified_bool_model`'s `for _ in 0..MAX_CANDIDATES` candidate-assignment enumeration.",
    },
    ConfigEntry {
        name: "MAX_CHECK_NODES",
        module: "crates/axeyum-solver/src/quant_bool_model_sat.rs",
        value: "100_000",
        unit: "visited term nodes (CheckBudget work-meter units)",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "an exhausted walk marks the block unproved (\"exhausted\" is sticky, so every later sub-result is `Unknown` rather than a value derived from a truncated traversal\" -- doc comment); the module's own contract is that this \"blocks that complete Boolean assignment or declines; it never produces a verdict\"",
        env_override: None,
        justification: undated("doc comment"),
        note: "Sibling cap to MAX_BOUND_BOOL_BRANCHES on the same structural certificate re-check walk.",
    },
    ConfigEntry {
        name: "MAX_FREE_BOOLEANS",
        module: "crates/axeyum-solver/src/quant_bool_model_sat.rs",
        value: "64",
        unit: "free Boolean symbols",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the search returns `Declined`; `decide_quantified_by_bool_model` maps that to `Ok(None)` and the front-door dispatcher falls through to other quantifier routes, reporting `unknown` only if none succeed",
        env_override: Some("AXEYUM_MAX_FREE_BOOLEANS"),
        justification: undated("doc comment"),
        note: "Admission gate before erasure/enumeration: bounds the free-Boolean set whose full 2^n candidate space this route is willing to search.",
    },
    ConfigEntry {
        name: "QUANT_BOOL_BV_MODEL_BINDER_CAP",
        module: "crates/axeyum-solver/src/quant_bool_model_sat.rs",
        value: "128",
        unit: "quantifier binders",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`admitted_positive_universal_bv` returns `None`, which bubbles through `positive_universal_bv_residual` to decline only the residual-QF_BV model-proof route",
        env_override: Some("AXEYUM_QUANT_BOOL_BV_MODEL_BINDER_CAP"),
        justification: undated("doc comment"),
        note: "Admission cap for a residual-QF_BV model proof over an admitted positive Bool/BV universal.",
    },
    ConfigEntry {
        name: "QUANT_BOOL_BV_MODEL_DEPTH_CAP",
        module: "crates/axeyum-solver/src/quant_bool_model_sat.rs",
        value: "256",
        unit: "source term depth",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`admitted_positive_universal_bv` returns `None`, which bubbles through `positive_universal_bv_residual` to decline only the residual-QF_BV model-proof route",
        env_override: Some("AXEYUM_QUANT_BOOL_BV_MODEL_DEPTH_CAP"),
        justification: undated("doc comment"),
        note: "Recursion-depth cap for the same residual-QF_BV model-proof admission walk as the binder/node caps.",
    },
    ConfigEntry {
        name: "QUANT_BOOL_BV_MODEL_NODE_CAP",
        module: "crates/axeyum-solver/src/quant_bool_model_sat.rs",
        value: "4_096",
        unit: "distinct source nodes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`admitted_positive_universal_bv` returns `None`, which bubbles through `positive_universal_bv_residual` to decline only the residual-QF_BV model-proof route",
        env_override: Some("AXEYUM_QUANT_BOOL_BV_MODEL_NODE_CAP"),
        justification: undated("doc comment"),
        note: "Sibling cap to QUANT_BOOL_BV_MODEL_BINDER_CAP; checked twice in the traversal (against both `source_nodes` and `visited`).",
    },
    ConfigEntry {
        name: "BV_ALTERNATION_BINDER_CAP",
        module: "crates/axeyum-solver/src/quant_bv_alternation_cert.rs",
        value: "1024",
        unit: "quantifier binders (both blocks combined)",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`admitted_alternation` returns `None`, declining both the search (`quant_bv_alternation_search.rs:32`) and the certificate recheck (`quant_bv_alternation_cert.rs:52`) for this route only",
        env_override: Some("AXEYUM_BV_ALTERNATION_BINDER_CAP"),
        justification: undated("doc comment"),
        note: "Shared admission gate (ADR-0125): the same constant admits the search and re-validates the certificate it produces.",
    },
    ConfigEntry {
        name: "BV_ALTERNATION_NODE_CAP",
        module: "crates/axeyum-solver/src/quant_bv_alternation_cert.rs",
        value: "4096",
        unit: "reachable matrix nodes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`closed_qf_bool_bv` returns `false` past this cap, which makes `admitted_alternation` decline; the search and cert-recheck both fall through to other routes",
        env_override: Some("AXEYUM_BV_ALTERNATION_NODE_CAP"),
        justification: undated("doc comment"),
        note: "Node-count sibling to BV_ALTERNATION_BINDER_CAP on the quantifier-free matrix.",
    },
    ConfigEntry {
        name: "BV_CONJUNCTIVE_UNIVERSAL_BINDER_CAP",
        module: "crates/axeyum-solver/src/quant_bv_conjunctive_cert.rs",
        value: "128",
        unit: "universal binders",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the admission walk declines (returns `None`), which forgoes only this conjunctive-universal-instance certificate route",
        env_override: Some("AXEYUM_BV_CONJUNCTIVE_UNIVERSAL_BINDER_CAP"),
        justification: undated("doc comment"),
        note: "Admission cap on the source checker for ADR-0127 conjunctive universal instances.",
    },
    ConfigEntry {
        name: "BV_CONJUNCTIVE_UNIVERSAL_NODE_CAP",
        module: "crates/axeyum-solver/src/quant_bv_conjunctive_cert.rs",
        value: "4_096",
        unit: "distinct source nodes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the admission walk declines (returns `None`), which forgoes only this conjunctive-universal-instance certificate route",
        env_override: Some("AXEYUM_BV_CONJUNCTIVE_UNIVERSAL_NODE_CAP"),
        justification: undated("doc comment"),
        note: "Node-count sibling to BV_CONJUNCTIVE_UNIVERSAL_BINDER_CAP; also checked against `2 * cap` at one intermediate visited-count site (quant_bv_conjunctive_cert.rs:215).",
    },
    ConfigEntry {
        name: "SEARCH_CANDIDATE_CAP",
        module: "crates/axeyum-solver/src/quant_bv_conjunctive_search.rs",
        value: "256",
        unit: "attempted binding candidates",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`find_bv_conjunctive_universal_instance` returns `Ok(None)`; the caller tries other quantifier routes and reports `unknown` only if none succeed",
        env_override: None,
        justification: undated("doc comment"),
        note: "Loop budget on the per-binder default-value substitution search, alongside the shared deadline.",
    },
    ConfigEntry {
        name: "BV_POSITIVE_INSTANCE_SET_CAP",
        module: "crates/axeyum-solver/src/quant_bv_instance_set_cert.rs",
        value: "256",
        unit: "source instances in one certificate",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the checker rejects a certificate whose instance count exceeds this cap; the caller falls through to other quantifier routes",
        env_override: Some("AXEYUM_BV_POSITIVE_INSTANCE_SET_CAP"),
        justification: undated("doc comment"),
        note: "Admission cap on one query-scoped ADR-0134 positive-universal instance-set certificate.",
    },
    ConfigEntry {
        name: "QUANT_BV_MODEL_BINDER_CAP",
        module: "crates/axeyum-solver/src/quant_bv_model_sat_cert.rs",
        value: "128",
        unit: "quantifier binders",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the checker's admission walk declines, rejecting only this certificate; candidate search (in `quant_bv_model_sat_search.rs`) is a separate, untrusted module by design (module doc)",
        env_override: Some("AXEYUM_QUANT_BV_MODEL_BINDER_CAP"),
        justification: undated("doc comment"),
        note: "Admission cap on one source-bound quantified-BV model certificate (ADR-0130/0131).",
    },
    ConfigEntry {
        name: "QUANT_BV_MODEL_DEPTH_CAP",
        module: "crates/axeyum-solver/src/quant_bv_model_sat_cert.rs",
        value: "256",
        unit: "source depth",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the checker's admission walk declines, rejecting only this certificate; candidate search is a separate, untrusted module by design (module doc)",
        env_override: Some("AXEYUM_QUANT_BV_MODEL_DEPTH_CAP"),
        justification: undated("doc comment"),
        note: "Recursion-depth cap for the same certificate-checker walk as QUANT_BV_MODEL_BINDER_CAP/QUANT_BV_MODEL_NODE_CAP.",
    },
    ConfigEntry {
        name: "QUANT_BV_MODEL_NODE_CAP",
        module: "crates/axeyum-solver/src/quant_bv_model_sat_cert.rs",
        value: "4_096",
        unit: "complete source DAG nodes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the checker's admission walk declines, rejecting only this certificate; candidate search is a separate, untrusted module by design (module doc)",
        env_override: Some("AXEYUM_QUANT_BV_MODEL_NODE_CAP"),
        justification: undated("doc comment"),
        note: "Sibling cap to QUANT_BV_MODEL_BINDER_CAP.",
    },
    ConfigEntry {
        name: "FREE_BV_CANDIDATE_BITS",
        module: "crates/axeyum-solver/src/quant_bv_model_sat_search.rs",
        value: "8",
        unit: "free BV bits (low-bit-complete search)",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`decide_quantified_bv_model_sat` returns `Ok(None)` before the `1usize << free.len()` exhaustive mask loop; the caller tries other quantifier routes",
        env_override: Some("AXEYUM_FREE_BV_CANDIDATE_BITS"),
        justification: undated("doc comment"),
        note: "Guards the exhaustive 2^n low-bit mask enumeration against combinatorial blow-up. Every candidate found here is re-checked by the independent `quant_bv_model_sat_cert` checker before being accepted (module doc).",
    },
    ConfigEntry {
        name: "TOTAL_FREE_BV_BITS_CAP",
        module: "crates/axeyum-solver/src/quant_bv_model_sat_search.rs",
        value: "4_096",
        unit: "total free BV bits across all symbols",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`decide_quantified_bv_model_sat` returns `Ok(None)` before starting the search; the caller tries other quantifier routes",
        env_override: Some("AXEYUM_TOTAL_FREE_BV_BITS_CAP"),
        justification: undated("doc comment"),
        note: "Pre-search admission gate, checked before FREE_BV_CANDIDATE_BITS; also declines on `u32` overflow of the summed widths.",
    },
    ConfigEntry {
        name: "BV_PAIRED_EXISTS_BINDER_CAP",
        module: "crates/axeyum-solver/src/quant_bv_paired_exists_cert.rs",
        value: "128",
        unit: "existential binders (both prefixes combined)",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`admitted_paired_existentials` declines (returns `None`), which forgoes only this ADR-0129 paired-existential witness-transfer route",
        env_override: Some("AXEYUM_BV_PAIRED_EXISTS_BINDER_CAP"),
        justification: undated("doc comment"),
        note: "Shared admission gate reused by both the search (quant_bv_paired_exists_search.rs) and the certificate checker.",
    },
    ConfigEntry {
        name: "BV_PAIRED_EXISTS_NODE_CAP",
        module: "crates/axeyum-solver/src/quant_bv_paired_exists_cert.rs",
        value: "4_096",
        unit: "distinct nodes (both source assertions combined)",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the admission walk declines (returns `None`), which forgoes only this ADR-0129 paired-existential witness-transfer route",
        env_override: Some("AXEYUM_BV_PAIRED_EXISTS_NODE_CAP"),
        justification: undated("doc comment"),
        note: "Node-count sibling to BV_PAIRED_EXISTS_BINDER_CAP.",
    },
    ConfigEntry {
        name: "PAIRED_EXISTS_PAIR_CAP",
        module: "crates/axeyum-solver/src/quant_bv_paired_exists_search.rs",
        value: "256",
        unit: "attempted positive/negative assertion pairs",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`find_bv_paired_existential_transfer` returns `Ok(None)`; the caller tries other quantifier routes",
        env_override: None,
        justification: undated("doc comment"),
        note: "Loop budget on the nested assertion-pair search, alongside the shared deadline.",
    },
    ConfigEntry {
        name: "TRANSFER_SUBSET_CAP",
        module: "crates/axeyum-solver/src/quant_bv_paired_exists_search.rs",
        value: "256",
        unit: "attempted transfer subsets",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the enumeration returns early once this budget or the deadline is reached; the caller tries other quantifier routes",
        env_override: None,
        justification: undated("doc comment"),
        note: "Loop budget on the transferred-conjunct subset search within one candidate pair.",
    },
    ConfigEntry {
        name: "MAX_COVER_BINDERS",
        module: "crates/axeyum-solver/src/quant_counterexample_cover.rs",
        value: "128",
        unit: "positive-universal binders",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the source-instance regeneration step declines past this cap, rejecting the case rather than certifying an unregenerated one",
        env_override: Some("AXEYUM_MAX_COVER_BINDERS"),
        justification: undated("doc comment"),
        note: "Admission cap while regenerating one carried universal instance from original IR.",
    },
    ConfigEntry {
        name: "MAX_COVER_SOURCE_NODES",
        module: "crates/axeyum-solver/src/quant_counterexample_cover.rs",
        value: "100_000",
        unit: "visited source nodes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the source-instance regeneration step declines past this cap, rejecting the case rather than certifying an unregenerated one",
        env_override: Some("AXEYUM_MAX_COVER_SOURCE_NODES"),
        justification: undated("doc comment"),
        note: "Node-count sibling to MAX_COVER_BINDERS on the same regeneration walk.",
    },
    ConfigEntry {
        name: "QUANT_COUNTEREXAMPLE_COVER_CASE_CAP",
        module: "crates/axeyum-solver/src/quant_counterexample_cover.rs",
        value: "256",
        unit: "source-bound cubes in one cover",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the checker rejects a certificate whose case count exceeds this cap; search may still find a smaller cover through other means",
        env_override: Some("AXEYUM_QUANT_COUNTEREXAMPLE_COVER_CASE_CAP"),
        justification: undated("doc comment"),
        note: "Admission cap on one checked ADR-0108 finite counterexample cover.",
    },
    ConfigEntry {
        name: "EQ_PARTITION_CASE_CAP",
        module: "crates/axeyum-solver/src/quant_eq_partition_cert.rs",
        value: "1 << 20",
        unit: "representative branches",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`check_equality_partition_refutation` returns `false`, rejecting the certificate; the caller tries other quantifier routes",
        env_override: Some("AXEYUM_EQ_PARTITION_CASE_CAP"),
        justification: undated("doc comment"),
        note: "Admission cap on how many representative branches the ADR-0101 equality-partition checker will visit.",
    },
    ConfigEntry {
        name: "RANGE_SIZE_CAP",
        module: "crates/axeyum-solver/src/quant_finite_cert.rs",
        value: "4096",
        unit: "in-range integer values",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the range-detection helper returns `None` past this width, so `prove_finite_int_quant_unsat_alethe` declines and `evidence.rs`'s `guarded_quant_alethe_certificate` (which is self-validating and tried alongside every other arithmetic route) simply does not fire",
        env_override: Some("AXEYUM_RANGE_SIZE_CAP"),
        justification: undated("doc comment"),
        note: "Same name and value as `crate::quant_guarded_int::RANGE_SIZE_CAP`, and the doc comment at quant_finite_cert.rs:63 says they must match so a certificate is producible whenever the decision engine expands the range. Unlike quant_alethe.rs's WITNESS_CANDIDATE_CAP, this module is one of the tried decision routes in evidence.rs, not post-decision-only proof rendering.",
    },
    ConfigEntry {
        name: "MAX_CLAUSE_LITERALS",
        module: "crates/axeyum-solver/src/quant_fourier_motzkin.rs",
        value: "64",
        unit: "literals in one DNF clause",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "a wider clause simply declines this pass (doc comment); the assertion passes through byte-identical for the general dispatcher to decide",
        env_override: Some("AXEYUM_MAX_CLAUSE_LITERALS"),
        justification: undated("doc comment"),
        note: "Sibling cap to MAX_DNF_CLAUSES on the same DNF-of-the-negation construction.",
    },
    ConfigEntry {
        name: "MAX_DNF_CLAUSES",
        module: "crates/axeyum-solver/src/quant_fourier_motzkin.rs",
        value: "64",
        unit: "conjunctive clauses in the negation's DNF",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "a wider DNF simply declines this pass (doc comment: \"conservative -- avoids blow-up and keeps the exactness argument tractable\"); the assertion passes through byte-identical for the general dispatcher to decide",
        env_override: Some("AXEYUM_MAX_DNF_CLAUSES"),
        justification: undated("doc comment"),
        note: "Bounds the exact real Fourier-Motzkin elimination pass, which is strictly additive: it can only turn an `unknown` into a provably-correct `unsat`/rewrite, or pass an assertion through unchanged (module doc).",
    },
    ConfigEntry {
        name: "RANGE_SIZE_CAP",
        module: "crates/axeyum-solver/src/quant_guarded_int.rs",
        value: "4096",
        unit: "in-range integer values",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "past this width the universal passes through unmodified; the general dispatcher decides it by other means (module doc: \"strictly additive\")",
        env_override: Some("AXEYUM_RANGE_SIZE_CAP"),
        justification: undated("doc comment"),
        note: "Same name and value as `crate::quant_finite_cert::RANGE_SIZE_CAP` -- deliberately matched (quant_finite_cert.rs:63) so a proof is producible whenever this pass decides to expand. This one is the actual rewrite/decision engine: it decides both `sat` and `unsat` by exact finite conjunction over `[lo, hi]`.",
    },
    ConfigEntry {
        name: "NEGATED_EXISTENTIAL_BINDER_CAP",
        module: "crates/axeyum-solver/src/quant_negated_exists_cert.rs",
        value: "128",
        unit: "existential binders",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the source checker's admission walk declines (returns `None`), rejecting only this ADR-0126 negated-existential witness route",
        env_override: Some("AXEYUM_NEGATED_EXISTENTIAL_BINDER_CAP"),
        justification: undated("doc comment"),
        note: "Admission cap on one evaluator-replayed witness for a negated existential.",
    },
    ConfigEntry {
        name: "NEGATED_EXISTENTIAL_NODE_CAP",
        module: "crates/axeyum-solver/src/quant_negated_exists_cert.rs",
        value: "4_096",
        unit: "distinct existential-body nodes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the source checker's admission walk declines (returns `None`), rejecting only this ADR-0126 negated-existential witness route",
        env_override: Some("AXEYUM_NEGATED_EXISTENTIAL_NODE_CAP"),
        justification: undated("doc comment"),
        note: "Node-count sibling to NEGATED_EXISTENTIAL_BINDER_CAP.",
    },
    ConfigEntry {
        name: "QUANTIFIED_UF_BINDER_CAP",
        module: "crates/axeyum-solver/src/quant_uf_model_sat_cert.rs",
        value: "16",
        unit: "binders in one checked universal prefix",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the checker declines past this cap; module doc: \"Unsupported shapes decline rather than sampling an infinite domain\" -- MBQI search is untrusted, only this checker's acceptance counts",
        env_override: Some("AXEYUM_QUANTIFIED_UF_BINDER_CAP"),
        justification: undated("doc comment"),
        note: "Admission cap on the checked finite-profile model checker for the almost-uninterpreted quantified fragment.",
    },
    ConfigEntry {
        name: "QUANTIFIED_UF_PROFILE_CAP",
        module: "crates/axeyum-solver/src/quant_uf_model_sat_cert.rs",
        value: "4096",
        unit: "finite-profile tuples checked per universal prefix",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the checker declines when this budget is exhausted mid-walk; module doc: \"Unsupported shapes decline rather than sampling an infinite domain\"",
        env_override: None,
        justification: undated("doc comment"),
        note: "Also used as a live decrementing budget (`let mut budget = QUANTIFIED_UF_PROFILE_CAP`, quant_uf_model_sat_cert.rs:224), not only a static admission threshold.",
    },
    ConfigEntry {
        name: "VACUOUS_EXISTS_COUNTEREXAMPLE_BINDER_CAP",
        module: "crates/axeyum-solver/src/quant_vacuous_exists_counterexample_cert.rs",
        value: "128",
        unit: "total binders",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the source checker's admission walk declines, rejecting only this ADR-0128 vacuous-existential counterexample route",
        env_override: Some("AXEYUM_VACUOUS_EXISTS_COUNTEREXAMPLE_BINDER_CAP"),
        justification: undated("doc comment"),
        note: "Admission cap on one checked counterexample below syntactically vacuous leading existential binders.",
    },
    ConfigEntry {
        name: "VACUOUS_EXISTS_COUNTEREXAMPLE_NODE_CAP",
        module: "crates/axeyum-solver/src/quant_vacuous_exists_counterexample_cert.rs",
        value: "4_096",
        unit: "distinct source nodes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the source checker's admission walk declines, rejecting only this ADR-0128 vacuous-existential counterexample route",
        env_override: Some("AXEYUM_VACUOUS_EXISTS_COUNTEREXAMPLE_NODE_CAP"),
        justification: undated("doc comment"),
        note: "Node-count sibling to VACUOUS_EXISTS_COUNTEREXAMPLE_BINDER_CAP.",
    },
    ConfigEntry {
        name: "RECON_ALPHABET_CAP",
        module: "crates/axeyum-solver/src/regex_reconstruct.rs",
        value: "96",
        unit: "representative alphabet size",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_RECON_ALPHABET_CAP"),
        justification: undated("doc comment"),
        note: "Caps the Lean kernel-module reconstruction of a regex-emptiness refutation, NOT the underlying verdict - the doc states plainly \"the certificate itself is unaffected\": this only decides whether a checkable proof artifact is produced.",
    },
    ConfigEntry {
        name: "RECON_MAX_STATES",
        module: "crates/axeyum-solver/src/regex_reconstruct.rs",
        value: "4_096",
        unit: "canonical residual states",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_RECON_MAX_STATES"),
        justification: undated("doc comment"),
        note: "The re-established emptiness-closure cap; `pub` because it is also referenced from the module's own top doc. Same verdict-is-unaffected-only-the-proof-artifact caveat as `RECON_STATE_CAP`/`RECON_ALPHABET_CAP`.",
    },
    ConfigEntry {
        name: "RECON_STATE_CAP",
        module: "crates/axeyum-solver/src/regex_reconstruct.rs",
        value: "96",
        unit: "automaton states (Q constructors)",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_RECON_STATE_CAP"),
        justification: undated("doc comment"),
        note: "Further caps the (already `RECON_MAX_STATES`-bounded) closure before rendering it into a kernel module, since the emitted n x m transition table would otherwise be unwieldy.",
    },
    ConfigEntry {
        name: "ABSOLUTE_CLAUSE_CEILING",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "64_000_000",
        unit: "estimated bit-blasted CNF clauses",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("no written justification"),
        note: "Default projected clause ceiling when `config.cnf_clause_budget` is unset; overridden by that field when the caller sets one. `estimate_blast_clauses` over-estimates pre-lowering, and exceeding the cap returns `CheckResult::Unknown { kind: UnknownKind::EncodingBudget, .. }` (\"oversized encoding refused gracefully\") before `lower_terms` allocates. No measurement or ADR is cited at the definition site.",
    },
    ConfigEntry {
        name: "BVE_BUDGET_SETUP_MULTIPLE",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "2_000",
        unit: "multiple of BVE's own occurrence-list setup cost",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "eliminate_variables_within truncates between variables and the partial result stays sound (equisatisfiable with a valid reconstruction), so an interrupted pass never produces a wrong verdict, only less clause reduction",
        env_override: Some("AXEYUM_BVE_BUDGET_MULTIPLE"),
        justification: dated(
            "doc comment",
            "2026-09-08",
            Some("abb6f80da"),
            &[sym(
                "crates/axeyum-solver/src/sat_bv_backend.rs",
                "BVE_BUDGET_SETUP_MULTIPLE",
            )],
            &[
                doc("docs/research/03-measurements/inprocessing-admission-2026-09-08.md"),
                commit("abb6f80da", "admit BVE through the shared budget primitive"),
            ],
        ),
        note: "Measured over the pinned 200-file QF_BV parity list: BVE's own work spans five orders of magnitude in units of its own setup cost (median 474x, p90 12,723x, max 39,654x), so \"there is no multiple that is simultaneously generous to every file and frugal with any of them\" -- 2000 was chosen as a trade, not a natural threshold. `AXEYUM_BVE_BUDGET_MULTIPLE` exists only to run an unbudgeted A/B arm against one binary.",
    },
    ConfigEntry {
        name: "BVE_MIN_RECOVERY_MULTIPLE",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "2",
        unit: "multiple of setup cost the remaining budget must be able to recover",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "skipping BVE/subsumption entirely when the gate refuses leaves the formula unchanged, which is trivially sound",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-09-08",
            Some("67fe79cb8"),
            &[sym(
                "crates/axeyum-solver/src/sat_bv_backend.rs",
                "BVE_MIN_RECOVERY_MULTIPLE",
            )],
            &[
                doc(
                    "docs/research/02-ecosystems/inprocessing-scheduling-2026-09/cadical-kissat-budget-model.md",
                ),
                commit("67fe79cb8", "record where the last elimination happened"),
            ],
        ),
        note: "Arms the accumulate-and-delay gate (`axeyum_ir::budget::EffortPolicy::with_init_cost`) with CaDiCaL's pre-search rule: do not start a pass whose fixed setup cost the available budget cannot recover twice over. Also used (same value) as `min_recovery_multiple` for the subsumption admission below -- one constant, two passes.",
    },
    ConfigEntry {
        name: "BVE_STEPS_PER_MILLISECOND",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "400_000",
        unit: "occurrence-list steps per millisecond",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "getting the conversion wrong is explicitly documented as safe in both directions: too high truncates via the wall deadline as it already would, too low stops the pass early with a still-equisatisfiable partial result",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-09-08",
            Some("abb6f80da"),
            &[sym(
                "crates/axeyum-solver/src/sat_bv_backend.rs",
                "BVE_STEPS_PER_MILLISECOND",
            )],
            &[
                doc("docs/research/03-measurements/inprocessing-admission-2026-09-08.md"),
                commit("abb6f80da", "admit BVE through the shared budget primitive"),
            ],
        ),
        note: "The one host-dependent number in the admission decision, confined to converting a wall-clock slice into the budget's step unit; unread with no deadline. Measured `bve_work_spent / bve_ms` over 97 parity files: p10 170,671, median 460,365, p90 1,326,285 -- 400,000 sits just under the median.",
    },
    ConfigEntry {
        name: "INPROCESS_MAX_CLAUSES",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "16_000_000",
        unit: "clauses",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Unlinked mirror of `axeyum-cnf/src/inprocess.rs`'s registered `DEFAULT_MAX_CLAUSES` -- same value 16_000_000, same role, no code link between the two. `formula.clauses().len() > INPROCESS_MAX_CLAUSES` records `cnf_inprocessing_skipped_size` and skips the pass (the SAT solve still runs on the un-inprocessed CNF).",
    },
    ConfigEntry {
        name: "INPROCESS_MAX_VARIABLES",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "4_000_000",
        unit: "CNF variables",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "CONFIRMED: this is the unlinked mirror the existing `axeyum-cnf/src/inprocess.rs::DEFAULT_MAX_VARIABLES` registry entry's note already names (\"Mirrors `sat_bv_backend`'s `INPROCESS_MAX_VARIABLES`; the two are not linked in code\") -- same value 4_000_000, same role (occurrence lists must fit one pass), no shared symbol. `formula.variable_count() > INPROCESS_MAX_VARIABLES` records `cnf_inprocessing_skipped_size` and skips inprocessing.",
    },
    ConfigEntry {
        name: "MAX_LINKED_PROOF_STEPS",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "8_000_000",
        unit: "DRAT steps (reduction prefix + search)",
        protects: Protects::Memory,
        on_exceed: OnExceed::Truncate,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "docs/research/03-measurements/inprocessed-unsat-proof-coverage-2026-09-08.md",
            "2026-09-08",
            None,
            &[sym(
                "crates/axeyum-cnf/src/reduction_link.rs",
                "fn check_unsat",
            )],
            &[doc(
                "docs/research/03-measurements/inprocessed-unsat-proof-coverage-2026-09-08.md",
            )],
        ),
        note: "Crossing it does NOT refuse: `ReductionLink::check_unsat` falls back to `check_reduced`, so the `unsat` is still checked -- against the REDUCED formula rather than the original, and the caller is told which (`ProofCoverage::Reduced(ReducedReason::OverBudget { steps, budget })`, surfaced as \"the reduced formula\" in the failure detail). So the bound weakens what the certificate is ABOUT, and it says so; that is why this is `Truncate`/`ToCaller` and not `RefuseUnknown`. The measurement is the reason it is worth registering: over the 200-file QF_BV parity list the prefix was a median of 658 steps, p90 71,881 and a maximum of 1,971,102, so the cap clears the worst observed instance by 4.06x -- NOT the orders of magnitude its size suggests. Its own doc says a larger corpus can be expected to cross it, and that the intended response is to wire the streaming route rather than raise the constant.",
    },
    ConfigEntry {
        name: "MAX_SHARED_GUARD_SPLIT_BRANCHES",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "16",
        unit: "disjunction branches",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "splitting `or(not(A => C_i))` into independent branch queries is denotation-preserving by construction (sat iff some branch sat, unsat iff all branches unsat), so declining the split for a branch count outside this window only changes which route decides the query, never the verdict",
        env_override: None,
        justification: undated("no written justification"),
        note: "Ceiling on `shared_guard_split_branches`'s recognized branch count; above it the split is declined and the disjunction is solved un-split. Caps how many independent per-branch SAT calls one split can spawn.",
    },
    ConfigEntry {
        name: "MIN_SHARED_GUARD_SPLIT_BRANCHES",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "4",
        unit: "disjunction branches",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "same denotation-preserving invariant as MAX_SHARED_GUARD_SPLIT_BRANCHES",
        env_override: None,
        justification: undated("no written justification"),
        note: "Floor on recognized branch count; below it splitting overhead is not worth paying and the disjunction is solved un-split.",
    },
    ConfigEntry {
        name: "MIN_SHARED_GUARD_SPLIT_DAG_NODES",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "5_000",
        unit: "shared term-DAG nodes in the single assertion",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "same denotation-preserving invariant as MAX_SHARED_GUARD_SPLIT_BRANCHES -- declining the split changes only which route decides the query",
        env_override: None,
        justification: undated("no written justification"),
        note: "`dag_nodes < MIN_SHARED_GUARD_SPLIT_DAG_NODES` declines the shared-guard split attempt on small formulas where the recognition overhead is not worth it.",
    },
    ConfigEntry {
        name: "SUBSUME_BUDGET_SETUP_MULTIPLE",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "50",
        unit: "multiple of subsumption's own occurrence-list setup cost",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "subsumption only deletes clauses, so an interrupted pass leaves a still model-preserving formula whatever is skipped",
        env_override: Some("AXEYUM_SUBSUME_BUDGET_MULTIPLE"),
        justification: dated(
            "doc comment",
            "2026-09-08",
            Some("7c775415b"),
            &[sym(
                "crates/axeyum-solver/src/sat_bv_backend.rs",
                "SUBSUME_BUDGET_SETUP_MULTIPLE",
            )],
            &[
                doc("docs/research/03-measurements/subsumption-work-meter-2026-09-08.md"),
                commit("7c775415b", "subsumption's budget recovers div3.c.50"),
            ],
        ),
        note: "A DIFFERENT kind of decision from BVE_BUDGET_SETUP_MULTIPLE per its own doc comment: subsumption's post-last-useful-action waste is only 1.5-2.2% (vs BVE's 22.9%), so every second this saves is bought against real subsumptions, not waste. K=50 recovers `div3.c.50`, a file the ungated arm lost; K=100 was measured WORSE than doing nothing on PAR-2. Read the doc comment's own caveat before trusting the ranking between adjacent K values.",
    },
    ConfigEntry {
        name: "SUBSUME_STEPS_PER_MILLISECOND",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "128_000",
        unit: "occurrence-list steps per millisecond",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "getting the conversion wrong is documented as safe in both directions: too high truncates via the wall deadline as it already would, too low stops the pass early with a still model-preserving partial result",
        env_override: None,
        justification: dated(
            "doc comment",
            "2026-09-08",
            Some("2aa14615b"),
            &[sym(
                "crates/axeyum-solver/src/sat_bv_backend.rs",
                "SUBSUME_STEPS_PER_MILLISECOND",
            )],
            &[
                doc("docs/research/03-measurements/subsumption-work-meter-2026-09-08.md"),
                commit(
                    "2aa14615b",
                    "register the four suites that control this lane's guards",
                ),
            ],
        ),
        note: "Deliberately separate from BVE_STEPS_PER_MILLISECOND: \"the measurement says they differ by 3.6x\" (subsumption's median 127,599-172,489 vs BVE's 460,365) -- \"a shared constant would have assumed\" the opposite direction. The one host-dependent number in the decision; unread with no deadline.",
    },
    ConfigEntry {
        name: "XOR_CDCL_FALLBACK_MAX_CLAUSES",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "50_000",
        unit: "clauses",
        protects: Protects::Termination,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"CDCL(XOR) search-fallback admission bound (ADR-0035). `solve_with_xor_cdcl` is conflict-budgeted but carries no wall-clock budget\" -- so this clause-count gate is the only thing preventing an unbounded run on a huge CNF. `formula.clauses().len() > XOR_CDCL_FALLBACK_MAX_CLAUSES` records `xor_cdcl_fallback_skipped_size` and returns the original result.",
    },
    ConfigEntry {
        name: "XOR_PROPAGATE_MAX_CLAUSES",
        module: "crates/axeyum-solver/src/sat_bv_backend.rs",
        value: "20_000",
        unit: "clauses",
        protects: Protects::Termination,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"`xor_propagate` runs Gaussian elimination over the recovered XOR system, which is O(gates^2 x vars) and currently carries no internal deadline.\" Gated by clause count as the only current bound; doc says \"raised once the pass is deadline-bounded.\" Above the cap `formula.clauses().len() <= XOR_PROPAGATE_MAX_CLAUSES` is false, `xor_propagate` is skipped, and `xor_propagate_skipped_size` is recorded in `stats.backend`.",
    },
    ConfigEntry {
        name: "MAX_PIVOTS",
        module: "crates/axeyum-solver/src/simplex.rs",
        value: "2_000_000",
        unit: "pivot operations",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::None,
        guarded_by: "`RunOutcome::Unknown` is a permitted verdict at every consumer; a truncated pivot sequence yields no sat/unsat claim at all",
        env_override: None,
        justification: undated("doc comment"),
        note: "Bland's rule already guarantees termination; this is the deterministic belt for a run with no wall-clock deadline.",
    },
    ConfigEntry {
        name: "MAX_TABLEAU_CELLS",
        module: "crates/axeyum-solver/src/simplex.rs",
        value: "4_000_000",
        unit: "tableau cells (rows x columns)",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "docs/research/12-performance/ladder-budget-discipline-2026-09-08.md",
            "2026-09-08",
            None,
            &[
                sym("crates/axeyum-solver/src/simplex.rs", "MAX_TABLEAU_CELLS"),
                sym("crates/axeyum-solver/src/lra.rs", "simplex_admission"),
                sym("crates/axeyum-solver/src/lra.rs", "simplex_fallback"),
            ],
            // The measurement is about the OTHER constructor: it says what a
            // cell bound in `feasible` would refuse. It rests on
            // `simplex_admission` still being the gate that runs first on that
            // route, because that gate is why the unbounded constructor is not
            // the catastrophe the 360-million-cell reading suggests.
            &[
                live("simplex_admission", "crates/axeyum-solver/src/lra.rs"),
                doc("docs/research/12-performance/ladder-budget-discipline-2026-09-08.md"),
            ],
        ),
        note: "About 128 MB at two `i128`s per cell. `Incremental::new` returns `None`, so the caller falls back to Fourier-Motzkin. Deterministic (no clock, no resident-set probe), which is what lets it be part of a reproducible verdict. THE GAP `lra_online::BYTES_PER_ADMITTED_ATOM`'s note reports -- this bound is checked ONLY in `Incremental::new`, while `feasible` (what `lra::simplex_fallback` calls) consults no cell bound at all -- was MEASURED on 2026-09-08 over the committed 200-file QF_LRA list, 24 s and 8 GiB per file, with the instrumented binary named in the doc. 36 files reach `simplex_fallback` at all (3,129 calls); SEVEN build a tableau over this cap, at 4.2 to 8.8 million cells, and all seven end `unknown`. So adding the check here would refuse a population that decides nothing today -- and would buy nothing either, since nothing runs after `lra` on those files. NOT ADDED, and the reason is the second half of the measurement: the largest tableau observed is 8.8 M cells (282 MB), 30x smaller than the 360 M the earlier reading found, because `lra::simplex_admission` (2026-09-08) now prices that allocation against `memory_limit_mb` BEFORE `feasible` is called. At 8 GiB that gate admits 268 M cells, so the two bounds on one allocation differ by 67x in opposite units -- a fixed cell count and a memory budget. The residual unguarded caller is one that sets NO memory limit; a fixed 4 M cap is the wrong instrument for it, and choosing the right one needs its own ADR rather than a line here.",
    },
    ConfigEntry {
        name: "DEFAULT_STRING_BOUND",
        module: "crates/axeyum-solver/src/smtlib.rs",
        value: "12",
        unit: "bytes",
        protects: Protects::Completeness,
        on_exceed: OnExceed::Relax,
        signal: Signal::None,
        guarded_by: "\"the clamp inside that function keeps a drifted value sound (it can only widen)\" - the doc's own safety argument for why a stale local copy cannot become unsound, only inefficient",
        env_override: None,
        justification: undated("doc comment"),
        note: "DIVERGENT TWIN, self-documented: \"axeyum_smtlib's STRING_MAX_LEN ... [n]amed here (rather than re-exported) because the solver only needs it as the ladder's first rung.\" A third named copy of the same underlying value as `axeyum-smtlib/src/parse.rs::STRING_MAX_LEN` and `bounded_completeness.rs::STRING_MAX_LEN`.",
    },
    ConfigEntry {
        name: "MEMBERSHIP_MAX_LIFTED_WITNESS_LEN",
        module: "crates/axeyum-solver/src/smtlib.rs",
        value: "4_000_000",
        unit: "witness elements",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("no written justification"),
        note: "Caps the `Vec` materialized while lifting a checked regex-membership witness through an existential concatenation definition; `CheckResult::Unknown` with an explicit detail string names both the actual and the capped length.",
    },
    ConfigEntry {
        name: "MEMBERSHIP_MAX_STATES",
        module: "crates/axeyum-solver/src/smtlib.rs",
        value: "60_000",
        unit: "distinct canonical residuals",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "DIVERGENT TWIN: `axeyum-solver/src/string_theory.rs::MEMBERSHIP_MAX_STATES` is the SAME NAME with a DIFFERENT VALUE (20_000) governing what reads as the same kind of resource (regex-membership derivative-closure states) in a sibling module of the same crate - exactly the two-gates-on-one-resource pattern this registry's own module doc calls out for `MAX_ONLINE_LRA_ATOMS`. Paired with the config-derived deadline so an intractable regex is a fast `unknown`.",
    },
    ConfigEntry {
        name: "MIN_RUNG_BUDGET",
        module: "crates/axeyum-solver/src/smtlib.rs",
        value: "std::time::Duration::from_millis(250)",
        unit: "milliseconds",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "a rung skipped for insufficient remaining budget just returns the `solved` result already in hand unchanged; per the surrounding comment, a rung that errors is not a failure of the query since the original Unknown is kept and the next rung tried - the same reasoning applies to a rung never attempted",
        env_override: None,
        justification: undated("doc comment"),
        note: "Least remaining wall-clock budget worth entering another `STRING_BOUND_LADDER` rung with, since a near-zero start still pays a full re-parse/re-encode and \"the interior routes only sample their deadline at coarse points\".",
    },
    ConfigEntry {
        name: "SOURCE_WITNESS_MAX_ALPHABET",
        module: "crates/axeyum-solver/src/smtlib.rs",
        value: "4",
        unit: "distinct source-derived characters",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the bounded source-witness probe is SAT-only and independently replay-gated; per `apply_source_string_sat_problem`'s own doc, exhausting any of its three step caps just \"preserve[s] the prior `unknown`\" - never fabricates a `sat`",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"A larger alphabet would make the length-four Cartesian product dominate the bounded probe; the assignment cap remains the final guard.\"",
    },
    ConfigEntry {
        name: "SOURCE_WITNESS_MAX_ASSIGNMENTS",
        module: "crates/axeyum-solver/src/smtlib.rs",
        value: "20_000",
        unit: "concrete assignments tried",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "same SAT-only/replay-gated invariant as `SOURCE_WITNESS_MAX_ALPHABET`: exhausting the cap \"leaves the existing `unknown` untouched\"",
        env_override: None,
        justification: undated("doc comment"),
        note: "Deterministic step cap on the bounded source-witness probe over the small alphabet product.",
    },
    ConfigEntry {
        name: "SOURCE_WITNESS_MAX_WORD_LEN",
        module: "crates/axeyum-solver/src/smtlib.rs",
        value: "4",
        unit: "generated word length",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "same SAT-only/replay-gated invariant as `SOURCE_WITNESS_MAX_ALPHABET`",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"Explicit source literals are retained even when longer; this cap applies only to the small alphabet product used to discover counterexamples.\"",
    },
    ConfigEntry {
        name: "WORD_INT_COUPLE_MAX_CANDIDATES",
        module: "crates/axeyum-solver/src/smtlib.rs",
        value: "128",
        unit: "candidate integers tried",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the `str.from_int`-coupled word-problem route only ever attempts to upgrade an already-`Unknown` result to a replay-checked `Sat`; a witness must lie within this many integers of the range's lower bound, anything further stays a sound `unknown` per the doc",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"Sized to decide the small-integer-witness class (the cvc5 regress shapes need a two- or three-digit integer)\" - a measured-shape justification without a date or commit, so kept undated rather than guessed.",
    },
    ConfigEntry {
        name: "WORD_INT_COUPLE_MAX_NODES_PER_CANDIDATE",
        module: "crates/axeyum-solver/src/smtlib.rs",
        value: "2_000",
        unit: "branch nodes",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "applied via `.min(` (`b.max_nodes = b.max_nodes.min(WORD_INT_COUPLE_MAX_NODES_PER_CANDIDATE)`), so a per-candidate search that would have run longer simply gets less budget and may itself decline that one candidate; anything further stays a sound `unknown` per the sibling constant's doc",
        env_override: None,
        justification: undated("doc comment"),
        note: "\"So one pathological pin cannot monopolize the wall-clock budget.\"",
    },
    ConfigEntry {
        name: "WORD_ROUTE_MAX_NODES",
        module: "crates/axeyum-solver/src/smtlib.rs",
        value: "200_000",
        unit: "branch nodes",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "DIVERGENT-NAME TWIN: `axeyum-solver/src/string_theory.rs::WORD_MAX_NODES` is explicitly documented there as mirroring `smtlib::WORD_ROUTE_MAX_NODES` - same value (200_000), different name, in a sibling module of the same crate. The sole termination guard for the word-equation route (ADR-0053, T-B.4b) when no deadline is set (always true on `wasm32`).",
    },
    ConfigEntry {
        name: "MAX_FM_ROWS",
        module: "crates/axeyum-solver/src/string_length_cert.rs",
        value: "256",
        unit: "Fourier-Motzkin inequalities",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "returning `None` from the Fourier-Motzkin elimination stage only declines this optional length-certificate proof strategy; the ordinary bounded/bit-blast route remains sound and complete for the query independently",
        env_override: None,
        justification: undated("no written justification"),
        note: "No doc comment on the const itself (\"Refuse a Fourier-Motzkin stage with more than this many inequalities\" is the entire comment, giving no reasoning for the value 256).",
    },
    ConfigEntry {
        name: "MAX_SOURCE_NODES",
        module: "crates/axeyum-solver/src/string_length_cert.rs",
        value: "4096",
        unit: "s-expression nodes",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`read_source` returning `None` above this size only declines the whole length-to-LIA certificate route for that script; per the doc, the abstraction declines on any unsupported operator anyway and this is only the belt on the certificate's own size - the underlying verdict is decided by another route",
        env_override: None,
        justification: undated("doc comment"),
        note: "",
    },
    ConfigEntry {
        name: "CONCAT_WITNESS_MAX_LEN",
        module: "crates/axeyum-solver/src/string_theory.rs",
        value: "512",
        unit: "witness length",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "an abandoned/failed witness search for a concat operand's shape only means this particular derivative-based witness shortcut misses a witness; other theory-solver channels (e.g. the mandatory sat replay) remain the source of truth",
        env_override: None,
        justification: undated("doc comment"),
        note: "Paired with `CONCAT_WITNESS_MAX_STATES` in the single call `problem.witness(budget, CONCAT_WITNESS_MAX_STATES, CONCAT_WITNESS_MAX_LEN)`.",
    },
    ConfigEntry {
        name: "CONCAT_WITNESS_MAX_STATES",
        module: "crates/axeyum-solver/src/string_theory.rs",
        value: "4_000",
        unit: "derivative-residual states",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "same reasoning as `CONCAT_WITNESS_MAX_LEN`",
        env_override: None,
        justification: undated("doc comment"),
        note: "Smaller than `MEMBERSHIP_MAX_STATES` (this file) because the shape's `Sigma*` runs enlarge the closure and the emptiness pass does not poll the deadline, so a tight cap keeps a pathological concat regex a fast `Unknown`.",
    },
    ConfigEntry {
        name: "LENGTH_SAT_MAX_LEN",
        module: "crates/axeyum-solver/src/string_theory.rs",
        value: "20_000",
        unit: "string length",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_LENGTH_SAT_MAX_LEN"),
        justification: undated("doc comment"),
        note: "`CheckResult::Unknown` when a solved length-to-LIA model's length falls outside `0..=LENGTH_SAT_MAX_LEN`. \"Exceeding the cap declines to `Unknown` - never a wrong verdict, since the cap only misses a witness\" per the doc.",
    },
    ConfigEntry {
        name: "MEMBERSHIP_MAX_STATES",
        module: "crates/axeyum-solver/src/string_theory.rs",
        value: "20_000",
        unit: "distinct canonical residuals",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "`!problem.refute_empty_within(...)` just `continue`s past this class without registering a theory conflict; per the surrounding comment, an abandoned closure just misses this conflict and is safe because it is caught later by the mandatory sat replay",
        env_override: None,
        justification: undated("doc comment"),
        note: "DIVERGENT TWIN: see `axeyum-solver/src/smtlib.rs::MEMBERSHIP_MAX_STATES` (same name, value 60_000 there vs 20_000 here) - flagged in detail on that entry. This module's copy governs the per-assert CDCL-loop theory-conflict search specifically; also note a nearby BARE literal `256` at the `quick_witness(&self.budget, 256)` call one line above the first use site (see bare-literals.md).",
    },
    ConfigEntry {
        name: "WORD_MAX_NODES",
        module: "crates/axeyum-solver/src/string_theory.rs",
        value: "200_000",
        unit: "branch nodes",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "DIVERGENT-NAME TWIN of `axeyum-solver/src/smtlib.rs::WORD_ROUTE_MAX_NODES` (same value, explicitly documented here as mirroring it). The branch-node budget for the per-assert refuter and the final word search; sole guard when no deadline is set (and always on `wasm32`).",
    },
    ConfigEntry {
        name: "MAX_DOMAIN_SIZE",
        module: "crates/axeyum-solver/src/uf_fmf.rs",
        value: "8",
        unit: "per-sort carrier cardinality",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the deepening loop `for step in 1..=MAX_DOMAIN_SIZE` simply stops; module doc: \"a query whose models are all infinite simply never certifies here and keeps the caller's `unknown`\" -- soundness rests on the independent checker, not on this search",
        env_override: Some("AXEYUM_MAX_DOMAIN_SIZE"),
        justification: undated("doc comment"),
        note: "Doc comment: \"The cvc5 finite-model-find probe over the public UF parity slice tops out at per-sort cardinality 5; 8 leaves margin without inviting blowup\" -- a real comparison, but no date is given.",
    },
    ConfigEntry {
        name: "MAX_EXPANSION_BACKOFFS",
        module: "crates/axeyum-solver/src/uf_fmf.rs",
        value: "512",
        unit: "bound-lowering retries per deepening step",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "once retries are exhausted the deepening step gives up on that bound; the search declines rather than emitting an unchecked model",
        env_override: None,
        justification: undated("doc comment"),
        note: "Each retry runs only the cheap cost estimator (no term building), so the descent stays fast even on files with hundreds of sorts (doc comment).",
    },
    ConfigEntry {
        name: "MAX_GROUND_INSTANCES",
        module: "crates/axeyum-solver/src/uf_fmf.rs",
        value: "64_000",
        unit: "ground-instance work-budget units",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "exceeding it triggers the per-sort backoff descent (a smaller expansion is tried instead); once every bound is at its floor the deepening loop stops and this module declines rather than emitting an unchecked model",
        env_override: None,
        justification: undated("doc comment"),
        note: "Ground-instance work budget for one expansion build (instantiations, closure axioms, table entries, functionality lemmas, selector-leaf visits).",
    },
    ConfigEntry {
        name: "MAX_SOURCE_DAG_NODES",
        module: "crates/axeyum-solver/src/uf_fmf.rs",
        value: "100_000",
        unit: "source DAG nodes",
        protects: Protects::Time,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the source formula is refused before any work begins; module doc: \"the expander is DAG-linear per instantiation, so a huge source formula is refused before any work\"",
        env_override: None,
        justification: undated("doc comment"),
        note: "Pre-search admission bound on total input size.",
    },
    ConfigEntry {
        name: "UF_FMF_FULL_SOLVE_ASSERTIONS",
        module: "crates/axeyum-solver/src/uf_fmf.rs",
        value: "usize::MAX",
        unit: "assertions handed to the post-refutation solve",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "shares the mechanism with UF_FMF_PROBE_SOLVE_ASSERTIONS but is deliberately set so the cap can never fire",
        env_override: None,
        justification: undated("doc comment"),
        note: "Currently a documented no-op (`usize::MAX`): everything reaching this call has already ended in `unknown`, so a large round costs nothing but its own chance of success, bounded by MAX_GROUND_INSTANCES and the shared deadline (doc comment). Registered because it shares the same comparison site as UF_FMF_PROBE_SOLVE_ASSERTIONS and lowering it would start imposing a limit.",
    },
    ConfigEntry {
        name: "UF_FMF_PROBE_SOLVE_ASSERTIONS",
        module: "crates/axeyum-solver/src/uf_fmf.rs",
        value: "2_000",
        unit: "assertions handed to the pre-refutation probe SAT solve",
        protects: Protects::Time,
        on_exceed: OnExceed::Truncate,
        signal: Signal::None,
        guarded_by: "an over-cap build triggers the same per-sort backoff descent as an over-budget MAX_GROUND_INSTANCES build (doc comment)",
        env_override: None,
        justification: undated("doc comment"),
        note: "Doc comment: every model certified on the UF parity slice came from a sub-1k-assertion build, while 30k+-assertion rounds produced only slow unknowns whose non-preemptible blasts starved the refutation family on declared-unsat files -- a real measurement, but no date is given.",
    },
    ConfigEntry {
        name: "BOOL_UF_EXHAUSTIVE_MAX_BITS",
        module: "crates/axeyum-solver/src/ufbv_finite.rs",
        value: "12",
        unit: "argument-domain bits",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "the pigeonhole check declines past this bit width; the query remains available to the pure-EUF fast path and the BV backend (module doc)",
        env_override: Some("AXEYUM_BOOL_UF_EXHAUSTIVE_MAX_BITS"),
        justification: undated("doc comment"),
        note: "Bounds a finite-domain pigeonhole refutation over a Bool/BV argument domain (2^bits exhaustive risk).",
    },
    ConfigEntry {
        name: "MAX_ARRAY_ITE_EQUALITY_DEPTH",
        module: "crates/axeyum-solver/src/ufbv_online.rs",
        value: "256",
        unit: "nested array-ITE layers",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`build_unknown` detail names this cap: \"array-ITE equality expansion exceeds depth {MAX_ARRAY_ITE_EQUALITY_DEPTH}\" (ufbv_online.rs:1797-1803).",
    },
    ConfigEntry {
        name: "MAX_ARRAY_ITE_EQUALITY_LEAVES",
        module: "crates/axeyum-solver/src/ufbv_online.rs",
        value: "256",
        unit: "leaf equalities from array-ITE decomposition",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`build_unknown` detail names this cap: \"array-ITE equality expansion exceeds {MAX_ARRAY_ITE_EQUALITY_LEAVES} leaves\" (ufbv_online.rs:1850-1856).",
    },
    ConfigEntry {
        name: "MAX_BOOLEAN_CLAUSES",
        module: "crates/axeyum-solver/src/ufbv_online.rs",
        value: "32_768",
        unit: "Boolean clauses after Tseitin encoding",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Static pre-check (ufbv_online.rs:2937-2941) and two dynamic in-search checks (ufbv_online.rs:1432-1543) all build `build_unknown` naming this cap.",
    },
    ConfigEntry {
        name: "MAX_BOOLEAN_VARIABLES",
        module: "crates/axeyum-solver/src/ufbv_online.rs",
        value: "8_192",
        unit: "Boolean variables after Tseitin encoding",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Static pre-check (ufbv_online.rs:2944-2949) and a dynamic in-search check (ufbv_online.rs:853-858) both build `build_unknown(UnknownKind::ResourceLimit, ...)` naming this cap.",
    },
    ConfigEntry {
        name: "MAX_BV_PROPAGATION_INTERFACE_ATOMS",
        module: "crates/axeyum-solver/src/ufbv_online.rs",
        value: "64",
        unit: "candidate interface atoms eligible for exact BV propagation",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`refresh_propagation` simply returns early past this cap (ufbv_online.rs:684-697), skipping only the exact one-candidate-per-state BV propagation accelerator; the canonical CDCL(T) search is unaffected.",
    },
    ConfigEntry {
        name: "MAX_BV_PROPAGATION_PROBES",
        module: "crates/axeyum-solver/src/ufbv_online.rs",
        value: "128",
        unit: "accumulated implication probes",
        protects: Protects::Time,
        on_exceed: OnExceed::SearchEvent,
        signal: Signal::NotApplicable,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Sibling cap to MAX_BV_PROPAGATION_INTERFACE_ATOMS in the same early-return guard (ufbv_online.rs:684-697).",
    },
    ConfigEntry {
        name: "MAX_INPUT_DAG_NODES",
        module: "crates/axeyum-solver/src/ufbv_online.rs",
        value: "16_384",
        unit: "input DAG nodes",
        protects: Protects::Memory,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: dated(
            "docs/research/12-performance/qf-abv-route-attribution-2026-09-08.md",
            "2026-09-08",
            Some("f24c61f91"),
            &[sym(
                "crates/axeyum-solver/src/ufbv_online.rs",
                "MAX_INPUT_DAG_NODES",
            )],
            &[doc(
                "docs/research/12-performance/qf-abv-route-attribution-2026-09-08.md",
            )],
        ),
        note: "Admits `abv-online-cdclt`, the FIRST route every array query tries. Declined `2018-Mann/arbiter_array_cex_w32d32q16n4b34.smt2` at 32,695 nodes on 2026-09-08. Registered because that route is the entry point for a whole division and had no registry presence at all; `crates/axeyum-solver/src/ufbv_online.rs` is still not in `GOVERNED_FILES`, so its other ~20 bounds remain unclaimed. The VALUE is unchanged and still rests on a doc comment.",
    },
    ConfigEntry {
        name: "MAX_INPUT_DEPTH",
        module: "crates/axeyum-solver/src/ufbv_online.rs",
        value: "4_096",
        unit: "recursive term depth",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`admit_input` returns `build_unknown(UnknownKind::ResourceLimit, \"...depth {} exceeds the recursive abstraction cap...\")` (ufbv_online.rs:1605-1611).",
    },
    ConfigEntry {
        name: "MAX_INTERFACE_ATOMS",
        module: "crates/axeyum-solver/src/ufbv_online.rs",
        value: "512",
        unit: "materialized interface equalities",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Checked at eight call sites (ufbv_online.rs:1208-2686); each builds a `build_unknown` naming this cap in the detail string, e.g. \"materialized interface equalities exceed the bounded cap of {MAX_INTERFACE_ATOMS}\".",
    },
    ConfigEntry {
        name: "MAX_INTERFACE_REFINEMENTS",
        module: "crates/axeyum-solver/src/ufbv_online.rs",
        value: "64",
        unit: "retained-search final checks / canonical rebuilds",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`build_unknown` detail names this cap directly, e.g. \"interface refinement exceeded {MAX_INTERFACE_REFINEMENTS} steps\" (ufbv_online.rs:1189-1195, 1474-1530).",
    },
    ConfigEntry {
        name: "MAX_THEORY_ATOMS",
        module: "crates/axeyum-solver/src/ufbv_online.rs",
        value: "1_024",
        unit: "semantic atoms (formula atoms plus generated interface equalities)",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Two sites: a static pre-check (`build_unknown(...\"has {} semantic atoms, exceeding the cap\"...)`, ufbv_online.rs:2167-2174) and a dynamic one during retained search (`\"dynamic theory atoms exceed the cap\"`, ufbv_online.rs:847-851).",
    },
    ConfigEntry {
        name: "MAX_INTERFACE_PAIRS",
        module: "crates/axeyum-solver/src/uflia_interface.rs",
        value: "64",
        unit: "proposed interface case-split pairs",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_UFLIA_INTERFACE_PAIRS"),
        justification: dated(
            "docs/research/12-performance/uflia-interface-caps-2026-09-08.md",
            "2026-09-08",
            None,
            &[
                sym(
                    "crates/axeyum-solver/src/uflia_online.rs",
                    "MAX_SPLIT_DEPTH",
                ),
                sym(
                    "crates/axeyum-solver/src/combined_theory_lia.rs",
                    "MAX_SPLIT_PAIRS",
                ),
            ],
            &[doc(
                "docs/research/12-performance/uflia-interface-caps-2026-09-08.md",
            )],
        ),
        note: "THE SHARED CEILING the two QF_UFLIA copies now read (`uflia_online::MAX_SPLIT_DEPTH` and `combined_theory_lia::MAX_SPLIT_PAIRS` are `= crate::uflia_interface::MAX_INTERFACE_PAIRS`), closing two of the four unlinked copies the registry recorded. The value is UNCHANGED at 64 and deliberately so: pairs are quadratic in the interface-term count, so a raise big enough to admit the losing population is the removal of a termination bound, not a raise. `AXEYUM_UFLIA_INTERFACE_PAIRS` selects the PROPOSAL POLICY (`all` / `care` / `care-truncate`), not the number; `care-truncate` answers the ceiling by keeping a bounded care-graph subset instead of declining, which is sound in both directions (sat is replay-gated, unsat is a relaxation refutation) and incomplete by construction.",
    },
    ConfigEntry {
        name: "MAX_BOOLEAN_ATOMS",
        module: "crates/axeyum-solver/src/uflia_online.rs",
        value: "8192",
        unit: "distinct theory atoms",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_UFLIA_MAX_BOOLEAN_ATOMS"),
        justification: dated(
            "docs/research/12-performance/uflia-interface-caps-2026-09-08.md",
            "2026-09-08",
            None,
            &[
                sym(
                    "crates/axeyum-solver/src/uflia_online.rs",
                    "MAX_BOOLEAN_ATOMS",
                ),
                sym(
                    "crates/axeyum-solver/src/uflia_online.rs",
                    "max_boolean_atoms",
                ),
            ],
            &[
                adr("ADR-1801"),
                doc("docs/research/12-performance/uflia-interface-caps-2026-09-08.md"),
            ],
        ),
        note: "RAISED 512 -> 8192 on 2026-09-08 (ADR-1801) against the committed 200-file QF_UFLIA list. At 512 this ceiling was the LAST thing 27 of the 50 files we lose reported, at atom counts of 595-2,972, each refused in 0.1-0.3 ms; raised, the route decides files at 595-1,442 atoms, decides none above that within 24 s (the deadline stops it, which is what the ceiling's own rationale asks for), gains ten files on the loss population and loses none, with zero disagreements against cvc5's committed verdicts. Effective value still read through `max_boolean_atoms()`, which the env var can only RAISE (`v.max(MAX_BOOLEAN_ATOMS)`), never lower. `uflra_online.rs::MAX_BOOLEAN_ATOMS` is the UFLRA sibling with the SAME name but a DIFFERENT value (48) and no env override — divergent twins, not duplicates, and NOT raised here because this lane did not measure that division.",
    },
    ConfigEntry {
        name: "MAX_BOOLEAN_CLAUSES",
        module: "crates/axeyum-solver/src/uflia_online.rs",
        value: "200_000",
        unit: "Tseitin clauses",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "'Hard ceiling on Tseitin clauses... above it the layer declines rather than build an unbounded encoding' (doc); two sites both call `decline(...)` -> `CheckResult::Unknown` (uflia_online.rs:1667, 1969). Byte-identical value and near-identical doc to `uflra_online.rs::MAX_BOOLEAN_CLAUSES`.",
    },
    ConfigEntry {
        name: "MAX_BOOLEAN_MODELS",
        module: "crates/axeyum-solver/src/uflia_online.rs",
        value: "100_000",
        unit: "propositional models enumerated",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "'Hard ceiling on the number of propositional models the Boolean DPLL(T) layer enumerates' (doc, byte-identical to `uflra_online.rs::MAX_BOOLEAN_MODELS`'s doc); checked at uflia_online.rs:2336 via `decline(...)`.",
    },
    ConfigEntry {
        name: "MAX_OPAQUE_BOOLEAN_ATOMS",
        module: "crates/axeyum-solver/src/uflia_online.rs",
        value: "128",
        unit: "distinct theory atoms (opaque Int-UF path)",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_UFLIA_MAX_OPAQUE_BOOLEAN_ATOMS"),
        justification: undated("doc comment"),
        note: "Doc: the opaque-app arithmetic abstraction 'is not yet deadline-aware during combined-state construction and theory assertion, so keep the online slice bounded.' Same env-raise-only pattern as MAX_BOOLEAN_ATOMS above (`v.max(MAX_OPAQUE_BOOLEAN_ATOMS)`). DELIBERATELY NOT RAISED with MAX_BOOLEAN_ATOMS on 2026-09-08: the isolation arm (general ceiling raised, this one left at 128) decides the SAME ten files, and `UfliaInterfaceCounters::opaque_atom_cap_declines` is 0 across every file in every arm of that measurement, so on the QF_UFLIA population this constant never fires. It guards the one place on this route where construction is not deadline-aware, so raising a bound that buys nothing measured would be a cost with no benefit.",
    },
    ConfigEntry {
        name: "MAX_SPLIT_DEPTH",
        module: "crates/axeyum-solver/src/uflia_online.rs",
        value: "crate::uflia_interface::MAX_INTERFACE_PAIRS",
        unit: "interface case-split recursion depth",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Effective value 64, through the alias. PARTLY CLOSED 2026-09-08: this constant is now `= crate::uflia_interface::MAX_INTERFACE_PAIRS`, as is `combined_theory_lia.rs::MAX_SPLIT_PAIRS`, so the two QF_UFLIA copies are one definition. The QF_UFLRA pair is untouched because this lane did not measure that division. ORIGINAL FINDING (four unlinked copies of one bound). Byte-identical doc comment AND value to `uflra_online.rs::MAX_SPLIT_DEPTH` ('Hard ceiling on interface case-split recursion depth (one level per shared pair). Above it the search declines to a graceful CheckResult::Unknown - never a wrong verdict.'). Also mirrored (per THEIR doc comments, not this one) by `combined_theory.rs::MAX_SPLIT_PAIRS` and `combined_theory_lia.rs::MAX_SPLIT_PAIRS` (both = 64). Four independent copies across four files, one intended meaning, no code-level link between any pair.",
    },
    ConfigEntry {
        name: "MAX_BOOLEAN_ATOMS",
        module: "crates/axeyum-solver/src/uflra_online.rs",
        value: "48",
        unit: "distinct theory atoms",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_UFLRA_MAX_BOOLEAN_ATOMS"),
        justification: undated("doc comment"),
        note: "FINDING: no env-override mechanism here, unlike `uflia_online.rs::MAX_BOOLEAN_ATOMS` (raised via `AXEYUM_UFLIA_MAX_BOOLEAN_ATOMS`) — same constant name, both files' doc comments describe the same role ('Hard ceiling on the number of distinct theory atoms in the Boolean skeleton'), but this UFLRA copy is 48 (not 512) and fixed at compile time with no override. Checked at 3 sites (uflra_online.rs:1259, 1448, 1580).",
    },
    ConfigEntry {
        name: "MAX_BOOLEAN_CLAUSES",
        module: "crates/axeyum-solver/src/uflra_online.rs",
        value: "200_000",
        unit: "Tseitin clauses",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Byte-identical doc and value to `uflia_online.rs::MAX_BOOLEAN_CLAUSES`; checked at uflra_online.rs:1315, 1591, both via `decline(...)`.",
    },
    ConfigEntry {
        name: "MAX_BOOLEAN_MODELS",
        module: "crates/axeyum-solver/src/uflra_online.rs",
        value: "100_000",
        unit: "propositional models enumerated",
        protects: Protects::Time,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Byte-identical doc and value to `uflia_online.rs::MAX_BOOLEAN_MODELS`; checked at uflra_online.rs:1966 via `decline(...)`.",
    },
    ConfigEntry {
        name: "MAX_SPLIT_DEPTH",
        module: "crates/axeyum-solver/src/uflra_online.rs",
        value: "64",
        unit: "interface case-split recursion depth",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "FINDING: byte-identical doc comment AND value to `uflia_online.rs::MAX_SPLIT_DEPTH` — see that entry's note for the full four-copy chain (this file, `uflia_online.rs`, `combined_theory.rs::MAX_SPLIT_PAIRS`, `combined_theory_lia.rs::MAX_SPLIT_PAIRS`). Checked at uflra_online.rs:249, 395.",
    },
];

/// The files this registry claims to cover **completely**.
///
/// Coverage is claimed per file rather than globally because a global claim
/// would be false the moment any crate grew a constant, and a check that is
/// always red is a check nobody reads. A file listed here must have every
/// constant `scripts/config_registry_scan.py` finds in it either registered in
/// [`REGISTRY`] or named in [`EXEMPT`]; a file not listed is not claimed, which
/// is a gap this module states rather than hides.
pub static GOVERNED_FILES: &[&str] = &[
    "crates/axeyum-cnf/src/cube.rs",
    "crates/axeyum-cnf/src/inprocess.rs",
    "crates/axeyum-cnf/src/simplify.rs",
    "crates/axeyum-egraph/src/lib.rs",
    "crates/axeyum-rewrite/src/arrays.rs",
    "crates/axeyum-rewrite/src/int_blast.rs",
    "crates/axeyum-rewrite/src/int_divmod.rs",
    "crates/axeyum-rewrite/src/quantifiers.rs",
    "crates/axeyum-rewrite/src/solve_eqs.rs",
    "crates/axeyum-solver/src/auto.rs",
    "crates/axeyum-solver/src/dl_online.rs",
    "crates/axeyum-solver/src/dpll_lia.rs",
    "crates/axeyum-solver/src/euf.rs",
    // Joined the governed set on 2026-09-08 with the memory-limit work. Nine of
    // its ten constants were already registered, so the file was one entry away
    // from claimable and nobody had claimed it -- and it is the file the three
    // OOM-killed `QF_LRA` runs actually died in.
    "crates/axeyum-solver/src/lra.rs",
    "crates/axeyum-solver/src/lra_online.rs",
    "crates/axeyum-solver/src/lra_theory.rs",
    "crates/axeyum-solver/src/memory_budget.rs",
    "crates/axeyum-solver/src/nia_linearize.rs",
    "crates/axeyum-solver/src/nra.rs",
    // Joined the governed set on 2026-09-09 with the fused portfolio. It has
    // exactly one constant and that constant is a stack RESERVATION whose
    // failure mode is a process abort rather than a decline, which is the kind
    // of value this registry exists to make someone write down.
    "crates/axeyum-solver/src/portfolio.rs",
    "crates/axeyum-solver/src/simplex.rs",
];

/// Admission-class bounds that cross with no signal and are **not yet**
/// attributable — the enumerated backlog, which may only shrink.
///
/// The 2026-09-08 coverage sweep took the registry from 19 governed files to
/// the configuration surface of six crates, and the silent admission-class
/// population went from 12 to 123. Wiring [`note_crossed`] at all of them is
/// per-gate work, not a sweep; pretending otherwise is how a checker starts
/// manufacturing green.
///
/// So this list is the honest state, written down rather than omitted, and
/// `every_silent_admission_bound_is_instrumented` treats it as a **ratchet**,
/// not an exemption:
///
/// - a bound here must really be silent, really be admission-class, and really
///   have NO [`note_crossed`] call site — wiring one without deleting its line
///   here is a failing test, so the list cannot go stale in the direction that
///   flatters it;
/// - a silent bound that is neither wired, nor in [`SILENT_UNINSTRUMENTED`],
///   nor here fails outright, so a lane adding one inherits the requirement;
/// - `the_unattributed_backlog_only_shrinks` pins the count, so the list can
///   lose entries and never gain them.
///
/// The distinction from [`SILENT_UNINSTRUMENTED`] is the point: that list is
/// for a bound this crate *cannot* reach, and it is checked to contain only
/// such bounds. This one is for a bound nobody has got to yet.
pub static SILENT_UNATTRIBUTED: &[&str] = &[
    "crates/axeyum-bv/src/lib.rs::INLINE_DEMAND_RANGES",
    "crates/axeyum-cnf/src/lib.rs::INTERNAL_AND_FLATTEN_NODE_LIMIT",
    "crates/axeyum-cnf/src/xor_extract.rs::MAX_XOR_VARS",
    "crates/axeyum-rewrite/src/canonical.rs::AC_REBUILD_MAX_OPERANDS",
    "crates/axeyum-rewrite/src/inverter.rs::MAX_NARROW_BV_WIDTH",
    "crates/axeyum-smtlib/src/parse.rs::EXACT_BOOLEAN_ATOM_CAP",
    "crates/axeyum-smtlib/src/parse.rs::EXACT_ITE_CASE_CAP",
    "crates/axeyum-smtlib/src/parse.rs::MAX_DEPTH",
    "crates/axeyum-smtlib/src/parse.rs::MAX_TRIGGER_DEPTH",
    "crates/axeyum-smtlib/src/parse.rs::SPLIT_REPLACE_REJOIN_PACKED_LIMIT",
    "crates/axeyum-smtlib/src/parse.rs::STRING_MAX_LEN",
    "crates/axeyum-smtlib/src/parse.rs::WORD_ATOM_MAX_DEPTH",
    "crates/axeyum-solver/src/abv.rs::MAX_BRANCH_SCALAR_CHOICE_DEPTH",
    "crates/axeyum-solver/src/abv.rs::MAX_BRANCH_SELECT_CYCLE_CONJUNCTS",
    "crates/axeyum-solver/src/abv.rs::MAX_FOLLOWUP_OR_CYCLE_GUARD_CONJUNCTS",
    "crates/axeyum-solver/src/abv.rs::MAX_OR_MIXED_BEAM_CONJUNCTS",
    "crates/axeyum-solver/src/abv.rs::MAX_RETURNED_OR_STABILIZATION_CONJUNCTS",
    "crates/axeyum-solver/src/abv.rs::MAX_SCALAR_REPLAY_REPAIR_CONJUNCTS",
    "crates/axeyum-solver/src/abv.rs::MAX_SCALAR_REPLAY_REPAIR_FALSE",
    "crates/axeyum-solver/src/array_axiom.rs::READ_CONGRUENCE_MAX_SATURATION_WORK",
    "crates/axeyum-solver/src/array_bv_abs.rs::BV_ABSTRACTION_TIMEOUT",
    "crates/axeyum-solver/src/array_bv_abs.rs::MAX_ABSTRACTED_NODES",
    "crates/axeyum-solver/src/array_bv_abs.rs::MAX_ABSTRACTED_TERMS",
    "crates/axeyum-solver/src/array_bv_abs.rs::MAX_ABSTRACTION_VISITS",
    "crates/axeyum-solver/src/array_finite.rs::MAX_FINITE_ARRAY_EXT_READS",
    "crates/axeyum-solver/src/bool_euf.rs::MAX_ATOMS",
    "crates/axeyum-solver/src/bv2nat_bound.rs::MAX_BOUND_WIDTH",
    "crates/axeyum-solver/src/bv_uf_local.rs::MAX_LOCAL_BV_WIDTH",
    "crates/axeyum-solver/src/cas_certificate.rs::MAX_ATOMS",
    "crates/axeyum-solver/src/cas_certificate.rs::MAX_DEPTH",
    "crates/axeyum-solver/src/cas_certificate.rs::MAX_MONOMIALS",
    "crates/axeyum-solver/src/cas_certificate.rs::MAX_STEPS",
    "crates/axeyum-solver/src/cas_poly.rs::MAX_IDEAL_ATOMS",
    "crates/axeyum-solver/src/cas_poly.rs::MAX_IDEAL_GENERATORS",
    "crates/axeyum-solver/src/cas_poly.rs::MAX_IDEAL_INEQUALITIES",
    "crates/axeyum-solver/src/combined_theory_lia.rs::DEFER_COMBINED_LIA_FEASIBILITY_ATOMS",
    "crates/axeyum-solver/src/evidence.rs::PRE_SOLVE_ARRAY_AXIOM_DAG_LIMIT",
    "crates/axeyum-solver/src/incremental.rs::MAX_WARM_ARRAY_UF_APPS_PER_ROOT",
    "crates/axeyum-solver/src/incremental.rs::MAX_WARM_STRUCTURAL_ARRAY_DEPTH",
    "crates/axeyum-solver/src/incremental.rs::MAX_WARM_STRUCTURAL_ARRAY_NODES",
    "crates/axeyum-solver/src/lia_online.rs::DEFER_LIA_FEASIBILITY_ATOMS",
    "crates/axeyum-solver/src/lia_online.rs::DEFER_LIA_FEASIBILITY_CLAUSES",
    "crates/axeyum-solver/src/lra.rs::LP_RELAXATION_CORE_MINIMIZE_LIMIT",
    "crates/axeyum-solver/src/lra.rs::TIGHTEN_COEFF_LIMIT",
    "crates/axeyum-solver/src/mbqi_model_finder.rs::DEFAULT_REPAIR_CANDIDATE_CAP",
    "crates/axeyum-solver/src/mbqi_model_finder.rs::DEFAULT_REPAIR_FUNCTION_CAP",
    "crates/axeyum-solver/src/mbqi_model_finder.rs::DEFAULT_REPAIR_VALUE_CAP",
    "crates/axeyum-solver/src/nra_handelman_cert.rs::MAX_GENERATORS",
    "crates/axeyum-solver/src/nra_handelman_cert.rs::MAX_MONOMIALS",
    "crates/axeyum-solver/src/nra_handelman_cert.rs::RELAXATION_DENOMINATOR_THRESHOLD",
    "crates/axeyum-solver/src/nra_real_root.rs::ISOLATE_REFINE_DEPTH",
    "crates/axeyum-solver/src/qinst_egraph.rs::INVENTION_GROUND_CEILING",
    "crates/axeyum-solver/src/qinst_egraph.rs::MAX_CANDIDATE_APPLICATIONS",
    "crates/axeyum-solver/src/qinst_egraph.rs::MAX_CANDIDATE_EQUALITIES",
    "crates/axeyum-solver/src/qinst_egraph.rs::MAX_PREDECESSOR_RECURRENCE_INDEX",
    "crates/axeyum-solver/src/qinst_egraph.rs::MAX_QUANTIFIER_PROVENANCE_DEPTH",
    "crates/axeyum-solver/src/qinst_egraph.rs::MAX_QUANTIFIER_PROVENANCE_NODES",
    "crates/axeyum-solver/src/quant_bool_model_sat.rs::MAX_BOUND_BOOL_BRANCHES",
    "crates/axeyum-solver/src/quant_bool_model_sat.rs::MAX_CANDIDATES",
    "crates/axeyum-solver/src/quant_bool_model_sat.rs::MAX_CHECK_NODES",
    "crates/axeyum-solver/src/quant_bool_model_sat.rs::MAX_FREE_BOOLEANS",
    "crates/axeyum-solver/src/quant_bool_model_sat.rs::QUANT_BOOL_BV_MODEL_BINDER_CAP",
    "crates/axeyum-solver/src/quant_bool_model_sat.rs::QUANT_BOOL_BV_MODEL_DEPTH_CAP",
    "crates/axeyum-solver/src/quant_bool_model_sat.rs::QUANT_BOOL_BV_MODEL_NODE_CAP",
    "crates/axeyum-solver/src/quant_bv_alternation_cert.rs::BV_ALTERNATION_BINDER_CAP",
    "crates/axeyum-solver/src/quant_bv_alternation_cert.rs::BV_ALTERNATION_NODE_CAP",
    "crates/axeyum-solver/src/quant_bv_conjunctive_cert.rs::BV_CONJUNCTIVE_UNIVERSAL_BINDER_CAP",
    "crates/axeyum-solver/src/quant_bv_conjunctive_cert.rs::BV_CONJUNCTIVE_UNIVERSAL_NODE_CAP",
    "crates/axeyum-solver/src/quant_bv_conjunctive_search.rs::SEARCH_CANDIDATE_CAP",
    "crates/axeyum-solver/src/quant_bv_instance_set_cert.rs::BV_POSITIVE_INSTANCE_SET_CAP",
    "crates/axeyum-solver/src/quant_bv_model_sat_cert.rs::QUANT_BV_MODEL_BINDER_CAP",
    "crates/axeyum-solver/src/quant_bv_model_sat_cert.rs::QUANT_BV_MODEL_DEPTH_CAP",
    "crates/axeyum-solver/src/quant_bv_model_sat_cert.rs::QUANT_BV_MODEL_NODE_CAP",
    "crates/axeyum-solver/src/quant_bv_model_sat_search.rs::FREE_BV_CANDIDATE_BITS",
    "crates/axeyum-solver/src/quant_bv_model_sat_search.rs::TOTAL_FREE_BV_BITS_CAP",
    "crates/axeyum-solver/src/quant_bv_paired_exists_cert.rs::BV_PAIRED_EXISTS_BINDER_CAP",
    "crates/axeyum-solver/src/quant_bv_paired_exists_cert.rs::BV_PAIRED_EXISTS_NODE_CAP",
    "crates/axeyum-solver/src/quant_bv_paired_exists_search.rs::PAIRED_EXISTS_PAIR_CAP",
    "crates/axeyum-solver/src/quant_bv_paired_exists_search.rs::TRANSFER_SUBSET_CAP",
    "crates/axeyum-solver/src/quant_counterexample_cover.rs::MAX_COVER_BINDERS",
    "crates/axeyum-solver/src/quant_counterexample_cover.rs::MAX_COVER_SOURCE_NODES",
    "crates/axeyum-solver/src/quant_counterexample_cover.rs::QUANT_COUNTEREXAMPLE_COVER_CASE_CAP",
    "crates/axeyum-solver/src/quant_eq_partition_cert.rs::EQ_PARTITION_CASE_CAP",
    "crates/axeyum-solver/src/quant_finite_cert.rs::RANGE_SIZE_CAP",
    "crates/axeyum-solver/src/quant_fourier_motzkin.rs::MAX_CLAUSE_LITERALS",
    "crates/axeyum-solver/src/quant_fourier_motzkin.rs::MAX_DNF_CLAUSES",
    "crates/axeyum-solver/src/quant_guarded_int.rs::RANGE_SIZE_CAP",
    "crates/axeyum-solver/src/quant_negated_exists_cert.rs::NEGATED_EXISTENTIAL_BINDER_CAP",
    "crates/axeyum-solver/src/quant_negated_exists_cert.rs::NEGATED_EXISTENTIAL_NODE_CAP",
    "crates/axeyum-solver/src/quant_uf_model_sat_cert.rs::QUANTIFIED_UF_BINDER_CAP",
    "crates/axeyum-solver/src/quant_uf_model_sat_cert.rs::QUANTIFIED_UF_PROFILE_CAP",
    "crates/axeyum-solver/src/quant_vacuous_exists_counterexample_cert.rs::VACUOUS_EXISTS_COUNTEREXAMPLE_BINDER_CAP",
    "crates/axeyum-solver/src/quant_vacuous_exists_counterexample_cert.rs::VACUOUS_EXISTS_COUNTEREXAMPLE_NODE_CAP",
    "crates/axeyum-solver/src/sat_bv_backend.rs::MAX_SHARED_GUARD_SPLIT_BRANCHES",
    "crates/axeyum-solver/src/sat_bv_backend.rs::MIN_SHARED_GUARD_SPLIT_BRANCHES",
    "crates/axeyum-solver/src/sat_bv_backend.rs::MIN_SHARED_GUARD_SPLIT_DAG_NODES",
    "crates/axeyum-solver/src/smtlib.rs::DEFAULT_STRING_BOUND",
    "crates/axeyum-solver/src/smtlib.rs::MIN_RUNG_BUDGET",
    "crates/axeyum-solver/src/smtlib.rs::SOURCE_WITNESS_MAX_ALPHABET",
    "crates/axeyum-solver/src/smtlib.rs::SOURCE_WITNESS_MAX_ASSIGNMENTS",
    "crates/axeyum-solver/src/smtlib.rs::SOURCE_WITNESS_MAX_WORD_LEN",
    "crates/axeyum-solver/src/smtlib.rs::WORD_INT_COUPLE_MAX_CANDIDATES",
    "crates/axeyum-solver/src/string_length_cert.rs::MAX_FM_ROWS",
    "crates/axeyum-solver/src/string_length_cert.rs::MAX_SOURCE_NODES",
    "crates/axeyum-solver/src/string_theory.rs::CONCAT_WITNESS_MAX_LEN",
    "crates/axeyum-solver/src/string_theory.rs::CONCAT_WITNESS_MAX_STATES",
    "crates/axeyum-solver/src/string_theory.rs::MEMBERSHIP_MAX_STATES",
    "crates/axeyum-solver/src/uf_fmf.rs::MAX_DOMAIN_SIZE",
    "crates/axeyum-solver/src/uf_fmf.rs::MAX_EXPANSION_BACKOFFS",
    "crates/axeyum-solver/src/uf_fmf.rs::MAX_SOURCE_DAG_NODES",
    "crates/axeyum-solver/src/ufbv_finite.rs::BOOL_UF_EXHAUSTIVE_MAX_BITS",
];

/// The size of the backlog above, pinned so it can only fall.
///
/// A count in a comment is a wish. This one is asserted, and lowering it is the
/// only edit the test accepts.
pub const SILENT_UNATTRIBUTED_MAX: usize = 111;

/// Admission-class bounds that cross with no signal and which this crate
/// **cannot** instrument, each with the structural reason.
///
/// A silent crossing that nothing records is the failure this registry keeps
/// rediscovering: the population riding on such a bound is unmeasurable by
/// construction, so a stale bound nobody hits is indistinguishable from a stale
/// bound carrying fifty files. `every_silent_admission_bound_is_instrumented`
/// therefore requires a [`note_crossed`] call site for every one of them, and
/// this is the escape hatch — deliberately narrow, because an escape hatch that
/// can excuse anything turns the check into decoration.
///
/// It is narrow in a way a reviewer can check mechanically:
/// `uninstrumentable_bounds_are_outside_this_crate` fails if a line here names
/// a bound in `axeyum-solver`, so nothing reachable from
/// [`note_crossed`] can be excused. Only a genuine crate-boundary problem
/// qualifies, and the fix for one is to move the recorder, not to add a line.
pub static SILENT_UNINSTRUMENTED: &[(&str, &str)] = &[(
    "crates/axeyum-rewrite/src/quantifiers.rs::CHAIN_INSTANCE_CAP",
    "`note_crossed` lives in `axeyum-solver`, which depends on `axeyum-rewrite` \
     and not the other way round, so the rewrite crate cannot call it. Making \
     this gate attributable needs the recorder in a crate below both — a \
     refactor with its own ADR, not a line in this table.",
)];

/// Constants in a [`GOVERNED_FILES`] file that are deliberately NOT governing
/// values, each with the reason.
///
/// This list exists so a non-governing constant is *classified* rather than
/// *omitted*. An omission and a judgement look identical in a registry; only
/// this list tells them apart, and a reviewer can disagree with a line here in
/// a way they cannot disagree with an absence.
pub static EXEMPT: &[(&str, &str, &str)] = &[
    (
        "crates/axeyum-solver/src/dl_online.rs",
        "ZERO_VERTEX",
        "An index, not a bound: the fixed vertex id 0 used as the shortest-path source.",
    ),
    (
        "crates/axeyum-solver/src/dl_online.rs",
        "MIN_EQUALITY_GATES",
        "A route-shape predicate on the query's syntax, not a resource bound; it does not \
         meter anything that grows with search effort.",
    ),
    (
        "crates/axeyum-solver/src/dl_online.rs",
        "MAX_MODERATE_ATOMS",
        "Paired with MIN_EQUALITY_GATES in the same syntactic route predicate. Registered \
         nowhere because crossing it changes no resource, only which of two equally \
         complete probes runs first.",
    ),
    (
        "crates/axeyum-solver/src/nia_linearize.rs",
        "BAND",
        "A bit mask (`1 << 62`), not a bound, and function-local: it appears twice in the \
         file with the same value in two different functions.",
    ),
    (
        "crates/axeyum-solver/src/nra.rs",
        "MAX_PROBE_VARS",
        "Bounds a diagnostic probe that cannot change a verdict; it neither admits nor \
         refuses, and its output is advisory.",
    ),
    (
        "crates/axeyum-solver/src/nra.rs",
        "MAX_COORD_VARS",
        "Coordinate-descent sat-search shaping. Only ever finds a model that is then \
         replayed, so it cannot cause a refusal.",
    ),
    (
        "crates/axeyum-solver/src/nra.rs",
        "MAX_COORD_ROUNDS",
        "As MAX_COORD_VARS: shapes a sat-search that is model-replayed either way.",
    ),
    (
        "crates/axeyum-solver/src/nra.rs",
        "REFINE_BOUND",
        "Function-local inside `too_large_to_refine`; an i128 overflow guard on one \
         candidate rational, not a bound on the search. Its effect is covered by the \
         registered MAX_REFINE_ROUNDS, which is what eventually surfaces as `unknown`.",
    ),
    (
        "crates/axeyum-rewrite/src/arrays.rs",
        "READ_OVER_WRITE_WITNESS_SAMPLES",
        "Audit power of a faithfulness witness, not a solver bound: it sets how many \
         concrete tests the witness runs, and is compared against nothing that varies \
         with the query.",
    ),
    (
        "crates/axeyum-rewrite/src/arrays.rs",
        "SAMPLED_ARRAY_ENTRIES",
        "As above: witness-sampling shape, not an admission or effort bound.",
    ),
    (
        "crates/axeyum-rewrite/src/int_divmod.rs",
        "INT_DIVMOD_WITNESS_SAMPLES",
        "Witness audit power, not a solver bound.",
    ),
    (
        "crates/axeyum-rewrite/src/int_divmod.rs",
        "SAMPLED_INT_BOUND",
        "The magnitude range the witness samples over; audit shape, not a solver bound.",
    ),
];

// ---------------------------------------------------------------------------
// Recording
// ---------------------------------------------------------------------------

std::thread_local! {
    /// Whether config consultations on this thread should be recorded.
    ///
    /// Scoped exactly as `cdclt::COLLECT_LAYER_STATS` and
    /// `layers::COLLECT_BV_LAYER_STATS` are, and for the same reason: one knob
    /// at the top of a solve, read at the handful of consultation points,
    /// rather than a parameter threaded through every dispatch and theory
    /// entry point. Off by default, and off costs one `Cell<bool>` read.
    static RECORD_CONFIG: Cell<bool> = const { Cell::new(false) };
    /// Keys consulted on this thread while recording was enabled.
    ///
    /// A `BTreeSet`, never a `HashSet`: the emitted line is part of a run's
    /// output, and this tree's determinism promise forbids output whose order
    /// depends on per-process hash seeding.
    static CONSULTED: RefCell<BTreeSet<&'static str>> =
        const { RefCell::new(BTreeSet::new()) };
    /// Bounds actually CROSSED on this thread while recording was enabled, with
    /// the observed quantity and the bound it crossed.
    ///
    /// A `BTreeMap` for the same reason `CONSULTED` is a `BTreeSet`: this
    /// reaches a run's output and the determinism promise forbids an order that
    /// depends on hash seeding.
    static CROSSED: RefCell<BTreeMap<&'static str, (u64, u64)>> =
        const { RefCell::new(BTreeMap::new()) };
    /// The cross-thread mirror of [`CONSULTED`] / [`CROSSED`], when a
    /// [`crate::live_instruments`] board was installed at
    /// [`ConfigTraceGuard::enable`] time. `None` on every ordinary run.
    ///
    /// Created at guard construction rather than tested at each recording site,
    /// so [`note_consulted`] on a run WITHOUT a board costs the same one
    /// `Cell<bool>` read it always did.
    static CONFIG_MIRROR: RefCell<Option<Arc<ConfigTraceMirror>>> =
        const { RefCell::new(None) };
}

/// The cross-thread half of the `; config` line: the consulted keys and the
/// crossed bounds a **running** query has accumulated so far.
///
/// # Why only these two
///
/// Everything else on the line — the digest, the entry count, the dated count,
/// the environment overrides — is derived from [`REGISTRY`] and the process
/// environment, both of which any thread can read at any time. The consulted
/// and crossed sets were the only thread-local half, and they were therefore
/// the reason the whole line vanished on a watchdog kill: printing the static
/// half alone would leave `consulted=` silently absent, which reads as "nothing
/// was consulted" rather than "we could not see".
///
/// # Cost
///
/// Written only when the set actually GROWS. A key already present is a
/// `BTreeSet` lookup on the thread-local and a return, so a bound consulted in
/// a loop takes the shared lock once, not once per iteration.
#[derive(Debug, Default)]
pub struct ConfigTraceMirror {
    /// Both sets under one lock; see [`ConfigTraceState`].
    state: Mutex<ConfigTraceState>,
}

/// The two sets a [`ConfigTraceMirror`] holds, behind one lock so a reader
/// cannot observe a crossing whose key is not yet in the consulted set.
///
/// A named struct rather than the tuple this started as: the tuple tripped
/// `clippy::type_complexity`, and naming the halves is the fix that also makes
/// that invariant readable at the field.
#[derive(Debug, Default)]
struct ConfigTraceState {
    /// Every governing key looked at, mirroring [`CONSULTED`].
    consulted: BTreeSet<&'static str>,
    /// Every bound crossed, with the observed quantity and the bound it
    /// crossed, mirroring [`CROSSED`].
    crossed: BTreeMap<&'static str, (u64, u64)>,
}

impl ConfigTraceMirror {
    /// Records `key` as consulted. A poisoned lock is recovered rather than
    /// propagated: telemetry must never turn one panic into two.
    fn note_consulted(&self, key: &'static str) {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        state.consulted.insert(key);
    }

    /// Records `key` as crossed at `observed` against `bound`, keeping the
    /// first crossing exactly as [`CROSSED`] does.
    fn note_crossed(&self, key: &'static str, observed: u64, bound: u64) {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        state.consulted.insert(key);
        state.crossed.entry(key).or_insert((observed, bound));
    }

    /// The consulted keys and crossed bounds accumulated so far, readable from
    /// any thread while the worker is still running.
    #[must_use]
    pub fn sample(&self) -> (Vec<&'static str>, Vec<(&'static str, u64, u64)>) {
        let state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        (
            state.consulted.iter().copied().collect(),
            state
                .crossed
                .iter()
                .map(|(k, (o, b))| (*k, *o, *b))
                .collect(),
        )
    }
}

/// Enables configuration recording for the lifetime of the returned guard,
/// restoring the previous setting on drop so nested solves compose.
///
/// Same convention as `TheoryLayerStatsGuard` / `BvLayerStatsGuard` /
/// `DlOnlineStatsGuard` / `FrontDoorStatsGuard`, and wired to the same
/// `--trace` / `AXEYUM_TRACE=1` flag in `smtcomp_cli`. Constructing no guard
/// means no recording and no allocation.
///
/// ```ignore
/// let _guard = axeyum_solver::ConfigTraceGuard::enable();
/// let _ = axeyum_solver::solve_smtlib(text, &config);
/// let line = axeyum_solver::config_trace_line();
/// ```
pub struct ConfigTraceGuard(bool);

impl ConfigTraceGuard {
    /// Enables recording, and clears whatever a previous guard left behind so a
    /// run's consulted set describes THIS run.
    #[must_use]
    pub fn enable() -> Self {
        CONSULTED.with(|c| c.borrow_mut().clear());
        CROSSED.with(|c| c.borrow_mut().clear());
        // The board decision is taken HERE, once, rather than at each recording
        // site: `note_consulted` on a run with no board must keep costing one
        // `Cell<bool>` read. A board installed later in the same guard's extent
        // simply does not get a `; config` mirror, which is the same answer the
        // instrument gave before this existed.
        let mirror = crate::live_instruments::installed().then(|| {
            let mirror = Arc::new(ConfigTraceMirror::default());
            crate::live_instruments::publish_live(
                crate::live_instruments::instrument::CONFIG,
                Arc::clone(&mirror),
                // A handle, never a snapshot: the query writes through it for as
                // long as it runs, so a watchdog always reads the latest sets
                // without the worker having to publish again. The reading is
                // therefore always partial — a query that has not returned may
                // still consult more bounds.
                crate::live_instruments::Sampled::InFlight,
            );
            mirror
        });
        CONFIG_MIRROR.with(|c| *c.borrow_mut() = mirror);
        ConfigTraceGuard(RECORD_CONFIG.with(|c| c.replace(true)))
    }
}

impl Drop for ConfigTraceGuard {
    fn drop(&mut self) {
        RECORD_CONFIG.with(|c| c.set(self.0));
        CONFIG_MIRROR.with(|c| *c.borrow_mut() = None);
    }
}

/// Mirrors one recording onto the cross-thread board, when a board was
/// installed at [`ConfigTraceGuard::enable`] time.
///
/// Called only when the thread-local set actually grew, so a bound consulted
/// inside a loop takes the shared lock once. `try_borrow` rather than `borrow`
/// for the same reason `live_instruments::publish_live` uses it: a re-entrant
/// recording (which no current call path produces) must drop the mirror write,
/// never panic mid-solve.
fn mirror_config(f: impl FnOnce(&ConfigTraceMirror)) {
    CONFIG_MIRROR.with(|c| {
        if let Ok(slot) = c.try_borrow()
            && let Some(mirror) = slot.as_ref()
        {
            f(mirror);
        }
    });
}

/// Records that a governing value was consulted, when recording is on.
///
/// Off by default this is one thread-local `Cell<bool>` read and a return: no
/// allocation, no clock, and nothing that can change a verdict. `key` must be a
/// registered [`ConfigEntry::key`]; `consulted_keys_are_registered` checks that
/// every key any call site passes exists in [`REGISTRY`], so a typo is a failing
/// test rather than a line of output nobody can trace.
pub fn note_consulted(key: &'static str) {
    if !RECORD_CONFIG.with(Cell::get) {
        return;
    }
    // The insert's return value is the growth test: a key already present means
    // the shared set already has it, so the cross-thread mirror below is
    // reached once per distinct key rather than once per consultation.
    let is_new = CONSULTED.with(|c| c.borrow_mut().insert(key));
    if is_new {
        mirror_config(|mirror| mirror.note_consulted(key));
    }
}

/// The keys consulted on this thread since the active guard was constructed,
/// sorted.
#[must_use]
pub fn consulted() -> Vec<&'static str> {
    CONSULTED.with(|c| c.borrow().iter().copied().collect())
}

/// Records that a governing value was **crossed**, when recording is on.
///
/// [`note_consulted`] says a bound was looked at. This says it *bit*, and with
/// what numbers — which is the difference between a run that can be traced and
/// one that cannot. The registry's own enumeration found **12 admission-class
/// entries whose crossing produces no branch a caller can observe**, and for
/// those, "how many files did this bound cost us?" is unmeasurable by
/// construction: the population riding on a silent gate cannot be counted, so a
/// stale bound nobody hits looks exactly like a stale bound carrying fifty
/// files. That is why this is a separate call and not a field on
/// [`ConfigEntry`].
///
/// `observed` and `bound` are in the entry's own [`ConfigEntry::unit`], stated
/// in the same currency the code compared — never normalized here, because two
/// gates metering one resource in different units is a defect this registry
/// exists to make visible, not to launder.
///
/// Off by default this is one thread-local `Cell<bool>` read and a return: no
/// allocation, no clock, and nothing that can change a verdict. Only the
/// **first** crossing of a key is kept, so a bound crossed in a loop cannot
/// make the trace line grow without limit, and the recorded numbers are the
/// ones from the crossing that first changed the route.
pub fn note_crossed(key: &'static str, observed: u64, bound: u64) {
    if !RECORD_CONFIG.with(Cell::get) {
        return;
    }
    let is_new_key = CONSULTED.with(|c| c.borrow_mut().insert(key));
    // Only the FIRST crossing of a key is kept, here and in the mirror, so this
    // is reached once per distinct key however tight the loop that crossed it.
    let is_new_crossing = CROSSED.with(|c| {
        let mut crossed = c.borrow_mut();
        let before = crossed.len();
        crossed.entry(key).or_insert((observed, bound));
        crossed.len() != before
    });
    if is_new_key || is_new_crossing {
        mirror_config(|mirror| mirror.note_crossed(key, observed, bound));
    }
}

/// The bounds crossed on this thread since the active guard was constructed, as
/// `(key, observed, bound)`, sorted by key.
#[must_use]
pub fn crossings() -> Vec<(&'static str, u64, u64)> {
    CROSSED.with(|c| c.borrow().iter().map(|(k, (o, b))| (*k, *o, *b)).collect())
}

/// Environment overrides in force for this process, as `(variable, value)`,
/// sorted by variable name.
///
/// Read at call time rather than cached, so a test that sets one sees it. Only
/// variables named by a registry entry are reported: an unrecognized
/// `AXEYUM_*` variable is not this registry's business and reporting it would
/// make the line unfalsifiable.
#[must_use]
pub fn active_env_overrides() -> Vec<(&'static str, String)> {
    let mut names: BTreeSet<&'static str> = BTreeSet::new();
    for e in REGISTRY {
        if let Some(v) = e.env_override {
            names.insert(v);
        }
    }
    names
        .into_iter()
        .filter_map(|n| std::env::var(n).ok().map(|v| (n, v)))
        .collect()
}

/// A 64-bit FNV-1a digest over the registry's sorted `key=value` pairs and the
/// active environment overrides.
///
/// Two runs printing the same digest used the same configuration; two runs
/// printing different digests did not, and the `; config-override` lines say
/// how. Dependency-free on purpose — `axeyum-solver` has no hash crate and the
/// digest is an identity check between runs, not a security primitive.
#[must_use]
pub fn digest() -> u64 {
    const OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut h = OFFSET;
    let mut feed = |bytes: &[u8]| {
        for b in bytes {
            h ^= u64::from(*b);
            h = h.wrapping_mul(PRIME);
        }
    };
    for e in REGISTRY {
        feed(e.module.as_bytes());
        feed(b"::");
        feed(e.name.as_bytes());
        feed(b"=");
        feed(e.value.as_bytes());
        feed(b"\n");
    }
    for (k, v) in active_env_overrides() {
        feed(b"env ");
        feed(k.as_bytes());
        feed(b"=");
        feed(v.as_bytes());
        feed(b"\n");
    }
    h
}

/// How many registry entries carry a dated justification.
///
/// Reported alongside the total because the ratio is the number this module
/// exists to move, and a registry that did not report it could grow undated
/// entries indefinitely without anything noticing.
#[must_use]
pub fn dated_count() -> usize {
    REGISTRY.iter().filter(|e| e.is_dated()).count()
}

/// How many registry entries carry NO date — the number this module is
/// currently worst at, and therefore the one it should be hardest to overlook.
///
/// It is derived, never written down: a count in prose is a wish, and this one
/// has moved by 300 in two days. [`config_trace_line`] prints it, so a run's own
/// output says what fraction of its configuration nobody has measured.
#[must_use]
pub fn undated_count() -> usize {
    REGISTRY.len() - dated_count()
}

/// The floor under [`dated_count`], asserted by `the_dated_count_only_rises`.
///
/// A ratchet on DATES, deliberately not on the undated share. Ratcheting the
/// share would punish honest coverage work — registering a governing value
/// nobody has measured is exactly what this module wants a lane to do, and it
/// moves the percentage the wrong way. What must never happen is *losing* a
/// date: a measurement deleted, or an entry quietly downgraded to `undated`
/// because its `rests_on` went red and that was the cheap way out.
///
/// Raise it when dates are added. Lowering it is the edit that needs an
/// argument, and the test says so in its failure message.
pub const DATED_FLOOR: usize = 77;

/// The one-line configuration summary a `--trace` run prints.
///
/// Deliberately one line and digest-first: a corpus sweep's output is grepped,
/// and a per-run dump of 114 entries would not be. The full table is available
/// through [`REGISTRY`] and from `scripts/check-config-registry-staleness.py`.
#[must_use]
pub fn config_trace_line() -> String {
    config_trace_line_from(&consulted(), &crossings())
}

/// The best `; config` reading `board` holds, or `None` when the query never
/// installed a mirror (which on a `--trace` run means it never got as far as
/// constructing a [`ConfigTraceGuard`]).
///
/// # Why this is not just the static half
///
/// The digest, the entry counts and the environment overrides are readable from
/// any thread at any time. The consulted and crossed sets are not, and printing
/// the line without them would leave `consulted=` silently absent — which reads
/// as "nothing was consulted", the one wrong answer this line must never give.
/// So the whole line is either rendered from a mirror that has the sets, or not
/// rendered at all.
///
/// The reading is always [`crate::live_instruments::Sampled::InFlight`]: the
/// mirror is a handle a running query writes through, so a query that has not
/// returned may still consult bounds this line does not name. The sets are
/// therefore LOWER BOUNDS, exactly like every other partial reading.
#[must_use]
pub fn live_config_trace_line(
    board: &crate::live_instruments::LiveInstruments,
) -> Option<crate::live_instruments::LiveSample<String>> {
    let handle =
        board.sample::<Arc<ConfigTraceMirror>>(crate::live_instruments::instrument::CONFIG)?;
    let (consulted, crossed) = handle.value.sample();
    Some(crate::live_instruments::LiveSample {
        value: config_trace_line_from(&consulted, &crossed),
        sampled: crate::live_instruments::Sampled::InFlight,
        sequence: handle.sequence,
    })
}

/// Renders the `; config` line from an explicit consulted/crossed pair.
///
/// Split out of [`config_trace_line`] so the watchdog path renders the SAME
/// bytes from the cross-thread mirror that a completed run renders from its
/// thread-local sets — one formatter, so the two families cannot drift.
fn config_trace_line_from(
    consulted: &[&'static str],
    crossed: &[(&'static str, u64, u64)],
) -> String {
    // `undated=` is here rather than left to a gate's output because the
    // undated share is the honest headline of this module and a number that
    // only a checker prints is a number most readers never see.
    let mut s = format!(
        "; config digest={:016x} entries={} dated={} undated={}",
        digest(),
        REGISTRY.len(),
        dated_count(),
        undated_count()
    );
    for (k, v) in active_env_overrides() {
        let _ = write!(s, " env:{k}={v}");
    }
    if !consulted.is_empty() {
        let _ = write!(s, " consulted={}", consulted.len());
        for key in consulted {
            s.push(' ');
            s.push_str(key);
        }
    }
    // Crossings come AFTER consultations and carry their numbers, so a reader
    // can tell "this bound was looked at" from "this bound decided the route,
    // at 1560 against 1024". A silent decline that leaves no such line is the
    // defect; a run that prints one is attributable.
    if !crossed.is_empty() {
        let _ = write!(s, " crossed={}", crossed.len());
        for (key, observed, bound) in crossed {
            let _ = write!(s, " {key}={observed}/{bound}");
        }
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;
    use std::path::{Path, PathBuf};

    /// The workspace root, derived from this crate's manifest directory rather
    /// than from a hardcoded path, so the tests work from any checkout or
    /// worktree.
    fn repo_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("crates/<crate> has two ancestors")
            .to_path_buf()
    }

    /// Module-level `const NAME: <numeric> = value;` occurrences in one file,
    /// skipping `#[cfg(test)]` items.
    ///
    /// A deliberately independent re-implementation of
    /// `scripts/config_registry_scan.py`, so the registry has two readers of
    /// the same source rather than one reader trusted twice. That paid for
    /// itself immediately: written line-at-a-time it read an EMPTY value for
    /// `lra_theory::DEFAULT_ONLINE_LRA_BUDGET_BYTES`, whose initializer sits on
    /// the following line, and `every_entry_names_a_live_constant` reported the
    /// disagreement against a registry row that was in fact correct. Values
    /// therefore continue across lines to the terminating `;`, as the Python
    /// side already did.
    fn scan(path: &Path) -> BTreeMap<String, String> {
        let text = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let types = [
            "usize",
            "u8",
            "u16",
            "u32",
            "u64",
            "u128",
            "i8",
            "i16",
            "i32",
            "i64",
            "i128",
            "f32",
            "f64",
            "Duration",
            "std::time::Duration",
        ];
        let mut out = BTreeMap::new();
        let lines: Vec<&str> = text.lines().collect();
        let skip = cfg_test_spans(&lines);
        for (idx, raw) in lines.iter().enumerate() {
            if skip.iter().any(|(a, b)| idx >= *a && idx < *b) {
                continue;
            }
            let line = raw.trim_start();
            let line = line
                .strip_prefix("pub(crate) ")
                .or_else(|| line.strip_prefix("pub(super) "))
                .or_else(|| line.strip_prefix("pub "))
                .unwrap_or(line);
            let Some(rest) = line.strip_prefix("const ") else {
                continue;
            };
            let Some((name, after)) = rest.split_once(':') else {
                continue;
            };
            let name = name.trim();
            if name.is_empty()
                || !name
                    .chars()
                    .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
            {
                continue;
            }
            let Some((ty, value)) = after.split_once('=') else {
                continue;
            };
            if !types.contains(&ty.trim()) {
                continue;
            }
            // A `const` initializer may sit on following lines. Accumulate to
            // the terminating `;`, collapsing whitespace, so the value read
            // here is the value the Python scanner reads.
            let mut acc = value.to_string();
            let mut k = idx;
            while !acc.contains(';') && k + 1 < lines.len() {
                k += 1;
                acc.push(' ');
                acc.push_str(lines[k]);
            }
            let acc = acc.split(';').next().unwrap_or("").to_string();
            let value = acc.split_whitespace().collect::<Vec<_>>().join(" ");
            out.insert(name.to_string(), value);
        }
        out
    }

    /// Half-open line spans of `#[cfg(test)]` items, by brace depth.
    fn cfg_test_spans(lines: &[&str]) -> Vec<(usize, usize)> {
        let mut spans = Vec::new();
        let mut i = 0;
        while i < lines.len() {
            if lines[i].trim() != "#[cfg(test)]" {
                i += 1;
                continue;
            }
            let start = i;
            let mut j = i + 1;
            let mut depth: i32 = 0;
            let mut opened = false;
            while j < lines.len() {
                for ch in lines[j].chars() {
                    match ch {
                        '{' => {
                            depth += 1;
                            opened = true;
                        }
                        '}' => depth -= 1,
                        _ => {}
                    }
                }
                if opened && depth <= 0 {
                    break;
                }
                if !opened && lines[j].contains(';') {
                    break;
                }
                j += 1;
            }
            spans.push((start, (j + 1).min(lines.len())));
            i = j + 1;
        }
        spans
    }

    /// The table must be sorted by key and hold no key twice.
    ///
    /// Sortedness is not cosmetic: a run emits its configuration from this
    /// slice, and comparing two runs' output is only meaningful if the order is
    /// fixed independently of how the table was edited.
    #[test]
    fn registry_is_sorted_and_unique() {
        let keys: Vec<String> = REGISTRY.iter().map(ConfigEntry::key).collect();
        let mut sorted = keys.clone();
        sorted.sort();
        assert_eq!(keys, sorted, "REGISTRY is not sorted by module::name");
        let unique: BTreeSet<&String> = keys.iter().collect();
        assert_eq!(unique.len(), keys.len(), "REGISTRY holds a duplicate key");
    }

    /// Every entry must name a constant that still exists, at the module it
    /// claims, with the value it records.
    ///
    /// This is what makes a deleted or renamed constant a failing test instead
    /// of a registry line that quietly describes nothing. Function-local
    /// constants (`MAX_EXP`, `REFINE_BOUND`) are matched by name only, since a
    /// module-level scan cannot see them.
    #[test]
    fn every_entry_names_a_live_constant() {
        let root = repo_root();
        let mut missing = Vec::new();
        let mut wrong_value = Vec::new();
        for e in REGISTRY {
            let path = root.join(e.module);
            assert!(
                path.exists(),
                "{} names a file that does not exist",
                e.key()
            );
            let found = scan(&path);
            match found.get(e.name) {
                Some(v) if v == e.value => {}
                Some(v) => {
                    wrong_value.push(format!("{}: registry {} vs source {}", e.key(), e.value, v));
                }
                None => {
                    // A function-local `const` is invisible to a module-level
                    // scan, so fall back to a textual search that still fails
                    // if the constant is gone entirely.
                    let text = std::fs::read_to_string(&path).expect("read module");
                    let needle = format!("const {}:", e.name);
                    if !text.contains(&needle) {
                        missing.push(e.key());
                    }
                }
            }
        }
        assert!(
            missing.is_empty(),
            "registry names constants that no longer exist: {missing:?}"
        );
        assert!(
            wrong_value.is_empty(),
            "registry values disagree with the source: {wrong_value:?}"
        );
    }

    /// Every constant in a governed file must be registered or exempted.
    ///
    /// This is the guard that dies when an entry is deleted, and the one that
    /// forces a lane adding a new cap to a governed file to say what it is. It
    /// derives its population from the SOURCE, so it measures the tree rather
    /// than the maintainer's memory.
    #[test]
    fn every_governing_constant_is_registered() {
        let root = repo_root();
        let registered: BTreeSet<(&str, &str)> =
            REGISTRY.iter().map(|e| (e.module, e.name)).collect();
        let exempt: BTreeSet<(&str, &str)> = EXEMPT.iter().map(|(m, n, _)| (*m, *n)).collect();
        let mut unclassified = Vec::new();
        for file in GOVERNED_FILES {
            let path = root.join(file);
            assert!(path.exists(), "governed file missing: {file}");
            for name in scan(&path).keys() {
                let key = (*file, name.as_str());
                let hit = registered.iter().any(|(m, n)| *m == key.0 && *n == key.1)
                    || exempt.iter().any(|(m, n)| *m == key.0 && *n == key.1);
                if !hit {
                    unclassified.push(format!("{file}::{name}"));
                }
            }
        }
        assert!(
            unclassified.is_empty(),
            "constants in governed files with neither a REGISTRY entry nor an EXEMPT reason: \
             {unclassified:#?}\nAdd an entry describing what it governs, or an EXEMPT line \
             saying why it is not a governing value."
        );
    }

    /// Every key any `note_consulted` call site passes must be a registered
    /// key.
    ///
    /// The keys are `&'static str` rather than typed handles, so a typo would
    /// otherwise become a line of `--trace` output that traces to nothing. This
    /// derives its population by scanning the crate's own sources for the call,
    /// so it measures the call sites that exist rather than a list someone
    /// remembered to update — and it fails equally on a call site added without
    /// an entry and on an entry renamed without its call site.
    #[test]
    fn consulted_keys_are_registered() {
        let src_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let keys: BTreeSet<String> = REGISTRY.iter().map(ConfigEntry::key).collect();
        let mut sites = 0usize;
        let mut bad = Vec::new();
        let mut stack = vec![src_dir];
        while let Some(dir) = stack.pop() {
            for entry in std::fs::read_dir(&dir).expect("read src dir") {
                let path = entry.expect("dir entry").path();
                if path.is_dir() {
                    stack.push(path);
                    continue;
                }
                if path.extension().is_none_or(|e| e != "rs") {
                    continue;
                }
                // Skip this file. It DEFINES `note_consulted` and this very
                // scanner quotes the call in its own source, so including it
                // makes the test match its own string literals and report two
                // fragments of Rust as unregistered keys. That is the second
                // self-reference bug in this module — the first was
                // `registry_len_matches_its_own_source` counting its own
                // needle — and both produced confident, plausible, wrong
                // failure messages about the table.
                if path.file_name().is_some_and(|f| f == "config_registry.rs") {
                    continue;
                }
                let text = std::fs::read_to_string(&path).expect("read source");
                // Match `note_consulted(` / `note_crossed(` followed by a string
                // literal, across the line break rustfmt inserts for a long key.
                // BOTH recorders are scanned: a crossing key is exactly as able
                // to be a typo as a consultation key, and a crossing recorded
                // under an unregistered key is worse — it is a trace line
                // nobody can resolve back to a bound.
                for recorder in ["note_consulted(", "note_crossed("] {
                    let mut rest = text.as_str();
                    while let Some(at) = rest.find(recorder) {
                        rest = &rest[at + recorder.len()..];
                        let Some(open) = rest.find('"') else { break };
                        // Only a whitespace run may separate the paren from the
                        // literal; anything else is a call passing a variable,
                        // which this test cannot check and does not claim to.
                        if !rest[..open].chars().all(char::is_whitespace) {
                            continue;
                        }
                        let after = &rest[open + 1..];
                        let Some(close) = after.find('"') else { break };
                        let key = &after[..close];
                        sites += 1;
                        if !keys.contains(key) {
                            bad.push(format!("{}: {key}", path.display()));
                        }
                        rest = &after[close..];
                    }
                }
            }
        }
        assert!(
            bad.is_empty(),
            "note_consulted / note_crossed keys that are not registered: {bad:#?}"
        );
        // A scan that found nothing would pass vacuously, which is the failure
        // mode this repository has been bitten by most often.
        assert!(
            sites >= 6,
            "expected the instrumented gates to be found; the scan saw {sites} \
             call site(s), so it is passing vacuously"
        );
    }

    /// Every key passed to one recorder, read from this crate's own sources.
    ///
    /// Shared by the coverage guard below. Deliberately a second reader of the
    /// same text rather than a list: a coverage test whose population is typed
    /// by hand measures the maintainer's memory, and this one exists precisely
    /// because eleven of twelve silent gates were unattributable without anyone
    /// noticing.
    fn recorded_keys(recorder: &str) -> BTreeSet<String> {
        let src_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut keys = BTreeSet::new();
        let mut stack = vec![src_dir];
        while let Some(dir) = stack.pop() {
            for entry in std::fs::read_dir(&dir).expect("read src dir") {
                let path = entry.expect("dir entry").path();
                if path.is_dir() {
                    stack.push(path);
                    continue;
                }
                if path.extension().is_none_or(|e| e != "rs") {
                    continue;
                }
                // This file quotes the recorder's own name in its doc comments
                // and in this scanner, so including it would report fragments
                // of Rust as recorded keys.
                if path.file_name().is_some_and(|f| f == "config_registry.rs") {
                    continue;
                }
                let text = std::fs::read_to_string(&path).expect("read source");
                let mut rest = text.as_str();
                while let Some(at) = rest.find(recorder) {
                    rest = &rest[at + recorder.len()..];
                    let Some(open) = rest.find('"') else { break };
                    if !rest[..open].chars().all(char::is_whitespace) {
                        continue;
                    }
                    let after = &rest[open + 1..];
                    let Some(close) = after.find('"') else { break };
                    keys.insert(after[..close].to_string());
                    rest = &after[close..];
                }
            }
        }
        keys
    }

    /// Every admission-class bound that crosses with **no signal** must have a
    /// [`note_crossed`] call site, or be named in [`SILENT_UNINSTRUMENTED`].
    ///
    /// This is the ratchet on the gap the registry's own enumeration measured:
    /// twelve entries changed behaviour with no branch a caller could observe,
    /// and eleven of them recorded nothing at all, so "how many files did this
    /// bound cost us?" was unanswerable by construction. The population is
    /// derived from [`REGISTRY`] rather than written down, so a lane adding a
    /// silent bound inherits the requirement instead of being trusted to
    /// remember it.
    #[test]
    fn every_silent_admission_bound_is_instrumented() {
        let crossed = recorded_keys("note_crossed(");
        let excused: BTreeSet<&str> = SILENT_UNINSTRUMENTED.iter().map(|(k, _)| *k).collect();
        let backlog: BTreeSet<&str> = SILENT_UNATTRIBUTED.iter().copied().collect();
        let mut population = 0usize;
        let mut unclassified = Vec::new();
        for e in REGISTRY {
            let admission = matches!(
                e.on_exceed,
                OnExceed::RefuseUnknown | OnExceed::DeclineRoute
            ) || (e.on_exceed == OnExceed::Relax && e.signal == Signal::None);
            if !admission || e.signal != Signal::None {
                continue;
            }
            population += 1;
            let key = e.key();
            if !crossed.contains(&key)
                && !excused.contains(key.as_str())
                && !backlog.contains(key.as_str())
            {
                unclassified.push(key);
            }
        }
        // A population of zero would make this pass while measuring nothing —
        // the failure mode this repository has been bitten by most often. The
        // floor is well below the measured 123 and above anything an accident
        // could produce; lowering it needs a measurement, not a convenience.
        assert!(
            population >= 100,
            "the silent admission-class population is {population}; this check is passing vacuously"
        );
        assert!(
            unclassified.is_empty(),
            "admission-class bounds that cross with no signal and record no crossing, so a run \
             that lost a decision to one cannot say so: {unclassified:#?}\nWire \
             `config_registry::note_crossed(key, observed, bound)` at the gate, add a line to \
             SILENT_UNINSTRUMENTED saying why this crate cannot, or — only for a bound that \
             already existed — SILENT_UNATTRIBUTED, whose count may not grow."
        );
    }

    /// The backlog may only shrink, and every line in it must still describe a
    /// bound that is silent, admission-class, and genuinely unwired.
    ///
    /// Without this the backlog is an exemption list with a nicer name: a lane
    /// could add a silent bound and a line excusing it in the same diff, and
    /// nothing would notice. With it, the only edits the suite accepts are
    /// deletions — and a deletion is only possible by wiring the gate.
    ///
    /// The "still unwired" half matters as much as the count. A key that has
    /// been wired but left in the list makes the backlog overstate the debt,
    /// which sounds harmless and is not: the number is what this programme
    /// reports as its remaining gap, and a number nobody can trust downward is
    /// as useless as one nobody can trust upward.
    #[test]
    fn the_unattributed_backlog_only_shrinks() {
        assert!(
            SILENT_UNATTRIBUTED.len() <= SILENT_UNATTRIBUTED_MAX,
            "the unattributed backlog grew to {} against a pinned maximum of {}; a NEW silent \
             bound must be wired, not excused",
            SILENT_UNATTRIBUTED.len(),
            SILENT_UNATTRIBUTED_MAX
        );
        let mut sorted = SILENT_UNATTRIBUTED.to_vec();
        sorted.sort_unstable();
        assert_eq!(
            SILENT_UNATTRIBUTED.to_vec(),
            sorted,
            "SILENT_UNATTRIBUTED is not sorted, so two lanes editing it will conflict silently"
        );
        let unique: BTreeSet<&&str> = SILENT_UNATTRIBUTED.iter().collect();
        assert_eq!(
            unique.len(),
            SILENT_UNATTRIBUTED.len(),
            "SILENT_UNATTRIBUTED holds a key twice, which inflates the debt it reports"
        );

        let crossed = recorded_keys("note_crossed(");
        let silent: BTreeSet<String> = REGISTRY
            .iter()
            .filter(|e| {
                e.signal == Signal::None
                    && (matches!(
                        e.on_exceed,
                        OnExceed::RefuseUnknown | OnExceed::DeclineRoute
                    ) || e.on_exceed == OnExceed::Relax)
            })
            .map(ConfigEntry::key)
            .collect();
        let mut wrong = Vec::new();
        for key in SILENT_UNATTRIBUTED {
            if !silent.contains(*key) {
                wrong.push(format!(
                    "{key}: not a silent admission-class registry entry"
                ));
            }
            if crossed.contains(*key) {
                wrong.push(format!(
                    "{key}: is wired to note_crossed — delete this line and lower \
                     SILENT_UNATTRIBUTED_MAX"
                ));
            }
        }
        assert!(wrong.is_empty(), "{wrong:#?}");
        assert_eq!(
            SILENT_UNATTRIBUTED_MAX,
            SILENT_UNATTRIBUTED.len(),
            "the pinned maximum must equal the list it pins, or the slack is room to grow"
        );
    }

    /// [`SILENT_UNINSTRUMENTED`] may only excuse a bound this crate genuinely
    /// cannot reach.
    ///
    /// Without this the escape hatch above excuses anything, and a coverage
    /// check that can be satisfied by editing its own exemption list is not a
    /// check. A bound defined in `axeyum-solver` is reachable from
    /// [`note_crossed`] by construction, so naming one here is always wrong.
    #[test]
    fn uninstrumentable_bounds_are_outside_this_crate() {
        let registered: BTreeSet<String> = REGISTRY.iter().map(ConfigEntry::key).collect();
        for (key, reason) in SILENT_UNINSTRUMENTED {
            assert!(
                registered.contains(*key),
                "{key} is excused from instrumentation but is not a registered key"
            );
            assert!(
                !key.starts_with("crates/axeyum-solver/"),
                "{key} is in this crate, so `note_crossed` can reach it; wire the gate \
                 instead of excusing it"
            );
            assert!(
                !reason.is_empty(),
                "{key} is excused with no reason, which is an omission wearing a judgement's \
                 clothes"
            );
        }
    }

    /// An instrumented gate really does record its key when the guard is on,
    /// end to end through the real code path.
    ///
    /// `recording_is_opt_in_and_restores` calls [`note_consulted`] directly, so
    /// it proves the mechanism and NOT the wiring. This drives a real
    /// `simplex::Incremental::new`, which is one of the four instrumented
    /// sites. Written because a hand check of `--trace` over the micro and
    /// regression corpora printed no `consulted=` field on any of 155 files —
    /// those queries are all decided before reaching an instrumented gate — and
    /// an instrument nothing has been shown to reach is indistinguishable from
    /// one that does not work.
    ///
    /// Gated on `full` because it names `crate::simplex`, which lives inside
    /// `full_modules!()` (`lib.rs:70`) and does not exist in a default build.
    /// Without the gate, a plain `cargo check -p axeyum-solver --tests` fails
    /// with "cannot find `simplex` in `crate`" — which two lanes reported as a
    /// pre-existing defect on 2026-09-09. It is not one: the gate the pre-push
    /// hook runs passes `--all-features`. But a developer running the obvious
    /// command should not meet a build error, so the cfg makes the narrow
    /// invocation agree with the gate.
    #[cfg(feature = "full")]
    #[test]
    fn an_instrumented_gate_records_through_the_real_path() {
        let key = "crates/axeyum-solver/src/simplex.rs::MAX_TABLEAU_CELLS";
        assert!(
            REGISTRY.iter().any(|e| e.key() == key),
            "the key this test asserts is not registered"
        );
        {
            let _g = ConfigTraceGuard::enable();
            // A tiny, admissible system: the point is that the gate is
            // consulted, not that it refuses.
            let _ = crate::simplex::Incremental::new(1, vec![]);
            assert!(
                consulted().contains(&key),
                "simplex::Incremental::new did not record its bound; consulted = {:?}",
                consulted()
            );
        }
        // And the same call adds nothing once the guard is gone. The set is
        // NOT empty here, deliberately: it is cleared when a guard is enabled,
        // not when one is dropped, so a caller can read it after the solve it
        // was measuring. What must hold is that an unguarded call does not
        // grow it.
        let before = consulted();
        let _ = crate::simplex::Incremental::new(1, vec![]);
        let _ = crate::simplex::Incremental::new(2, vec![]);
        assert_eq!(
            consulted(),
            before,
            "an unguarded call changed the consulted set"
        );
    }

    /// The table's length must match the number of `ConfigEntry` literals in
    /// this file's own source text.
    ///
    /// Cheap, but it is the check that catches an entry lost to a bad merge:
    /// two lanes appending to one table produce a conflict where "keep both
    /// sides" can silently drop a struct literal, and nothing else here counts
    /// the literals.
    #[test]
    fn registry_len_matches_its_own_source() {
        let src = include_str!("config_registry.rs");
        // Built by concatenation so this line does not match its own pattern.
        // Written literally, it counted itself: 114 literals against 113
        // entries, a failure whose message blamed the table rather than the
        // check. A self-counting check is exactly the "what would this print if
        // it were broken?" case, and it printed a plausible off-by-one.
        let needle = concat!("    ConfigEntry", " {");
        let literals = src.matches(needle).count();
        assert_eq!(
            literals,
            REGISTRY.len(),
            "the file holds {literals} `ConfigEntry` literals but REGISTRY has {} entries",
            REGISTRY.len()
        );
    }

    /// A soundness-protecting bound must either signal its crossing or name
    /// what stops the crossing becoming a wrong verdict.
    ///
    /// The registry's own invariant, and the one that would have made
    /// `nia_linearize::MAX_CONGRUENCE_GROUPS` answerable when it was written:
    /// the question "what makes this safe?" has a required field.
    #[test]
    fn unsignalled_relaxations_name_their_guard() {
        for e in REGISTRY {
            if e.signal == Signal::None {
                assert!(
                    !e.guarded_by.is_empty(),
                    "{} crosses with no signal and names no guard",
                    e.key()
                );
            } else {
                assert!(
                    e.guarded_by.is_empty(),
                    "{} names a guard but does not have Signal::None",
                    e.key()
                );
            }
        }
    }

    /// A dated justification must parse as `YYYY-MM-DD` and rest on something.
    ///
    /// The `rests_on` requirement is the whole staleness contract: a date with
    /// no dependencies cannot go stale, so it would be a date that means
    /// nothing.
    #[test]
    fn dated_justifications_are_well_formed() {
        for e in REGISTRY {
            let Some(d) = e.justification.measured_on else {
                assert!(
                    e.justification.rests_on.is_empty(),
                    "{} has dependencies but no date to compare them against",
                    e.key()
                );
                continue;
            };
            let parts: Vec<&str> = d.split('-').collect();
            assert_eq!(parts.len(), 3, "{}: bad date {d}", e.key());
            assert!(
                parts[0].len() == 4 && parts[1].len() == 2 && parts[2].len() == 2,
                "{}: bad date {d}",
                e.key()
            );
            assert!(
                d.chars().all(|c| c.is_ascii_digit() || c == '-'),
                "{}: bad date {d}",
                e.key()
            );
            assert!(
                !e.justification.rests_on.is_empty(),
                "{} is dated but rests on nothing, so its date can never go stale",
                e.key()
            );
            for dep in e.justification.rests_on {
                assert!(
                    repo_root().join(dep.path).exists(),
                    "{} rests on a path that does not exist: {}",
                    e.key(),
                    dep.path
                );
            }
        }
    }

    /// Every dated entry must name at least one [`Basis`], and every basis must
    /// be well formed enough for `scripts/check-admission-limit-basis.py` to
    /// resolve it.
    ///
    /// This is the coverage half of the basis contract; the script is the
    /// liveness half. Neither substitutes for the other: a registry where the
    /// script passes because nothing declares a basis would be exactly the
    /// state that let `MAX_PRE_SAT_ARITH_ATOMS` cite a retired allocator for a
    /// month.
    ///
    /// The undated direction is asserted too, and for the same reason the
    /// `rests_on` version of it is: a basis with no measurement to support has
    /// nothing to be the basis *of*.
    #[test]
    fn dated_justifications_declare_a_basis() {
        let root = repo_root();
        for e in REGISTRY {
            if e.justification.measured_on.is_none() {
                assert!(
                    e.justification.basis.is_empty(),
                    "{} declares a basis but has no measurement for it to support",
                    e.key()
                );
                continue;
            }
            assert!(
                !e.justification.basis.is_empty(),
                "{} is dated but names no basis, so nothing it rests on can be \
                 shown to have disappeared",
                e.key()
            );
            for b in e.justification.basis {
                match b {
                    Basis::LiveSymbol { ident, in_path } => {
                        assert!(!ident.is_empty(), "{}: empty basis identifier", e.key());
                        assert!(
                            root.join(in_path).exists(),
                            "{} names basis symbol {ident} in {in_path}, which does not exist",
                            e.key()
                        );
                    }
                    Basis::CommitSubject {
                        sha,
                        subject_contains,
                    } => {
                        assert!(
                            sha.len() >= 7 && sha.chars().all(|c| c.is_ascii_hexdigit()),
                            "{}: {sha} is not a commit id",
                            e.key()
                        );
                        assert!(
                            !subject_contains.is_empty(),
                            "{}: a commit basis that requires nothing of the subject cannot fail",
                            e.key()
                        );
                    }
                    Basis::AdrLive(id) => {
                        assert!(
                            id.starts_with("ADR-") && id.len() > 4,
                            "{}: {id} is not an ADR id",
                            e.key()
                        );
                    }
                    Basis::DocPath(p) => {
                        assert!(
                            root.join(p).exists(),
                            "{} names document basis {p}, which does not exist",
                            e.key()
                        );
                    }
                }
            }
        }
    }

    /// A date may be added but never lost.
    ///
    /// The ratchet is on DATES rather than on the undated share on purpose:
    /// registering an unmeasured governing value is work this module wants, and
    /// it moves the share the wrong way, so a share ratchet would pay a lane to
    /// leave a bound unregistered. Losing a date is the thing that must not
    /// happen quietly — most temptingly by downgrading an entry to `undated`
    /// when its `rests_on` goes red, which turns a finding into a silence.
    #[test]
    fn the_dated_count_only_rises() {
        assert!(
            dated_count() >= DATED_FLOOR,
            "dated entries fell to {} against a floor of {DATED_FLOOR}. If a measurement was \
             genuinely re-taken and an entry is honestly undated again, lower DATED_FLOOR in the \
             same commit and say why; do not lower it to make this pass.",
            dated_count()
        );
        assert_eq!(
            dated_count() + undated_count(),
            REGISTRY.len(),
            "dated + undated must partition the table"
        );
        // The floor must track the table, or it stops being a ratchet and
        // becomes a number that was true once.
        assert!(
            dated_count() <= DATED_FLOOR + 64,
            "dated_count() is {} against a floor of {DATED_FLOOR}: raise DATED_FLOOR so the \
             ratchet keeps holding what has been achieved",
            dated_count()
        );
    }

    /// The trace line reports the undated share, not only the dated count.
    ///
    /// The share is this module's honest headline, and a headline only a
    /// checker prints is one most readers never see.
    #[test]
    fn the_trace_line_reports_what_is_unmeasured() {
        let line = config_trace_line();
        assert!(
            line.contains(&format!("undated={}", undated_count())),
            "the trace line does not report the undated count: {line}"
        );
        assert!(
            undated_count() > 0,
            "no undated entries, so this test is asserting nothing; delete it or re-derive it"
        );
    }

    /// The emitted line must be deterministic and byte-identical across calls.
    #[test]
    fn trace_line_is_deterministic() {
        let a = config_trace_line();
        let b = config_trace_line();
        assert_eq!(a, b);
        assert!(a.starts_with("; config digest="));
    }

    /// Recording is off unless a guard is constructed, and a guard restores the
    /// previous setting on drop.
    #[test]
    fn recording_is_opt_in_and_restores() {
        note_consulted("crates/axeyum-solver/src/simplex.rs::MAX_PIVOTS");
        assert!(consulted().is_empty(), "recorded with no guard active");
        {
            let _g = ConfigTraceGuard::enable();
            note_consulted("crates/axeyum-solver/src/simplex.rs::MAX_PIVOTS");
            assert_eq!(consulted().len(), 1);
        }
        note_consulted("crates/axeyum-solver/src/simplex.rs::MAX_TABLEAU_CELLS");
        assert_eq!(
            consulted().len(),
            1,
            "recording continued after the guard was dropped"
        );
    }

    /// Exemptions must name a real constant in a governed file, and must not
    /// also be registered.
    ///
    /// Without this an exemption could be a typo that silences a real gap.
    #[test]
    fn exemptions_are_real_and_disjoint() {
        let root = repo_root();
        for (module, name, reason) in EXEMPT {
            assert!(
                !reason.is_empty(),
                "{module}::{name} is exempt with no reason"
            );
            assert!(
                GOVERNED_FILES.contains(module),
                "{module}::{name} is exempt but its file is not governed"
            );
            let text = std::fs::read_to_string(root.join(module)).expect("read module");
            assert!(
                text.contains(&format!("const {name}:")),
                "{module}::{name} is exempt but no such constant exists"
            );
            assert!(
                !REGISTRY
                    .iter()
                    .any(|e| e.module == *module && e.name == *name),
                "{module}::{name} is both registered and exempt"
            );
        }
    }

    /// Every environment variable this registry NAMES must be read somewhere in
    /// the workspace's own sources.
    ///
    /// # Why this test and not a list
    ///
    /// `env_override` is the field a reader consults before running an A/B. An
    /// entry naming a variable that nothing reads is strictly worse than
    /// `None`: the operator sets it, the run proceeds on the shipped default,
    /// and the result is reported as the raised arm. So the failure this must
    /// catch is not "a lever is missing" but "a lever is *claimed*".
    ///
    /// The population is derived from [`REGISTRY`], never from a literal, so it
    /// fails equally on a variable added to the table without a read and on a
    /// read deleted from the code. `config_registry.rs` itself is excluded: it
    /// names every variable by construction, and counting it would make the
    /// check unable to fail.
    ///
    /// # Why the scope is the WORKSPACE and not the entry's own crate
    ///
    /// The narrower version was written first and failed on its first honest
    /// run, at the five `AXEYUM_MEMORY_LIMIT_MB` entries: the variable is real
    /// but is read in `crates/axeyum-bench/examples/smtcomp_cli.rs`, which
    /// turns it into a `SolverConfig` field. A lever legitimately lives at
    /// whatever layer owns the knob, so "read by its own crate" is the wrong
    /// question and would have been silenced by relaxing the claim.
    #[test]
    fn every_env_override_is_read_by_the_code() {
        let declared: BTreeSet<&'static str> =
            REGISTRY.iter().filter_map(|e| e.env_override).collect();
        assert!(
            !declared.is_empty(),
            "no entry declares an env_override, so this test measured nothing"
        );
        let read = env_vars_read_by_the_workspace(&repo_root().join("crates"), &declared);
        let missing: Vec<String> = REGISTRY
            .iter()
            .filter_map(|e| e.env_override.map(|v| (e, v)))
            .filter(|(_, var)| !read.contains(var))
            .map(|(e, var)| format!("{}: {var}", e.key()))
            .collect();
        assert!(
            missing.is_empty(),
            "registry entries name an environment variable that no workspace source reads: \
             {missing:#?}\nEither wire the lever (see `axeyum_ir::config_lever`) or set \
             `env_override: None`. A claimed lever that does nothing turns an A/B into a \
             measurement of the shipped default reported as the other arm."
        );
    }

    /// Which of `wanted` occur in a `.rs` file under `dir`.
    ///
    /// Skips this module's own source: it names every variable by construction,
    /// so including it would make the caller unable to fail. The `AXEYUM_`
    /// pre-filter keeps this one pass over ~72 MB of sources rather than one
    /// pass per variable.
    fn env_vars_read_by_the_workspace(
        dir: &Path,
        wanted: &BTreeSet<&'static str>,
    ) -> BTreeSet<&'static str> {
        let mut found = BTreeSet::new();
        let mut stack = vec![dir.to_path_buf()];
        while let Some(dir) = stack.pop() {
            let Ok(read) = std::fs::read_dir(&dir) else {
                continue;
            };
            for entry in read {
                let path = entry.expect("dir entry").path();
                if path.is_dir() {
                    if path.file_name().is_some_and(|f| f == "target") {
                        continue;
                    }
                    stack.push(path);
                    continue;
                }
                if path.extension().is_none_or(|e| e != "rs") {
                    continue;
                }
                if path.file_name().is_some_and(|f| f == "config_registry.rs") {
                    continue;
                }
                let text = std::fs::read_to_string(&path).expect("read source");
                if !text.contains("AXEYUM_") {
                    continue;
                }
                for var in wanted {
                    // The QUOTED literal, not the bare name. Written as a bare
                    // substring this check passed its own mutation: renaming
                    // `AXEYUM_BOOL_EUF_MAX_ATOMS` to `…_TYPO` at the only site
                    // that reads it left the registry's name a substring of the
                    // code's, and all 18 tests stayed green. Every read in this
                    // tree is a string literal; a doc comment naming the
                    // variable in backticks is not a read and must not count.
                    if text.contains(&format!("\"{var}\"")) {
                        found.insert(*var);
                    }
                }
            }
        }
        found
    }
}
