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
//! # Recording (off by default)
//!
//! [`ConfigTraceGuard`] follows the four opt-in, off-by-default guards this tree
//! already ships — `TheoryLayerStatsGuard`, [`crate::BvLayerStatsGuard`],
//! `DlOnlineStatsGuard`, `FrontDoorStatsGuard` — all wired to the single
//! existing `--trace` / `AXEYUM_TRACE=1` flag in `smtcomp_cli`. No new CLI
//! surface. With no guard constructed, [`note_consulted`] reads one thread-local
//! `Cell<bool>` and returns: nothing is allocated and no clock is read.

use std::cell::{Cell, RefCell};
use std::collections::BTreeSet;
use std::fmt::Write as _;

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
    }
}

/// A justification with a measurement date and the things that measurement
/// rests on.
const fn dated(
    location: &'static str,
    measured_on: &'static str,
    measured_at_commit: Option<&'static str>,
    rests_on: &'static [Dependency],
) -> Justification {
    Justification {
        location,
        measured_on: Some(measured_on),
        measured_at_commit,
        rests_on,
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
        name: "MAX_ARRAY_EQ_INDEX_BITS",
        module: "crates/axeyum-rewrite/src/arrays.rs",
        value: "8",
        unit: "index bits",
        protects: Protects::Completeness,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Bounds eager array-equality expansion over 2^iw indices and the O(n^2) Ackermann pairing behind it. Refuses as `ArrayElimError::Unsupported`.",
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
        ),
        note: "THE SIGNALLED TWIN. Crossing it is reported as `ZeroDivisorCongruence::Omitted` and `auto::guard_zero_divisor_sat` turns the resulting `sat` into `unknown`. Same name and same value as `nia_linearize::MAX_CONGRUENCE_GROUPS`, which signals nothing — see that entry.",
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
        justification: undated("doc comment"),
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
        env_override: None,
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
        justification: undated("doc comment"),
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
        name: "UF_ARITH_CEGAR_PROBE_SHARE",
        module: "crates/axeyum-solver/src/auto.rs",
        value: "2",
        unit: "divisor of the dispatcher's remaining deadline",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: Some("AXEYUM_UF_ARITH_OVERBOUND"),
        justification: dated(
            "docs/research/12-performance/uf-arith-overbound-2026-09-08.md",
            "2026-09-08",
            None,
            &[],
        ),
        note: "The lazy-Ackermann CEGAR's share of the budget on an over-bound UF+arithmetic \
               query. Before this constant existed the CEGAR took the WHOLE budget and its \
               `Unknown` was the dispatcher's final answer, so `euf-online`, `euf-offline` and \
               `dispatch_uf_arith_online` were unreachable above 64 congruence pairs. The env \
               override selects the whole policy (`terminal` restores that behaviour, `skip` \
               removes the CEGAR), not just this divisor.",
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
        note: "FINDING. `atom()` returns `None` on size, which at the call site is INDISTINGUISHABLE from `this term is not difference-shaped`. A size refusal and a structural decline share one signal, so no trace can attribute the route change to this bound. Same class as the unit mismatch ADR-1751 fixed: the gate's meaning is lost at the boundary.",
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
        signal: Signal::ToCaller,
        guarded_by: "",
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
        env_override: None,
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
        value: "1_280",
        unit: "arithmetic atoms",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "An exception rectangle carved out of the pre-SAT trigger, so a moderate query is admitted rather than refused. Names `windowreal-no_t_deadlock-17.smt2` at 0.10-0.20 s / 18 MiB, undated.",
    },
    ConfigEntry {
        name: "MAX_MODERATE_PRE_SAT_CNF_VARS",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "8_192",
        unit: "CNF variables",
        protects: Protects::Memory,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "Joint partner to the moderate atom bound; both must hold.",
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
        justification: undated("doc comment"),
        note: "Joint (AND'ed with the CNF-variable bound) admission boundary before the first SAT round. Guards a measured abort on `pursuit-safety-16.smt2` at an 8 GiB ceiling — file named, DATE ABSENT.",
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
        justification: undated("doc comment"),
        note: "Joint partner to the pre-SAT atom bound.",
    },
    ConfigEntry {
        name: "MAX_TWO_EDGE_DIFF_EDGES",
        module: "crates/axeyum-solver/src/dpll_lia.rs",
        value: "512",
        unit: "difference-logic edges",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::None,
        guarded_by: "falls through to the Bellman-Ford gate",
        env_override: None,
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
        ),
        note: "ACCOUNTING, NOT ADMISSION. Until 2026-08-21 the same constant was an admission width-gate; the doc records why that was the wrong direction. It now only decides whether a retained core counts against `MAX_DYNAMIC_LARGE_CORE_LITERALS`. Registered because a reader who greps the name will otherwise assume the old contract.",
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
        note: "Admits the eager UF-elimination route. The doc names the decidable frontier (40 pairs) and the unbounded hang (117+) with per-file counts, but NO DATE.",
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
        justification: undated("doc comment"),
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
            "2026-09-07",
            None,
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
        ),
        note: "A SCREEN, explicitly not a cost model — the doc names three replacement cost models the corpus falsified. Calibrated so the default budget reproduces the flat 1,024-atom cap byte-identically, which is why its definition divides by exactly that number.",
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
            &[
                sym(
                    "crates/axeyum-solver/src/lra_online.rs",
                    "DEFAULT_ONLINE_LRA_BUDGET_BYTES",
                ),
                sym(
                    "crates/axeyum-solver/src/lra_theory.rs",
                    "MAX_ONLINE_LRA_ATOMS",
                ),
            ],
        ),
        note: "THE REPLACEMENT for the stale flat atom cap. Used when `SolverConfig::memory_limit_mb` is unset; when it is set, that is the budget instead — so this is the first bound in the registry that MOVES with a caller-supplied resource limit rather than being fixed at compile time.",
    },
    ConfigEntry {
        name: "DEFAULT_STEP_BUDGET",
        module: "crates/axeyum-solver/src/lra_online.rs",
        value: "16_000_000",
        unit: "main-loop iterations",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
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
                sym(
                    "crates/axeyum-solver/src/lra_theory.rs",
                    "MAX_ONLINE_LRA_ATOMS",
                ),
                sym(
                    "crates/axeyum-solver/src/lra_online.rs",
                    "MAX_LRA_CACHED_COEFFICIENTS",
                ),
                sym(
                    "crates/axeyum-solver/src/lra_online.rs",
                    "DEFAULT_ONLINE_LRA_BUDGET_BYTES",
                ),
            ],
        ),
        note: "THE WORKED EXAMPLE. It is no longer the LRA route's own admission gate (ADR-1752 replaced that with a byte budget) but it IS still live as the atom ceiling `nra.rs` projects against (ADR-1751), and the byte budget is calibrated to reproduce it exactly at the default. Its `rests_on` names `MAX_LRA_CACHED_COEFFICIENTS` — the dependency whose absence let a 2026-08-03 measurement stand for thirteen months after the 2026-08-06 commit that falsified it.",
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
        ),
        note: "THE BEST-JUSTIFIED ENTRY IN THIS REGISTRY, and the model for the rest: the doc carries a table of measured peaks over `bvmul` commutativity miters, names the host, gives the date, AND ships a re-measurement test (`crates/axeyum-solver/tests/memory_budget.rs`) so the number can be re-taken rather than re-argued. Converts a byte budget into `clause_ceiling()`.",
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
        env_override: None,
        justification: undated("doc comment"),
        note: "Grants an extra slice only when envelopes were actually emitted.",
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
        env_override: None,
        justification: undated("doc comment"),
        note: "Default slice for the pre-ladder NIA relaxation so it cannot hang before the width ladder is reached.",
    },
    ConfigEntry {
        name: "POW2_TABLE_MAX_CASES",
        module: "crates/axeyum-solver/src/nia_linearize.rs",
        value: "128",
        unit: "disjunct cases in one value table",
        protects: Protects::Completeness,
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::NotApplicable,
        guarded_by: "",
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
        on_exceed: OnExceed::DeclineRoute,
        signal: Signal::ToCaller,
        guarded_by: "",
        env_override: None,
        justification: undated("doc comment"),
        note: "`pow2_value` returns `None` past it so `1 << k` stays inside `i128`.",
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
        name: "MAX_PIVOTS",
        module: "crates/axeyum-solver/src/simplex.rs",
        value: "2_000_000",
        unit: "pivot operations",
        protects: Protects::Termination,
        on_exceed: OnExceed::RefuseUnknown,
        signal: Signal::ToCaller,
        guarded_by: "",
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
        justification: undated("doc comment"),
        note: "About 128 MB at two `i128`s per cell. `Incremental::new` returns `None`, so the caller falls back to Fourier-Motzkin. Deterministic (no clock, no resident-set probe), which is what lets it be part of a reproducible verdict.",
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
    "crates/axeyum-solver/src/lra_online.rs",
    "crates/axeyum-solver/src/lra_theory.rs",
    "crates/axeyum-solver/src/memory_budget.rs",
    "crates/axeyum-solver/src/nia_linearize.rs",
    "crates/axeyum-solver/src/nra.rs",
    "crates/axeyum-solver/src/simplex.rs",
];

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
        ConfigTraceGuard(RECORD_CONFIG.with(|c| c.replace(true)))
    }
}

impl Drop for ConfigTraceGuard {
    fn drop(&mut self) {
        RECORD_CONFIG.with(|c| c.set(self.0));
    }
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
    CONSULTED.with(|c| {
        c.borrow_mut().insert(key);
    });
}

/// The keys consulted on this thread since the active guard was constructed,
/// sorted.
#[must_use]
pub fn consulted() -> Vec<&'static str> {
    CONSULTED.with(|c| c.borrow().iter().copied().collect())
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

/// The one-line configuration summary a `--trace` run prints.
///
/// Deliberately one line and digest-first: a corpus sweep's output is grepped,
/// and a per-run dump of 113 entries would not be. The full table is available
/// through [`REGISTRY`] and from `scripts/check-config-registry-staleness.py`.
#[must_use]
pub fn config_trace_line() -> String {
    let mut s = format!(
        "; config digest={:016x} entries={} dated={}",
        digest(),
        REGISTRY.len(),
        dated_count()
    );
    for (k, v) in active_env_overrides() {
        let _ = write!(s, " env:{k}={v}");
    }
    let consulted = consulted();
    if !consulted.is_empty() {
        let _ = write!(s, " consulted={}", consulted.len());
        for key in consulted {
            s.push(' ');
            s.push_str(key);
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
                // Match `note_consulted(` followed by a string literal, across
                // the line break rustfmt inserts for a long key.
                let mut rest = text.as_str();
                while let Some(at) = rest.find("note_consulted(") {
                    rest = &rest[at + "note_consulted(".len()..];
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
        assert!(
            bad.is_empty(),
            "note_consulted keys that are not registered: {bad:#?}"
        );
        // A scan that found nothing would pass vacuously, which is the failure
        // mode this repository has been bitten by most often.
        assert!(
            sites >= 4,
            "expected the instrumented gates to be found; the scan saw {sites} \
             call site(s), so it is passing vacuously"
        );
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
}
