//! The `QF_UFLIA` online combination's **interface layer**: which shared-term
//! pairs it proposes, and clock-free counters saying what happened to them.
//!
//! ## Why this module exists
//!
//! The online model-based EUF + linear-integer combination
//! ([`crate::uflia_online`]) is the route whose architecture matches what Z3
//! (`setup_QF_UFLIA` → `theory_lra` over native congruence closure) and cvc5
//! (`--ackermann` off, force-disabled with UF present) actually run for this
//! logic. On 2026-09-08 it was made *reachable* on the losing `QF_UFLIA`
//! population for the first time
//! ([`uf-arith-overbound-2026-09-08`](../../../docs/research/12-performance/uf-arith-overbound-2026-09-08.md)).
//!
//! Being reachable is not the same as running. The interface pair set is
//! built ALL-PAIRS — every unordered pair of atomic integer terms with at least
//! one EUF endpoint ([`crate::uflia_online::interface_pairs`]) — and then a
//! single ceiling of 64 decides whether the route runs **at all**:
//! `uflia_online::MAX_SPLIT_DEPTH` in the conjunctive core and
//! `combined_theory_lia::MAX_SPLIT_PAIRS` in the Boolean CDCL(T) driver. Because
//! the set is quadratic in the number of interface terms, 64 pairs is about
//! **twelve** shared integer terms; above that the route declines before
//! deciding anything.
//!
//! Nothing in `--trace` could say whether that was happening: the online UFLIA
//! layer had no counters at all, and the two cap declines report themselves
//! through strings that name neither the bound nor its value (measured in this
//! lane: `combined_theory_lia.rs`'s `None` surfaces as "incremental combined
//! state could not be built safely", which reads as a modelling gap). This
//! module supplies the missing measurement and makes the pair set a **policy**
//! so the ceiling can be answered with something other than a decline.
//!
//! ## What the references do instead, and what we can copy
//!
//! - **cvc5** builds a *care graph*: it proposes an interface equality only for
//!   a pair that could fire a congruence — corresponding arguments of two
//!   applications of the same function. [`UfliaInterfacePolicy::CareGraph`] is
//!   that filter, restricted to pairs the existing code already proposes, so it
//!   can only ever shrink the set.
//! - **Z3** randomises each coinciding shared variable inside its slack before
//!   proposing an equality, so only *forced* coincidences survive. That filter
//!   is **not available at this point in our architecture** and saying so is a
//!   finding, not an omission: we materialise the `eq`/`lt`/`gt` interface atoms
//!   up front, at combined-state construction, before any literal is asserted
//!   and therefore before any model exists to randomise. Z3 filters at final
//!   check, where it has one. Adopting it here means moving interface atoms to
//!   dynamic registration at final check, which is a different slice.
//!
//! ## Soundness of dropping a pair
//!
//! Every policy here only ever REMOVES pairs from the proposal, and that is
//! sound in both directions — which is what makes an experimental policy safe
//! to ship behind a default:
//!
//! - **`sat` cannot become wrong.** A leaf model is accepted only after it
//!   replays against the original literals
//!   (`uflia_online::Search::leaf` → `replays_literals`, and the Boolean
//!   layer's `replays_assertions`). A model assembled under a coarser
//!   arrangement either replays or is declined.
//! - **`unsat` cannot become wrong.** Each dropped pair removes the forced
//!   `s = t` / `s < t` / `s > t` from the LIA side and the corresponding
//!   arrangement fact from the EUF side, so every explored branch is a
//!   RELAXATION of the branches it stands for. If all coarse branches are
//!   infeasible, so is every fine branch inside them.
//!
//! What a filter costs is **completeness**: an arrangement that would have been
//! separated is not, and the search reports `Unknown`. Against a cap that
//! declines outright at 65 pairs, more `Unknown` is not the relevant comparison
//! — today the route returns `Unknown` for the whole query.
//!
//! ## Cost when off
//!
//! One thread-local `Cell<bool>` read per recording site; no clock read, no
//! allocation. Same shape as [`crate::UfArithOverboundStats`] and
//! [`crate::LiaCounters`], which `--trace` already composes. Nothing here is
//! read by the search, so no verdict can depend on whether a guard is armed.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{FuncId, Op, TermArena, TermId, TermNode};

/// Which interface pairs the `QF_UFLIA` online combination proposes, and what it
/// does when the proposal exceeds the split ceiling.
///
/// Selected by `AXEYUM_UFLIA_INTERFACE_PAIRS` (`all` / `care` / `care-truncate`)
/// or, in-process, by [`UfliaInterfacePolicyGuard`], so the arms can be A/B-ed on
/// ONE binary rather than on one build per arm. An unset or unrecognised value is
/// the default; `all` names the historical behaviour explicitly, so a bisect
/// against it is one environment variable rather than a build.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum UfliaInterfacePolicy {
    /// Every unordered pair of atomic integer terms with at least one EUF
    /// endpoint, and a **decline** when there are more than the ceiling. The
    /// historical behaviour, kept as a named arm so the change is measured
    /// against it rather than only remembered.
    All,
    /// cvc5's care graph: keep only a pair that could fire a congruence —
    /// corresponding arguments of two applications of the same function at the
    /// same arity. Still declines when the filtered set is over the ceiling.
    CareGraph,
    /// The care graph, and when it is still over the ceiling, keep the first
    /// [`MAX_INTERFACE_PAIRS`] in the deterministic care order instead of
    /// declining. Sound in both directions (see the module docs); incomplete by
    /// construction, which is the trade being made.
    ///
    /// **The default since 2026-09-08 (ADR-1801).** On the committed 200-file
    /// `QF_UFLIA` list, with the Boolean-layer atom ceiling also raised, this arm
    /// decides 31 of the 50 files we lose against 14 for `All`, and loses none.
    /// On its own — atom ceiling unchanged — it decides one, because the atom
    /// ceiling refuses those queries before the interface layer is reached; the
    /// two changes are not independent and neither is sufficient.
    #[default]
    CareGraphTruncate,
}

impl UfliaInterfacePolicy {
    /// The short name this policy is selected by and reported as.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::All => "all",
            Self::CareGraph => "care",
            Self::CareGraphTruncate => "care-truncate",
        }
    }

    /// Whether an over-ceiling proposal is truncated rather than declined.
    #[must_use]
    pub const fn truncates(self) -> bool {
        matches!(self, Self::CareGraphTruncate)
    }

    /// Whether the care-graph filter is applied.
    #[must_use]
    pub const fn filters(self) -> bool {
        matches!(self, Self::CareGraph | Self::CareGraphTruncate)
    }
}

/// The ceiling on proposed interface pairs, shared by the conjunctive core and
/// the Boolean CDCL(T) driver.
///
/// **This is the same number as `uflia_online::MAX_SPLIT_DEPTH` and
/// `combined_theory_lia::MAX_SPLIT_PAIRS`, and that is the point.** The config
/// registry recorded those (with `uflra_online::MAX_SPLIT_DEPTH` and
/// `combined_theory::MAX_SPLIT_PAIRS`) as *four unlinked copies of one bound* —
/// same value, same intended meaning, byte-identical doc comments, no code-level
/// link. The two on the `QF_UFLIA` path now read this constant, so a change to
/// the ceiling can no longer move one and leave the other.
///
/// Kept at 64 by this lane rather than raised: the pair count is QUADRATIC in
/// the interface-term count, so raising it trades an admission decline for a
/// `3^k` search, and the measurement this lane took says the losing population
/// is one to two orders of magnitude over the ceiling — a raise big enough to
/// admit those files is not a raise, it is the removal of a termination bound.
/// The filter is the lever; the ceiling stays.
pub const MAX_INTERFACE_PAIRS: usize = 64;

std::thread_local! {
    /// A per-thread override of the process policy, set by
    /// [`UfliaInterfacePolicyGuard`]. It exists because the process policy is
    /// read once from the environment: without it, no test could exercise more
    /// than one arm in a process.
    static UFLIA_INTERFACE_OVERRIDE: Cell<Option<UfliaInterfacePolicy>> = const { Cell::new(None) };
}

/// Forces `policy` on this thread for the lifetime of the guard, restoring the
/// previous setting on drop.
pub struct UfliaInterfacePolicyGuard(Option<UfliaInterfacePolicy>);

impl UfliaInterfacePolicyGuard {
    /// Overrides the process policy on this thread.
    #[must_use]
    pub fn set(policy: UfliaInterfacePolicy) -> Self {
        UfliaInterfacePolicyGuard(UFLIA_INTERFACE_OVERRIDE.with(|c| c.replace(Some(policy))))
    }
}

impl Drop for UfliaInterfacePolicyGuard {
    fn drop(&mut self) {
        UFLIA_INTERFACE_OVERRIDE.with(|c| c.set(self.0));
    }
}

/// The [`UfliaInterfacePolicy`] in force on this thread: a live
/// [`UfliaInterfacePolicyGuard`]'s choice, else the process policy resolved once
/// from `AXEYUM_UFLIA_INTERFACE_PAIRS`. An unset or unrecognised value is the
/// default, so a typo degrades to the shipped behaviour rather than to an arm
/// nobody chose.
#[must_use]
pub fn uflia_interface_policy() -> UfliaInterfacePolicy {
    static RESOLVED: std::sync::OnceLock<UfliaInterfacePolicy> = std::sync::OnceLock::new();
    if let Some(policy) = UFLIA_INTERFACE_OVERRIDE.with(Cell::get) {
        return policy;
    }
    *RESOLVED.get_or_init(
        || match std::env::var("AXEYUM_UFLIA_INTERFACE_PAIRS").as_deref() {
            Ok("all") => UfliaInterfacePolicy::All,
            Ok("care") => UfliaInterfacePolicy::CareGraph,
            _ => UfliaInterfacePolicy::CareGraphTruncate,
        },
    )
}

/// The **care graph** over `assertions`: the unordered pairs `(a, b)` of atomic
/// integer terms that occupy the SAME argument position of two applications of
/// the same uninterpreted function at the same arity.
///
/// These are exactly the equalities whose truth could fire a new congruence, and
/// therefore the only ones whose case-split can change the EUF arrangement. Any
/// other pair in the all-pairs proposal is a split the search pays three
/// branches for and learns nothing from.
///
/// Deterministic: applications are collected in a [`BTreeSet`]-ordered walk and
/// the result is a sorted set, so the order is stable across runs (a public API
/// promise — no hash-map iteration order in output).
#[must_use]
pub fn care_graph_pairs(arena: &TermArena, roots: &[TermId]) -> BTreeSet<(TermId, TermId)> {
    // (function, arity) -> the argument tuples of its applications.
    let mut groups: BTreeMap<(FuncId, usize), Vec<Vec<TermId>>> = BTreeMap::new();
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if let Op::Apply(func) = op {
                groups
                    .entry((*func, args.len()))
                    .or_default()
                    .push(args.to_vec());
            }
            stack.extend(args.iter().copied());
        }
    }

    let mut pairs: BTreeSet<(TermId, TermId)> = BTreeSet::new();
    for tuples in groups.values() {
        for i in 0..tuples.len() {
            for j in (i + 1)..tuples.len() {
                for (&a, &b) in tuples[i].iter().zip(tuples[j].iter()) {
                    if a == b {
                        continue;
                    }
                    pairs.insert(if a < b { (a, b) } else { (b, a) });
                }
            }
        }
    }
    pairs
}

/// `n` as a `u32`, saturating at [`u32::MAX`] rather than truncating.
///
/// These fields are `pairs_max_*`, whose whole job is to say how far over the
/// ceiling a proposal was. A wrapping cast would report a 4-billion-and-one pair
/// proposal as `1`, i.e. as comfortably inside a ceiling of 64 — a counter that
/// reads as the opposite of the truth at exactly the size that would matter
/// most. Saturating is the only reading that stays honest at the top.
fn saturating_u32(n: usize) -> u32 {
    u32::try_from(n).unwrap_or(u32::MAX)
}

/// Applies the thread's [`UfliaInterfacePolicy`] to an all-pairs proposal.
///
/// `proposed` is the set [`crate::uflia_online::interface_pairs`] built;
/// `roots` are the terms the care graph is read off. Returns `None` when the
/// resulting set is still over [`MAX_INTERFACE_PAIRS`] and the policy declines
/// rather than truncates — the caller then reports its own cap decline, exactly
/// as it did before this module existed.
///
/// Recording is a side effect only: the returned set is a pure function of
/// `proposed`, `roots` and the policy, so no verdict can depend on whether a
/// counter guard is armed.
#[must_use]
pub fn apply_interface_policy(
    arena: &TermArena,
    roots: &[TermId],
    proposed: Vec<(TermId, TermId)>,
) -> Option<Vec<(TermId, TermId)>> {
    let policy = uflia_interface_policy();
    let before = proposed.len();
    let mut kept = proposed;
    let mut filtered = 0usize;
    if policy.filters() && before > MAX_INTERFACE_PAIRS {
        // Only pay for the care graph when the ceiling would otherwise bite:
        // under the ceiling the all-pairs set already runs, and shrinking it
        // there would trade completeness for nothing.
        let care = care_graph_pairs(arena, roots);
        let after: Vec<(TermId, TermId)> = kept
            .into_iter()
            .filter(|&(s, t)| care.contains(&(s, t)) || care.contains(&(t, s)))
            .collect();
        filtered = before - after.len();
        kept = after;
    }
    let mut truncated = 0usize;
    if kept.len() > MAX_INTERFACE_PAIRS {
        if !policy.truncates() {
            note_admission(|c| {
                c.proposals = c.proposals.saturating_add(1);
                c.pairs_proposed = c.pairs_proposed.saturating_add(before as u64);
                c.pairs_max_proposed = c.pairs_max_proposed.max(saturating_u32(before));
                c.care_filtered = c.care_filtered.saturating_add(filtered as u64);
                c.pair_cap_declines = c.pair_cap_declines.saturating_add(1);
            });
            return None;
        }
        truncated = kept.len() - MAX_INTERFACE_PAIRS;
        kept.truncate(MAX_INTERFACE_PAIRS);
    }
    let after = kept.len();
    note_admission(|c| {
        c.proposals = c.proposals.saturating_add(1);
        c.pairs_proposed = c.pairs_proposed.saturating_add(before as u64);
        c.pairs_kept = c.pairs_kept.saturating_add(after as u64);
        c.pairs_max_proposed = c.pairs_max_proposed.max(saturating_u32(before));
        c.pairs_max_kept = c.pairs_max_kept.max(saturating_u32(after));
        c.care_filtered = c.care_filtered.saturating_add(filtered as u64);
        c.truncated = c.truncated.saturating_add(truncated as u64);
    });
    Some(kept)
}

/// Clock-free counters for the `QF_UFLIA` online combination's interface layer.
///
/// Every field is a count, never a duration: timing for the route as a whole is
/// already carried by [`crate::RouteTrace`]'s `bound_ms`, and a second clock here
/// would only give a reader two numbers to reconcile.
///
/// [`Self::proposals`] is the **entry counter**: it is incremented before any
/// other field can move, so a zero elsewhere in a snapshot with `proposals > 0`
/// means "that code ran and counted nothing", while `proposals == 0` means the
/// interface layer was never reached. The line is printed only when
/// `proposals > 0` for exactly that reason — an all-zero row on every non-UFLIA
/// file would be three different statements wearing the same eight bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub struct UfliaInterfaceCounters {
    /// Calls into the online `QF_UFLIA` combination — the entry counter for
    /// every other field.
    ///
    /// This is deliberately the OUTERMOST site, not the interface-pair
    /// proposal, and the reason is the measurement that produced this module:
    /// on 40 of the 44 timed-out `QF_UFLIA` losses (2026-09-08) the route
    /// declines on an **admission** cap and never reaches the interface layer
    /// at all. A counter whose entry site is the pair proposal prints nothing
    /// on exactly the population it exists to explain.
    pub entries: u32,
    /// The largest theory-atom set the Boolean layer was offered, against
    /// `uflia_online::MAX_BOOLEAN_ATOMS` (512, raisable by
    /// `AXEYUM_UFLIA_MAX_BOOLEAN_ATOMS`).
    pub atoms_max: u32,
    /// Declines at the Boolean-layer theory-atom ceiling.
    pub atom_cap_declines: u32,
    /// Declines at the opaque-application theory-atom ceiling
    /// (`MAX_OPAQUE_BOOLEAN_ATOMS`, 128).
    pub opaque_atom_cap_declines: u32,
    /// Declines because the incremental combined state could not be built —
    /// the site whose four causes used to share one string.
    pub combined_build_declines: u32,
    /// Declines at the Tseitin clause ceiling (`MAX_BOOLEAN_CLAUSES`).
    pub clause_cap_declines: u32,
    /// Declines at the enumerative propositional-model ceiling
    /// (`MAX_BOOLEAN_MODELS`).
    pub model_cap_declines: u32,
    /// Interface pair sets built.
    pub proposals: u32,
    /// Pairs the all-pairs rule proposed, summed over [`Self::proposals`].
    pub pairs_proposed: u64,
    /// Pairs that survived the policy and became `eq`/`lt`/`gt` atoms.
    pub pairs_kept: u64,
    /// The largest single all-pairs proposal, so a mean cannot hide a file that
    /// is one order of magnitude over the ceiling behind one that is at it.
    pub pairs_max_proposed: u32,
    /// The largest single surviving set.
    pub pairs_max_kept: u32,
    /// Pairs dropped by the care-graph filter.
    pub care_filtered: u64,
    /// Pairs dropped by truncation at [`MAX_INTERFACE_PAIRS`].
    pub truncated: u64,
    /// Proposals that were over the ceiling and DECLINED — the count of times
    /// the whole route gave up without deciding anything. A nonzero value on a
    /// division we lose is the signal this module exists for.
    pub pair_cap_declines: u32,
    /// Interface DFS nodes entered.
    pub split_nodes: u64,
    /// DFS nodes where the EUF side already entailed the equality (one branch).
    pub split_entailed: u64,
    /// DFS nodes where the EUF side already refuted it (one branch).
    pub split_refuted: u64,
    /// DFS nodes where neither held, so the node really branched three ways.
    /// The difference between this and [`Self::split_nodes`] is how much of the
    /// split is doing work rather than being walked past.
    pub split_undetermined: u64,
    /// The deepest `forced` stack reached.
    pub split_max_depth: u32,
    /// Times the DFS hit the depth ceiling and declined.
    pub depth_cap_hits: u32,
    /// Times a DFS node stopped because the wall-clock deadline had passed.
    pub deadline_hits: u32,
    /// Leaves reached (a complete arrangement, both theories consistent).
    pub leaves: u64,
    /// Leaves whose combined model could not be built.
    pub leaf_model_build_failures: u64,
    /// Leaves whose combined model did not replay against the original literals.
    pub leaf_replay_failures: u64,
}

impl UfliaInterfaceCounters {
    /// The all-zero counters, so the thread-local can be a `const` initializer.
    const ZERO: Self = Self {
        entries: 0,
        atoms_max: 0,
        atom_cap_declines: 0,
        opaque_atom_cap_declines: 0,
        combined_build_declines: 0,
        clause_cap_declines: 0,
        model_cap_declines: 0,
        proposals: 0,
        pairs_proposed: 0,
        pairs_kept: 0,
        pairs_max_proposed: 0,
        pairs_max_kept: 0,
        care_filtered: 0,
        truncated: 0,
        pair_cap_declines: 0,
        split_nodes: 0,
        split_entailed: 0,
        split_refuted: 0,
        split_undetermined: 0,
        split_max_depth: 0,
        depth_cap_hits: 0,
        deadline_hits: 0,
        leaves: 0,
        leaf_model_build_failures: 0,
        leaf_replay_failures: 0,
    };

    /// Whether the interface layer was reached at all on this thread. The gate
    /// every reporter should use before printing [`Self::trace_line`].
    #[must_use]
    pub const fn engaged(&self) -> bool {
        self.entries > 0
    }

    /// One `;`-prefixed `--trace` line, in the `key=value` shape every other
    /// instrument in this tree prints.
    #[must_use]
    pub fn trace_line(&self) -> String {
        format!(
            "; uflia-interface policy={} cap={} entries={} atoms_max={} atom_cap_declines={} \
             opaque_atom_cap_declines={} combined_build_declines={} clause_cap_declines={} \
             model_cap_declines={} proposals={} pairs_proposed={} pairs_kept={} \
             pairs_max_proposed={} pairs_max_kept={} care_filtered={} truncated={} \
             pair_cap_declines={} split_nodes={} split_entailed={} split_refuted={} \
             split_undetermined={} split_max_depth={} depth_cap_hits={} deadline_hits={} \
             leaves={} leaf_model_build_failures={} leaf_replay_failures={}",
            uflia_interface_policy().name(),
            MAX_INTERFACE_PAIRS,
            self.entries,
            self.atoms_max,
            self.atom_cap_declines,
            self.opaque_atom_cap_declines,
            self.combined_build_declines,
            self.clause_cap_declines,
            self.model_cap_declines,
            self.proposals,
            self.pairs_proposed,
            self.pairs_kept,
            self.pairs_max_proposed,
            self.pairs_max_kept,
            self.care_filtered,
            self.truncated,
            self.pair_cap_declines,
            self.split_nodes,
            self.split_entailed,
            self.split_refuted,
            self.split_undetermined,
            self.split_max_depth,
            self.depth_cap_hits,
            self.deadline_hits,
            self.leaves,
            self.leaf_model_build_failures,
            self.leaf_replay_failures,
        )
    }
}

std::thread_local! {
    /// Whether interface counters are being collected on this thread.
    static COLLECT_UFLIA_INTERFACE: Cell<bool> = const { Cell::new(false) };
    /// The counters accumulated since the active guard was created.
    static UFLIA_INTERFACE_COUNTERS: Cell<UfliaInterfaceCounters> =
        const { Cell::new(UfliaInterfaceCounters::ZERO) };
    /// Recording calls since the guard was constructed, for the mirror cadence.
    static UFLIA_INTERFACE_RECORDS: Cell<u64> = const { Cell::new(0) };
}

/// How many recording calls pass between mirror flushes.
///
/// The DFS records once per node, so unlike
/// [`crate::UfArithOverboundStats`] — reached a handful of times per query —
/// this instrument IS on a loop and cannot afford to republish per event. Same
/// choice, and the same number, as `crate::LiaCounters`' cadence: often enough
/// that a reading taken at an arbitrary watchdog kill is close to current, rare
/// enough that the publish is never on the hot path.
const LIVE_MIRROR_RECORDS: u64 = 1_024;

/// Enables interface counter collection on this thread for the lifetime of the
/// guard, resetting the counters on construction and restoring the previous
/// setting on drop.
pub struct UfliaInterfaceCountersGuard(bool);

impl UfliaInterfaceCountersGuard {
    /// Enables collection for the lifetime of the returned guard.
    #[must_use]
    pub fn enable() -> Self {
        let previous = COLLECT_UFLIA_INTERFACE.with(|c| c.replace(true));
        UFLIA_INTERFACE_COUNTERS.with(|c| c.set(UfliaInterfaceCounters::ZERO));
        UFLIA_INTERFACE_RECORDS.with(|c| c.set(0));
        UfliaInterfaceCountersGuard(previous)
    }
}

impl Drop for UfliaInterfaceCountersGuard {
    /// Restores the previous setting and publishes the finished counters. The
    /// only COMPLETE publish point this instrument has: its fields accumulate
    /// across the whole solve rather than being lifted at a stage boundary.
    fn drop(&mut self) {
        COLLECT_UFLIA_INTERFACE.with(|c| c.set(self.0));
        crate::live_instruments::publish_live(
            crate::live_instruments::instrument::UFLIA_INTERFACE,
            UFLIA_INTERFACE_COUNTERS.with(Cell::get),
            crate::live_instruments::Sampled::Complete,
        );
    }
}

/// The counters accumulated on this thread since the active
/// [`UfliaInterfaceCountersGuard`] (or the most recently dropped one) was
/// created. All-zero means either "collection was never enabled" or "the online
/// UFLIA interface layer was never reached" — the caller knows which, because it
/// decides whether to construct the guard, and
/// [`UfliaInterfaceCounters::engaged`] distinguishes the second case.
#[must_use]
pub fn last_uflia_interface_counters() -> UfliaInterfaceCounters {
    UFLIA_INTERFACE_COUNTERS.with(Cell::get)
}

/// Applies `f` to this thread's counters when collection is enabled; otherwise
/// reads one `Cell<bool>` and returns.
///
/// For the **loop** sites (the interface DFS, which records once per node). The
/// live board is refreshed on the [`LIVE_MIRROR_RECORDS`] cadence, so a
/// watchdog kill reads a lower bound rather than nothing.
pub(crate) fn note(f: impl FnOnce(&mut UfliaInterfaceCounters)) {
    record(f, false);
}

/// [`note`], but refreshes the live board on **every** call.
///
/// For the admission sites — the route entry and the cap declines — which are
/// reached a handful of times per query and never inside a loop, so there is no
/// cadence to amortize. This is not a nicety: on the `QF_UFLIA` losses the
/// online combination declines in well under a millisecond and the process is
/// then killed by the watchdog twenty-four seconds later, so a cadence-only
/// publish leaves the board EMPTY on exactly the population the instrument
/// exists to explain — measured, before this split, as no `; uflia-interface`
/// line at all on a file whose whole story is one admission decline. Same
/// reasoning, and the same shape, as `crate::UfArithOverboundStats`.
pub(crate) fn note_admission(f: impl FnOnce(&mut UfliaInterfaceCounters)) {
    record(f, true);
}

fn record(f: impl FnOnce(&mut UfliaInterfaceCounters), always_publish: bool) {
    if !COLLECT_UFLIA_INTERFACE.with(Cell::get) {
        return;
    }
    let counters = UFLIA_INTERFACE_COUNTERS.with(|c| {
        let mut counters = c.get();
        f(&mut counters);
        c.set(counters);
        counters
    });
    let records = UFLIA_INTERFACE_RECORDS.with(|c| {
        let next = c.get().wrapping_add(1);
        c.set(next);
        next
    });
    if always_publish || records.is_multiple_of(LIVE_MIRROR_RECORDS) {
        crate::live_instruments::publish_live(
            crate::live_instruments::instrument::UFLIA_INTERFACE,
            counters,
            // Partial: the search has not returned, so every field is a lower
            // bound and any ratio of two of them is not the finished ratio.
            crate::live_instruments::Sampled::InFlight,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Sort;

    fn int(arena: &mut TermArena, name: &str) -> TermId {
        arena.int_var(name).expect("int var")
    }

    fn sum(arena: &mut TermArena, terms: &[TermId]) -> TermId {
        let mut acc = terms[0];
        for &t in &terms[1..] {
            acc = arena.int_add(acc, t).expect("int add");
        }
        acc
    }

    /// The care graph keeps corresponding arguments of two applications of the
    /// same function and nothing else. `f(x)` / `f(y)` contributes `(x, y)`;
    /// `g(z)` has one application, so it contributes nothing.
    #[test]
    fn care_graph_is_corresponding_arguments_of_one_function() {
        let mut arena = TermArena::new();
        let fun_f = arena.declare_fun("f", &[Sort::Int], Sort::Int).expect("f");
        let fun_g = arena.declare_fun("g", &[Sort::Int], Sort::Int).expect("g");
        let arg_x = int(&mut arena, "x");
        let arg_y = int(&mut arena, "y");
        let arg_z = int(&mut arena, "z");
        let fx = arena.apply(fun_f, &[arg_x]).expect("f(x)");
        let fy = arena.apply(fun_f, &[arg_y]).expect("f(y)");
        let gz = arena.apply(fun_g, &[arg_z]).expect("g(z)");
        let root = sum(&mut arena, &[fx, fy, gz]);

        let care = care_graph_pairs(&arena, &[root]);
        let expected = if arg_x < arg_y {
            (arg_x, arg_y)
        } else {
            (arg_y, arg_x)
        };
        assert!(
            care.contains(&expected),
            "f's two arguments are a care pair"
        );
        assert_eq!(
            care.len(),
            1,
            "g has one application, so it contributes no pair: {care:?}"
        );
    }

    /// The care graph pairs CORRESPONDING argument positions, not any two
    /// arguments of two applications: `f(a, b)` and `f(c, d)` give `(a, c)` and
    /// `(b, d)`, never `(a, d)` or `(b, c)`.
    ///
    /// Written from the mutation battery, which found that reversing the
    /// position zip killed nothing — every other care-graph test used a UNARY
    /// function, where reversal is the identity. A congruence fires only when
    /// EVERY position agrees, so a graph that proposes a cross-position
    /// equality is proposing a split that can never fire one.
    #[test]
    fn care_pairs_are_position_wise_not_any_two_arguments() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::Int, Sort::Int], Sort::Int)
            .expect("f");
        let arg_a = int(&mut arena, "a");
        let arg_b = int(&mut arena, "b");
        let arg_c = int(&mut arena, "c");
        let arg_d = int(&mut arena, "d");
        let fab = arena.apply(f, &[arg_a, arg_b]).expect("f(a,b)");
        let fcd = arena.apply(f, &[arg_c, arg_d]).expect("f(c,d)");
        let root = sum(&mut arena, &[fab, fcd]);

        let care = care_graph_pairs(&arena, &[root]);
        let key = |x: TermId, y: TermId| if x < y { (x, y) } else { (y, x) };
        assert!(
            care.contains(&key(arg_a, arg_c)),
            "position 0 pairs with position 0"
        );
        assert!(
            care.contains(&key(arg_b, arg_d)),
            "position 1 pairs with position 1"
        );
        assert!(
            !care.contains(&key(arg_a, arg_d)) && !care.contains(&key(arg_b, arg_c)),
            "a cross-position pair can never fire a congruence: {care:?}"
        );
        assert_eq!(care.len(), 2);
    }

    /// Two applications at DIFFERENT arities cannot be congruent, so they share
    /// no care pair. A `zip` over the shorter tuple would silently pair position
    /// 0 of a unary application with position 0 of a binary one.
    #[test]
    fn different_arities_share_no_care_pair() {
        let mut arena = TermArena::new();
        let f1 = arena
            .declare_fun("f1", &[Sort::Int], Sort::Int)
            .expect("f1");
        let f2 = arena
            .declare_fun("f2", &[Sort::Int, Sort::Int], Sort::Int)
            .expect("f2");
        let x = int(&mut arena, "x");
        let y = int(&mut arena, "y");
        let a = arena.apply(f1, &[x]).expect("f1(x)");
        let b = arena.apply(f2, &[y, y]).expect("f2(y,y)");
        let root = sum(&mut arena, &[a, b]);
        assert!(
            care_graph_pairs(&arena, &[root]).is_empty(),
            "distinct functions and arities cannot fire a congruence together"
        );
    }

    /// Builds `n` applications of one unary function and returns the all-pairs
    /// proposal over their arguments plus the root term the care graph is read
    /// off.
    fn unary_family(n: usize) -> (TermArena, TermId, Vec<(TermId, TermId)>) {
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).expect("f");
        let mut apps = Vec::new();
        let mut args = Vec::new();
        for i in 0..n {
            let v = arena.int_var(&format!("x{i}")).expect("int var");
            args.push(v);
            apps.push(arena.apply(f, &[v]).expect("f(x)"));
        }
        let root = sum(&mut arena, &apps);
        let mut proposed = Vec::new();
        for i in 0..args.len() {
            for j in (i + 1)..args.len() {
                proposed.push((args[i], args[j]));
            }
        }
        (arena, root, proposed)
    }

    /// The `All` policy is the historical behaviour: nothing is filtered, and an
    /// over-ceiling proposal declines.
    #[test]
    fn all_policy_declines_over_the_ceiling_and_filters_nothing() {
        let _guard = UfliaInterfacePolicyGuard::set(UfliaInterfacePolicy::All);
        let (arena, root, proposed) = unary_family(4);
        let under = proposed.len();
        assert!(under <= MAX_INTERFACE_PAIRS);
        let kept = apply_interface_policy(&arena, &[root], proposed).expect("under the ceiling");
        assert_eq!(kept.len(), under, "`all` filters nothing under the ceiling");

        let (arena, root, proposed) = unary_family(40);
        assert!(proposed.len() > MAX_INTERFACE_PAIRS);
        assert!(
            apply_interface_policy(&arena, &[root], proposed).is_none(),
            "over the ceiling, `all` declines"
        );
    }

    /// `care-truncate` returns a set at the ceiling instead of declining, which
    /// is the whole point of the arm: the route runs where `all` gives up.
    #[test]
    fn care_truncate_returns_a_capped_set_instead_of_declining() {
        let _guard = UfliaInterfacePolicyGuard::set(UfliaInterfacePolicy::CareGraphTruncate);
        let (arena, root, proposed) = unary_family(40);
        assert!(proposed.len() > MAX_INTERFACE_PAIRS);
        let kept = apply_interface_policy(&arena, &[root], proposed)
            .expect("care-truncate never declines on size");
        assert_eq!(kept.len(), MAX_INTERFACE_PAIRS);
    }

    /// The care filter keeps only pairs the care graph contains. Here every
    /// argument pair IS a care pair (one unary function over all of them), so
    /// `care` alone still declines — the filter is not a licence to assume it
    /// always shrinks the set, and this is the case that proves it.
    #[test]
    fn care_alone_still_declines_when_every_pair_is_a_care_pair() {
        let _guard = UfliaInterfacePolicyGuard::set(UfliaInterfacePolicy::CareGraph);
        let (arena, root, proposed) = unary_family(40);
        assert!(
            apply_interface_policy(&arena, &[root], proposed).is_none(),
            "a care graph that keeps everything cannot get under the ceiling"
        );
    }

    /// The filter DOES shrink the set when the interface carries terms no
    /// congruence can use: 40 unary applications plus 20 bare LIA-only integer
    /// symbols. The all-pairs rule proposes every cross pair; the care graph
    /// keeps only the argument pairs.
    #[test]
    fn care_filter_drops_pairs_no_congruence_can_use() {
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).expect("f");
        let a = arena.int_var("a").expect("a");
        let b = arena.int_var("b").expect("b");
        let fa = arena.apply(f, &[a]).expect("f(a)");
        let fb = arena.apply(f, &[b]).expect("f(b)");
        let c = arena.int_var("c").expect("c");
        let root = sum(&mut arena, &[fa, fb, c]);
        let care = care_graph_pairs(&arena, &[root]);
        let ab = if a < b { (a, b) } else { (b, a) };
        assert_eq!(care.len(), 1);
        assert!(care.contains(&ab));
        for other in [(a, c), (b, c)] {
            let key = if other.0 < other.1 {
                other
            } else {
                (other.1, other.0)
            };
            assert!(
                !care.contains(&key),
                "`c` is in no application, so no congruence can fire on it"
            );
        }
    }

    /// The filter is APPLIED by [`apply_interface_policy`], not merely
    /// available: on a proposal whose all-pairs set is over the ceiling but
    /// whose care set is under it, `care` admits and `all` declines.
    ///
    /// This test exists because the mutation battery found nothing else pinning
    /// it — making `UfliaInterfacePolicy::filters` return `false` for every arm
    /// killed no test at all, because every other test either calls
    /// `care_graph_pairs` directly or exercises a proposal the filter cannot
    /// shrink. A policy that is never consulted is the exact shape of a knob
    /// that reads as configured and behaves as absent.
    #[test]
    fn the_care_filter_is_actually_applied_by_the_policy() {
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).expect("f");
        // Eleven applications: C(11,2) = 55 care pairs, under the ceiling.
        let mut apps = Vec::new();
        let mut args = Vec::new();
        for i in 0..11 {
            let v = arena.int_var(&format!("x{i}")).expect("int var");
            args.push(v);
            apps.push(arena.apply(f, &[v]).expect("f(x)"));
        }
        // Five bare integer symbols in no application: the all-pairs rule pairs
        // each of them with each UF argument, which no congruence can use.
        let mut bare = Vec::new();
        for i in 0..5 {
            bare.push(arena.int_var(&format!("c{i}")).expect("int var"));
        }
        let mut terms = apps.clone();
        terms.extend(bare.iter().copied());
        let root = sum(&mut arena, &terms);

        let mut candidates = args.clone();
        candidates.extend(bare.iter().copied());
        let mut proposed = Vec::new();
        for i in 0..candidates.len() {
            for j in (i + 1)..candidates.len() {
                // The all-pairs rule keeps a pair with at least one EUF endpoint.
                if i < args.len() || j < args.len() {
                    proposed.push((candidates[i], candidates[j]));
                }
            }
        }
        assert!(
            proposed.len() > MAX_INTERFACE_PAIRS,
            "the unfiltered proposal must be over the ceiling: {}",
            proposed.len()
        );
        assert_eq!(care_graph_pairs(&arena, &[root]).len(), 55);

        {
            let _guard = UfliaInterfacePolicyGuard::set(UfliaInterfacePolicy::All);
            assert!(
                apply_interface_policy(&arena, &[root], proposed.clone()).is_none(),
                "`all` declines this proposal"
            );
        }
        let _guard = UfliaInterfacePolicyGuard::set(UfliaInterfacePolicy::CareGraph);
        let kept = apply_interface_policy(&arena, &[root], proposed)
            .expect("`care` filters it under the ceiling and admits");
        assert_eq!(
            kept.len(),
            55,
            "exactly the care pairs survive, and nothing is truncated"
        );
    }

    /// Every policy is representable by its own name, and the default is the
    /// historical behaviour.
    #[test]
    fn policy_names_round_trip_and_the_default_is_the_measured_arm() {
        for policy in [
            UfliaInterfacePolicy::All,
            UfliaInterfacePolicy::CareGraph,
            UfliaInterfacePolicy::CareGraphTruncate,
        ] {
            let _guard = UfliaInterfacePolicyGuard::set(policy);
            assert_eq!(uflia_interface_policy(), policy);
            assert!(!policy.name().is_empty());
        }
        assert_eq!(
            UfliaInterfacePolicy::default(),
            UfliaInterfacePolicy::CareGraphTruncate,
            "the shipped default is the arm ADR-1801 measured, not the historical one"
        );
    }

    /// The counters are off by default: with a guard armed but nothing recorded
    /// the snapshot reads NOT engaged, so an unarmed run can never print a
    /// measured-looking zero.
    #[test]
    fn recording_is_a_no_op_without_a_guard() {
        let _guard = UfliaInterfaceCountersGuard::enable();
        assert!(!last_uflia_interface_counters().engaged());
        note(|c| c.entries = c.entries.saturating_add(1));
        assert!(last_uflia_interface_counters().engaged());
    }

    /// A declined proposal still records its size and the decline, so the reason
    /// the route gave up is visible in the counters and not only in a string.
    #[test]
    fn a_cap_decline_is_recorded_with_the_size_that_caused_it() {
        let _policy = UfliaInterfacePolicyGuard::set(UfliaInterfacePolicy::All);
        let _counters = UfliaInterfaceCountersGuard::enable();
        let (arena, root, proposed) = unary_family(40);
        let size = proposed.len();
        assert!(apply_interface_policy(&arena, &[root], proposed).is_none());
        let counters = last_uflia_interface_counters();
        assert_eq!(counters.pair_cap_declines, 1);
        assert_eq!(counters.pairs_max_proposed as usize, size);
        assert_eq!(counters.pairs_kept, 0, "nothing survived a decline");
    }
}
