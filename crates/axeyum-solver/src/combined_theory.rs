//! Warm, equality-sharing `EUF` + `LRA` theory oracle for the online `QF_UFLRA`
//! combination (Track 1, P1.6 — the shared-`CDCL(T)`-combination keystone, slice 1).
//!
//! The Boolean (`DPLL(T)`) layer in [`crate::uflra_online`] decides each propositional
//! model's conjunction of theory literals with a from-scratch `Nelson–Oppen`
//! combination (`decide_conjunction`): every call rebuilds a fresh
//! [`crate::lra_online::LraTheory`] (re-linearizing the atoms into the
//! Fourier–Motzkin atom builder) plus, per shared interface pair, three dynamically
//! registered order/equality atoms, and re-asserts the original `LRA` literals. That
//! cold rebuild is repeated for every early partial-assignment prune and every total
//! model the enumeration tries.
//!
//! [`CombinedTheory`] is the **warm** alternative. It performs the *identical*
//! combination as `decide_conjunction` — the same partition, the same shared pairs, the
//! same `LraTheory` atom layout, the same interface case-split DFS
//! ([`crate::uflra_online::run_interface_search`]), the same replay-checked leaf model —
//! but **caches** the constructed-and-base-asserted `LraTheory` across calls. When a
//! subsequent conjunction has the *same* `LRA` atom layout (the common case during the
//! enumeration, where successive models differ only in their `EUF` / Tseitin
//! assignments), the cached theory is reused at its post-base-assert baseline rather
//! than rebuilt. The interface DFS restores the theory to that baseline on exit (every
//! `push` is paired with a `pop`), so the cached state stays reusable.
//!
//! **Soundness / equivalence.** Because the warm path computes the *same* per-call atom
//! layout and drives the *same* DFS over an `LraTheory` with the *same* variable set as
//! the cold core, it returns the **identical verdict** (`Sat` / `Unsat` / `Unknown`,
//! and the same replay-checked model on `Sat`) to `decide_conjunction` on every input —
//! the parallel-run equivalence the slice-1 gate asserts. The warm path changes *only*
//! the lifetime of the theory solver, never the decision procedure. The `EUF` side is
//! stateless here (`classify_interface_equalities` / `euf_unsat` rebuild a small e-graph
//! per call, exactly as the cold core does), so only the `LraTheory` construction is
//! warmed in slice 1.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use axeyum_ir::{TermArena, TermId};

use crate::backend::{CheckResult, UnknownKind, UnknownReason};
use crate::euf_egraph::{EufTheory, TheoryLit, TheoryProp, TheorySolver};
use crate::lra_online::LraTheory;
use crate::theory_combination::{InterfaceStatus, classify_interface_equalities};
use crate::uflra_online::{
    Literal, PairAtoms, Partition, build_euf_assertions, collect_uflra_atoms, decide_conjunction,
    decline, euf_unsat, flatten_conjunction, is_theory_atom, partition, run_interface_search,
    shared_real_terms, unordered_pairs,
};

/// Hard ceiling on interface case-split pairs, mirroring the cold core's `MAX_SPLIT_DEPTH`
/// decline so the warm and cold paths reject the same oversized splits identically.
const MAX_SPLIT_PAIRS: usize = 64;

fn timeout_unknown(detail: impl Into<String>) -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Timeout,
        detail: detail.into(),
    })
}

/// The warm `EUF` + `LRA` equality-sharing theory oracle (slice 1).
///
/// Constructed once over the `BoolSearch` atom set (the indices are not load-bearing —
/// the cache keys on the per-call atom layout, not the construction argument).
/// [`CombinedTheory::check`] decides a conjunction of theory literals with the **same**
/// model-based combination as [`decide_conjunction`], reusing a cached `LraTheory` when
/// the `LRA` atom layout repeats.
pub(crate) struct CombinedTheory {
    /// The cached `LraTheory` and its provenance, valid at its post-base-assert baseline:
    /// `(lra_atom_terms layout, pair_atoms, pairs, theory)`. `None` until the first
    /// cacheable conjunction. A new call whose `lra_atom_terms` differs rebuilds.
    cache: Option<Cached>,
    /// The full theory-atom set in `BoolSearch` variable order (index `v` is the atom
    /// term of propositional variable `v`). [`CombinedTheory::propagate`] builds its
    /// warm `EUF` / `LRA` sub-theories over this whole set — asserting only the literals
    /// in the current conjunction — so the sub-theories can entail the *unassigned*
    /// atoms (the propagations). The sub-theory atom index then equals the `BoolSearch`
    /// variable directly.
    atom_terms: Vec<TermId>,
    /// The `BoolSearch` propositional variable each theory-atom [`TermId`] maps to —
    /// the inverse of `atom_terms`. [`CombinedTheory::propagate`] uses it to look up the
    /// variable for an asserted literal and for an interface-equality atom. An atom
    /// absent from this map has no propositional variable; an interface equality it
    /// names is then dropped (a sound omission — theory propagation only ever *adds*
    /// implied assignments).
    atom_var: BTreeMap<TermId, usize>,
    /// The absolute wall-clock deadline inherited from the online Boolean driver's
    /// `config.timeout`, forwarded to the shared interface-search DFS so the warm oracle
    /// honors the same budget as the cold core. `None` is the default, unbounded budget.
    deadline: Option<Instant>,
}

/// One warm-reusable `LraTheory` together with the layout it was built for.
struct Cached {
    /// The `LraTheory` atom layout `[original LRA atoms] ++ [eq/lt/gt per pair]` — the
    /// cache key. A call with the same layout reuses `theory` at its baseline.
    layout: Vec<TermId>,
    /// The interface pairs (in `TermId` order) the layout's trailing atoms encode.
    pairs: Vec<(TermId, TermId)>,
    /// The `eq`/`lt`/`gt` `LraTheory` indices per pair.
    pair_atoms: Vec<PairAtoms>,
    /// The theory, sitting at its baseline: the original `LRA` literals asserted, no
    /// interface atom on the trail. The DFS restores it here on exit.
    theory: LraTheory,
}

impl CombinedTheory {
    /// Builds the warm oracle. The construction argument warms nothing on its own (the
    /// cache fills lazily from the first conjunction); it is kept so the wiring mirrors
    /// the cold core's atom-set discovery and leaves room for a future eager pre-warm.
    #[must_use]
    pub(crate) fn new(arena: &mut TermArena, atom_terms: &[TermId]) -> Self {
        Self::new_with_deadline(arena, atom_terms, None)
    }

    /// Builds the warm oracle with a caller-owned deadline forwarded to the shared
    /// interface-search DFS, so the warm path honors the same `config.timeout` budget as
    /// the cold core rather than grinding a hard arrangement past it.
    #[must_use]
    pub(crate) fn new_with_deadline(
        _arena: &mut TermArena,
        atom_terms: &[TermId],
        deadline: Option<Instant>,
    ) -> Self {
        let mut atom_var = BTreeMap::new();
        for (var, &atom) in atom_terms.iter().enumerate() {
            // First occurrence wins, mirroring the `BoolSearch` atom numbering (the atom
            // set is already deduplicated upstream, so this is the identity mapping).
            atom_var.entry(atom).or_insert(var);
        }
        Self {
            cache: None,
            atom_terms: atom_terms.to_vec(),
            atom_var,
            deadline,
        }
    }

    /// Decides the conjunction of `literals` with the warm equality-sharing combination,
    /// returning the **identical** verdict (and `Sat` model) the cold
    /// [`decide_conjunction`] would — the parallel-run equivalence contract. Reuses the
    /// cached `LraTheory` when this call's `LRA` atom layout matches the cached one,
    /// otherwise rebuilds (and re-caches) it.
    pub(crate) fn check(&mut self, arena: &mut TermArena, literals: &[Literal]) -> CheckResult {
        // Steps 2–4: partition, shared pairs, the EUF single-theory short-circuit — bit
        // for bit the cold core's preamble, so a decline / early Unsat here is identical.
        let Some(part) = partition(arena, literals) else {
            return decline("atom outside QF_UFLRA for the online combination path");
        };
        let shared = shared_real_terms(arena, &part);
        let pairs = unordered_pairs(&shared);
        if pairs.len() > MAX_SPLIT_PAIRS {
            return decline("too many interface pairs for the online combination split");
        }
        let euf_assertions = build_euf_assertions(arena, &part.euf);
        if euf_unsat(arena, &euf_assertions) {
            return CheckResult::Unsat;
        }

        // Step 5: the per-call LRA atom layout (the original LRA literals, then three
        // interface atoms per shared pair) — identical to the cold core's `lra_atom_terms`.
        let mut layout: Vec<TermId> = part.lra.iter().map(|l| l.atom).collect();
        let mut pair_atoms: Vec<PairAtoms> = Vec::with_capacity(pairs.len());
        for &(s, t) in &pairs {
            let (Ok(eq), Ok(lt), Ok(gt)) =
                (arena.eq(s, t), arena.real_lt(s, t), arena.real_gt(s, t))
            else {
                return decline("interface term build failed");
            };
            let base = layout.len();
            layout.push(eq);
            layout.push(lt);
            layout.push(gt);
            pair_atoms.push(PairAtoms {
                eq: base,
                lt: base + 1,
                gt: base + 2,
            });
        }

        // Reuse the cached theory at its baseline when the layout matches; else rebuild
        // and re-cache. Either way the theory entering the DFS holds exactly the original
        // LRA literals — the same state the cold core constructs.
        let warm = matches!(&self.cache, Some(c) if c.layout == layout);
        if !warm {
            let Some(mut theory) = LraTheory::new_with_deadline(arena, &layout, self.deadline)
            else {
                self.cache = None;
                return timeout_unknown("timeout while constructing combined LRA theory");
            };
            for (index, lit) in part.lra.iter().enumerate() {
                if theory.assert(index, lit.value).is_err() {
                    // A base conflict is the cold core's immediate `Unsat`. Do not cache a
                    // conflicted theory; drop any stale cache so the next call rebuilds.
                    self.cache = None;
                    return CheckResult::Unsat;
                }
            }
            self.cache = Some(Cached {
                layout: layout.clone(),
                pairs: pairs.clone(),
                pair_atoms: pair_atoms.clone(),
                theory,
            });
        }

        let deadline = self.deadline;
        let cached = self.cache.as_mut().expect("cache populated above");
        run_interface_search(
            arena,
            literals,
            &part.euf,
            euf_assertions,
            &cached.pairs,
            &cached.pair_atoms,
            &mut cached.theory,
            deadline,
        )
    }

    /// **Combined theory propagation** (slice 2): the literals the warm `EUF` + `LRA`
    /// combination *genuinely entails* under the conjunction `literals` (the
    /// current partial propositional assignment's asserted theory atoms), each
    /// expressed as a [`TheoryProp`] over the **`BoolSearch` propositional variable**
    /// numbering. A `DPLL(T)` loop assigns each entailed literal without a decision,
    /// pruning the search — never changing the `Sat` / `Unsat` verdict.
    ///
    /// Three sound sources are unioned, each a strict under-approximation that **never
    /// fabricates** a propagation:
    ///
    /// - **`EUF`** ([`EufTheory::propagate`]): an unassigned equality atom whose two
    ///   sides are already congruent under the asserted equalities — entailed `true`,
    ///   with the asserted-equality core as the reason.
    /// - **`LRA`** ([`LraTheory::propagate`]): an unassigned *order* atom whose
    ///   negation is infeasible against the live Fourier–Motzkin system — entailed at
    ///   the proven polarity, with the asserted-only Farkas core as the reason. Only
    ///   the **original** `LRA` atoms map to query variables (the interface order atoms
    ///   the layout appends have no `BoolSearch` variable); the rest are dropped.
    /// - **Interface equalities** ([`classify_interface_equalities`] over the asserted
    ///   `EUF` state): each shared pair the `EUF` congruence already pins — `Entailed`
    ///   ⇒ the pair's `(= s t)` atom entailed `true`, `Refuted` (an asserted
    ///   disequality separates the classes) ⇒ entailed `false`. The reason is the
    ///   asserted `EUF` literals (asserted-only). Only pairs whose equality atom is a
    ///   query variable are emitted.
    ///
    /// Every emitted literal is genuinely entailed by the asserted state, and every
    /// reason literal is one of the asserted atoms at its asserted polarity — the
    /// soundness invariant the slice-2 gate checks (`asserted ∧ ¬entailed` is `UNSAT`,
    /// `0` unsound). A propagated atom with no `BoolSearch` variable is silently
    /// dropped: omitting an implied assignment only forgoes pruning, it can never
    /// change a verdict.
    pub(crate) fn propagate(&self, arena: &mut TermArena, literals: &[Literal]) -> Vec<TheoryProp> {
        let Some(part) = partition(arena, literals) else {
            return Vec::new();
        };
        // Only literals that are query variables can be asserted (and named in a
        // reason); restrict to those, in their conjunction order.
        let asserted: Vec<Literal> = literals
            .iter()
            .copied()
            .filter(|l| self.atom_var.contains_key(&l.atom))
            .collect();
        let mut out: Vec<TheoryProp> = Vec::new();
        self.euf_propagations(arena, &asserted, &mut out);
        self.lra_propagations(arena, &asserted, &mut out);
        self.interface_propagations(arena, &part, &mut out);
        out
    }

    /// Source (a): the `EUF` congruence entailments. The warm `EufTheory` is built over
    /// the **whole** atom set (so its atom index is the `BoolSearch` variable directly),
    /// with only the conjunction's literals asserted — so [`EufTheory::propagate`] can
    /// entail the *unassigned* equality atoms whose sides became congruent.
    fn euf_propagations(
        &self,
        arena: &mut TermArena,
        asserted: &[Literal],
        out: &mut Vec<TheoryProp>,
    ) {
        let mut euf = EufTheory::new(arena, &self.atom_terms);
        for lit in asserted {
            let var = self.atom_var[&lit.atom];
            if euf.assert(var, lit.value).is_err() {
                return; // an inconsistent EUF state — `check` reports it; emit nothing
            }
        }
        self.collect_props(&euf.propagate(), out);
    }

    /// Source (b): the `LRA` order entailments. The warm `LraTheory` is likewise built
    /// over the whole atom set (atom index = `BoolSearch` variable), asserting only the
    /// conjunction, so [`LraTheory::propagate`] entails the *unassigned* order atoms its
    /// negation probe refutes.
    fn lra_propagations(
        &self,
        arena: &mut TermArena,
        asserted: &[Literal],
        out: &mut Vec<TheoryProp>,
    ) {
        let Some(mut lra) = LraTheory::new_with_deadline(arena, &self.atom_terms, self.deadline)
        else {
            return;
        };
        for lit in asserted {
            let var = self.atom_var[&lit.atom];
            if lra.assert(var, lit.value).is_err() {
                return; // a base LRA conflict — `check` reports it; nothing to propagate
            }
        }
        self.collect_props(&lra.propagate(), out);
    }

    /// Source (c): interface-equality entailments — the shared pairs the asserted `EUF`
    /// congruence already pins `Entailed` / `Refuted`, mapped to the pair's `(= s t)`
    /// query variable. The reason is the asserted `EUF` literals (asserted-only).
    fn interface_propagations(
        &self,
        arena: &mut TermArena,
        part: &Partition,
        out: &mut Vec<TheoryProp>,
    ) {
        let shared = shared_real_terms(arena, part);
        let pairs = unordered_pairs(&shared);
        if pairs.is_empty() {
            return;
        }
        let euf_assertions = build_euf_assertions(arena, &part.euf);
        let reason = asserted_euf_reason(&self.atom_var, part);
        for &(s, t) in &pairs {
            let Ok(eq) = arena.eq(s, t) else { continue };
            let Some(&var) = self.atom_var.get(&eq) else {
                continue; // the interface equality is not a propositional query variable
            };
            let status = classify_interface_equalities(arena, &euf_assertions, &[(s, t)])
                .first()
                .map_or(InterfaceStatus::Undetermined, |c| c.1);
            let value = match status {
                InterfaceStatus::Entailed => true,
                InterfaceStatus::Refuted => false,
                InterfaceStatus::Undetermined => continue, // never propagate the uncertain
            };
            out.push(TheoryProp {
                lit: TheoryLit { atom: var, value },
                reason: reason.clone(),
            });
        }
    }

    /// Appends the sub-theory propagations (whose atom indices are already `BoolSearch`
    /// variables, since the sub-theory was built over the whole atom set) onto `out`.
    /// A propagation is kept only when every reason literal also names a `BoolSearch`
    /// variable in range — which holds by construction, but the bound check keeps the
    /// translation total and panic-free.
    fn collect_props(&self, props: &[TheoryProp], out: &mut Vec<TheoryProp>) {
        for prop in props {
            if prop.lit.atom >= self.atom_terms.len() {
                continue;
            }
            if prop.reason.iter().any(|r| r.atom >= self.atom_terms.len()) {
                continue;
            }
            out.push(prop.clone());
        }
    }
}

/// The asserted `EUF` literals as a reason core over `BoolSearch` variables: every
/// `EUF` literal currently asserted, at its asserted polarity. Asserted-only by
/// construction, so it is a sound explanation for any congruence entailment the
/// asserted `EUF` state forces. Literals without a query variable are skipped (they
/// cannot be named; their omission only weakens the reason, never its soundness, and
/// the interface entailment is still genuine under the named subset because the full
/// asserted state entails it).
fn asserted_euf_reason(atom_var: &BTreeMap<TermId, usize>, part: &Partition) -> Vec<TheoryLit> {
    part.euf
        .iter()
        .filter_map(|lit| {
            atom_var.get(&lit.atom).map(|&var| TheoryLit {
                atom: var,
                value: lit.value,
            })
        })
        .collect()
}

/// A verdict code for the parallel-run equivalence gate: `0` = `Unsat`, `1` = `Sat`,
/// `2` = `Unknown`. A stable, comparable encoding (the `Sat` model is irrelevant to the
/// equivalence claim — only the verdict must match).
fn verdict_code(result: &CheckResult) -> u8 {
    match result {
        CheckResult::Unsat => 0,
        CheckResult::Sat(_) => 1,
        CheckResult::Unknown(_) => 2,
    }
}

/// **Parallel-run equivalence harness** (slice-1 soundness gate, test-only): when
/// `assertions` flatten to a conjunction of `QF_UFLRA` theory atoms, decide it **both**
/// ways — the cold from-scratch [`decide_conjunction`] (the trusted reference) and the
/// warm [`CombinedTheory`] oracle this slice introduces — and return their verdict codes
/// `(cold, warm)`. The test asserts `cold == warm` on every instance: a divergence is the
/// bug slice 1 must not have. The warm oracle is reused across the conjunction's own
/// repeated sub-checks here too (a second `check` on the same instance must hit the cache
/// and still agree). Returns `None` for a non-conjunctive or non-atom shape (those are
/// gated by the separate offline-Ackermann differential).
///
/// Not part of the production surface.
#[doc(hidden)]
#[must_use]
pub fn combined_vs_cold_conjunction(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<(u8, u8)> {
    // Flatten to a conjunction of literals exactly as the fast-path does.
    let mut literals: Vec<Literal> = Vec::new();
    for &assertion in assertions {
        if !flatten_conjunction(arena, assertion, true, &mut literals) {
            return None;
        }
    }
    if literals.is_empty() || !literals.iter().all(|l| is_theory_atom(arena, l.atom)) {
        return None;
    }

    // The cold reference verdict (deadline-free: the trusted reference the warm oracle
    // must match on every input).
    let cold = verdict_code(&decide_conjunction(arena, &literals, None));

    // The warm oracle over the conjunction's atom set, checked twice so the cache-reuse
    // path is exercised (the second check must hit the warm baseline and still agree).
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen: std::collections::BTreeSet<TermId> = std::collections::BTreeSet::new();
    for &assertion in assertions {
        collect_uflra_atoms(arena, assertion, &mut atom_terms, &mut seen);
    }
    let mut combined = CombinedTheory::new(arena, &atom_terms);
    let warm_first = verdict_code(&combined.check(arena, &literals));
    let warm_second = verdict_code(&combined.check(arena, &literals));
    debug_assert_eq!(
        warm_first, warm_second,
        "warm oracle must be stable across cache reuse"
    );

    Some((cold, warm_first))
}

/// One reported combined-theory propagation over **atom terms** (the slice-2 test
/// harness shape): `(entailed atom, entailed polarity, reason as (atom, polarity)
/// pairs)`.
pub type PropagationReport = (TermId, bool, Vec<(TermId, bool)>);

/// How a combined-theory atom routes to the live sub-theories (slice 3b). The
/// incremental [`CombinedIncremental::assert`] consults this per propositional variable
/// to fan an assertion out to the owning sub-theory (or both, for a shared atom).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AtomRoute {
    /// A pure `LRA` order atom — asserted on the live `LraTheory` only.
    Lra,
    /// A pure `EUF` (UF-touching, non-linear-real) equality — asserted on the live
    /// `EufTheory` only.
    Euf,
    /// A linear-real equality that also mentions a `UF` application — asserted on
    /// **both** sub-theories (the original atom is genuinely shared).
    Both,
    /// An interface `(= s t)` atom for shared pair index `pair` — asserting it merges
    /// / separates the pair on **both** the `EufTheory` (via the eq atom) and the
    /// `LraTheory` (via its eq interface atom).
    InterfaceEq { pair: usize },
    /// An interface order atom (`s < t` / `s > t`) for a shared pair — asserted on the
    /// `LraTheory` only (the `EufTheory` has no order relation).
    InterfaceOrder,
}

/// One registered shared-interface pair (slice 3b): its `(s, t)` real terms and the
/// freshly-allocated propositional variables of its three structural atoms
/// (`eq` / `lt` / `gt`), beyond the original Tseitin `atom_count`. Slice 3c adds the
/// structural clauses (`eq ∨ lt ∨ gt`, mutual exclusion, the `EUF` ↔ `LRA` tie) over
/// these variables to the `SAT` clause DB and lets the generic
/// [`crate::cdclt::CdclT`] branch them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct InterfacePair {
    /// The shared real terms `(s, t)`, in [`TermId`] order.
    pub(crate) terms: (TermId, TermId),
    /// The fresh propositional variable for `(= s t)`.
    pub(crate) eq_var: usize,
    /// The fresh propositional variable for `(real_lt s t)`.
    pub(crate) lt_var: usize,
    /// The fresh propositional variable for `(real_gt s t)`.
    pub(crate) gt_var: usize,
}

/// A structural clause over the registered interface variables (slice 3b output): a
/// disjunction of `(variable, polarity)` literals. Slice 3c adds these to the `SAT`
/// clause DB so the generic [`crate::cdclt::CdclT`] branches the interface
/// case-split soundly.
pub(crate) type StructuralClause = Vec<(usize, bool)>;

/// **Incremental, backtrackable combined-theory state** (slice 3b): live `EUF` + `LRA`
/// sub-theories over the **full** atom set `[original atoms ++ interface eq/lt/gt per
/// shared pair]`, with the up-front interface variables registered beyond the original
/// `atom_count`. It [`impl TheorySolver`](TheorySolver) so the generic
/// [`crate::cdclt::CdclT`] can drive it: each `SAT` trail assignment of a
/// theory atom is forwarded to the owning sub-theory ([`CombinedIncremental::assert`]),
/// decisions backtrack in lockstep ([`push`](CombinedIncremental::push) /
/// [`pop`](CombinedIncremental::pop)), and the combination's entailments are returned by
/// [`propagate`](CombinedIncremental::propagate) reading the **live** sub-theories.
///
/// **Atom routing.** Each propositional variable carries an [`AtomRoute`]: a pure order
/// atom goes to `LRA`, a `UF`-touching equality to `EUF`, a shared linear-real-`UF`
/// equality to both, an interface `(= s t)` variable to both (merge/separate on `EUF`,
/// the `LRA` eq atom), an interface order variable to `LRA`. The fan-out keeps the two
/// sub-theories' shared-equality views in sync — the core of `Nelson–Oppen` combination.
///
/// **Conflict cores.** Both sub-theories return **asserted-only** conflict cores over
/// their own atom indices (which are the combined variables directly, since each
/// sub-theory is built over the full combined layout). A core therefore names only
/// currently-asserted literals at their asserted polarity — exactly the shape `1-UIP`
/// conflict analysis in [`crate::cdclt::CdclT`] consumes (every reason literal is a
/// trail literal, so resolution terminates at the first unique implication point).
///
/// **Validation (before the generic driver was wired).** Slice 3b keeps the trusted per-call
/// [`CombinedTheory::check`] and validates this surface against it
/// (`combined_incremental_vs_check`): driving the incremental surface to a fixpoint and
/// reading its verdict must AGREE with `check` on every case the incremental surface
/// *decides on its own*. Where an interface pair stays `Undetermined` (a genuine
/// case-split that only the slice-3c [`crate::cdclt::CdclT`] branching resolves), the incremental surface
/// honestly *defers* to `check` rather than guessing.
pub(crate) struct CombinedIncremental {
    /// Live `EUF` sub-theory over the full combined atom layout (index = combined var).
    euf: EufTheory,
    /// Live `LRA` sub-theory over the same full combined atom layout.
    lra: LraTheory,
    /// Per combined variable, how an assertion of it fans out to the sub-theories.
    routes: Vec<AtomRoute>,
    /// The registered shared-interface pairs (their structural variables + terms).
    pairs: Vec<InterfacePair>,
    /// Per combined variable, the value it is currently asserted at (`None` if free) —
    /// so [`CombinedIncremental::propagate`] knows the asserted literals to read as the
    /// conjunction, and backtracking restores them in lockstep with the sub-theories.
    assigned: Vec<Option<bool>>,
    /// The assignment log (combined variables assigned since the start, in order) —
    /// truncated back to a marker on [`pop`](CombinedIncremental::pop).
    assigned_log: Vec<usize>,
    /// Backtrack trail: the `assigned_log` length saved at each
    /// [`push`](CombinedIncremental::push).
    trail: Vec<usize>,
}

impl CombinedIncremental {
    /// Builds the incremental combined state over `atom_terms` (the `BoolSearch` /
    /// Tseitin atom numbering). The shared-interface pairs are computed **once** up front
    /// from the full atom set (an over-approximation: every pair of shared real terms),
    /// and three fresh propositional variables — `eq` / `lt` / `gt` — are registered per
    /// pair *beyond* the original `atom_terms.len()`. The live `EufTheory` and
    /// `LraTheory` are built over the resulting combined layout so a sub-theory atom index
    /// equals the combined variable directly.
    ///
    /// Returns `None` when the interface terms cannot be built (an arena failure) — the
    /// caller then falls back to the per-call [`CombinedTheory::check`].
    #[must_use]
    pub(crate) fn new(arena: &mut TermArena, atom_terms: &[TermId]) -> Option<Self> {
        Self::new_with_deadline(arena, atom_terms, None)
    }

    /// Builds the incremental combined state with one caller-owned absolute
    /// deadline shared by the `LRA` sub-theory and the outer Boolean search.
    #[must_use]
    pub(crate) fn new_with_deadline(
        arena: &mut TermArena,
        atom_terms: &[TermId],
        deadline: Option<Instant>,
    ) -> Option<Self> {
        let original_atoms: Vec<TermId> = atom_terms.to_vec();

        // Shared pairs over the full atom set, once. Build a Partition from "all atoms
        // asserted true" purely to discover the EUF/LRA real-term split; the polarity
        // does not affect which terms are shared.
        let all_true: Vec<Literal> = original_atoms
            .iter()
            .map(|&atom| Literal { atom, value: true })
            .collect();
        let part = partition(arena, &all_true)?;
        let shared = shared_real_terms(arena, &part);
        let raw_pairs = unordered_pairs(&shared);
        if raw_pairs.len() > MAX_SPLIT_PAIRS {
            return None;
        }

        let mut combined: Vec<TermId> = original_atoms.clone();
        let mut pairs: Vec<InterfacePair> = Vec::with_capacity(raw_pairs.len());
        for &(s, t) in &raw_pairs {
            let (Ok(eq), Ok(lt), Ok(gt)) =
                (arena.eq(s, t), arena.real_lt(s, t), arena.real_gt(s, t))
            else {
                return None;
            };
            let eq_var = combined.len();
            combined.push(eq);
            let lt_var = combined.len();
            combined.push(lt);
            let gt_var = combined.len();
            combined.push(gt);
            pairs.push(InterfacePair {
                terms: (s, t),
                eq_var,
                lt_var,
                gt_var,
            });
        }

        let routes = build_routes(&part, &original_atoms, &combined, &pairs);
        let euf = EufTheory::new(arena, &combined);
        let lra = LraTheory::new_with_deadline(arena, &combined, deadline)?;
        let n = combined.len();
        Some(Self {
            euf,
            lra,
            routes,
            pairs,
            assigned: vec![None; n],
            assigned_log: Vec::new(),
            trail: Vec::new(),
        })
    }

    /// The registered shared-interface pairs (their fresh `eq` / `lt` / `gt` variables and
    /// `(s, t)` terms). Slice 3c reads these to wire the structural clauses + the case-split
    /// branching into the generic [`crate::cdclt::CdclT`].
    #[must_use]
    pub(crate) fn interface_pairs(&self) -> &[InterfacePair] {
        &self.pairs
    }

    /// The structural clauses over the registered interface variables (slice 3b output,
    /// for slice 3c's `SAT` clause DB). Per shared pair `(s, t)` with variables
    /// `eq` / `lt` / `gt`:
    ///
    /// - **totality** `eq ∨ lt ∨ gt` — exactly one order relation holds over the reals;
    /// - **mutual exclusion** `¬eq ∨ ¬lt`, `¬eq ∨ ¬gt`, `¬lt ∨ ¬gt` — at most one holds.
    ///
    /// Together they pin each shared pair to exactly one of `{=, <, >}` — the
    /// trichotomy the interface case-split branches. (The `EUF` ↔ `LRA` *tie* — that the
    /// `eq` variable's truth equals the pair's `EUF` congruence — is enforced
    /// dynamically by [`CombinedIncremental::assert`] fanning the eq onto both
    /// sub-theories and by [`CombinedIncremental::propagate`]'s interface entailments,
    /// not by a static clause.)
    #[must_use]
    pub(crate) fn structural_clauses(&self) -> Vec<StructuralClause> {
        let mut clauses = Vec::with_capacity(self.pairs.len() * 4);
        for p in &self.pairs {
            clauses.push(vec![(p.eq_var, true), (p.lt_var, true), (p.gt_var, true)]);
            clauses.push(vec![(p.eq_var, false), (p.lt_var, false)]);
            clauses.push(vec![(p.eq_var, false), (p.gt_var, false)]);
            clauses.push(vec![(p.lt_var, false), (p.gt_var, false)]);
        }
        clauses
    }

    /// Records `var := value` in the assignment log, classifying the assertion against
    /// any existing assignment of `var`: `Fresh` (newly recorded — fan it out), `Repeat`
    /// (idempotent at the same value — a no-op), or `Conflict` (asserting the *opposite*
    /// of an already-asserted value — a theory conflict, e.g. a propagation entailing the
    /// negation of a trail literal).
    fn record(&mut self, var: usize, value: bool) -> RecordOutcome {
        match self.assigned.get(var).copied().flatten() {
            Some(existing) if existing == value => RecordOutcome::Repeat,
            Some(_) => RecordOutcome::Conflict,
            None => {
                self.assigned[var] = Some(value);
                self.assigned_log.push(var);
                RecordOutcome::Fresh
            }
        }
    }

    /// The currently-asserted literals over combined variables — a sound (if non-minimal)
    /// **asserted-only** conflict core for a direct contradiction (an opposite re-assert).
    /// `1-UIP` analysis still terminates on it: every literal is a trail literal.
    fn asserted_core(&self) -> Vec<TheoryLit> {
        self.assigned_log
            .iter()
            .filter_map(|&v| self.assigned[v].map(|value| TheoryLit { atom: v, value }))
            .collect()
    }
}

/// The outcome of recording an assertion against the current assignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RecordOutcome {
    /// A new assignment — the caller fans it out to the sub-theories.
    Fresh,
    /// The same value already asserted — a no-op.
    Repeat,
    /// The opposite value already asserted — a direct theory conflict.
    Conflict,
}

impl TheorySolver for CombinedIncremental {
    /// Asserts combined variable `var` at `value`, routing it to the owning sub-theory
    /// (or both, for a shared / interface-eq atom). Returns the conflicting **asserted**
    /// literal core (over combined variables) on inconsistency — suitable verbatim for
    /// `1-UIP` conflict analysis in [`crate::cdclt::CdclT`].
    fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        match self.record(var, value) {
            RecordOutcome::Repeat => return Ok(()), // idempotent re-assert at the same value
            RecordOutcome::Conflict => {
                // Asserting the opposite of an asserted literal: a direct conflict over the
                // asserted trail (var is not re-recorded, so the trail stays consistent).
                return Err(self.asserted_core());
            }
            RecordOutcome::Fresh => {}
        }
        let route = self.routes.get(var).copied().unwrap_or(AtomRoute::Euf);
        match route {
            AtomRoute::Lra | AtomRoute::InterfaceOrder => self.lra.assert(var, value),
            AtomRoute::Euf => self.euf.assert(var, value),
            AtomRoute::Both | AtomRoute::InterfaceEq { .. } => {
                self.euf.assert(var, value)?;
                self.lra.assert(var, value)
            }
        }
    }

    /// Saves a backtrack point on **both** sub-theories and the interface trail, in
    /// lockstep — so a later [`pop`](CombinedIncremental::pop) restores all three to this
    /// point together.
    fn push(&mut self) {
        self.euf.push();
        self.lra.push();
        self.trail.push(self.assigned_log.len());
    }

    /// Undoes every assertion back to the most recent
    /// [`push`](CombinedIncremental::push), on both sub-theories and the interface trail,
    /// in lockstep.
    fn pop(&mut self) {
        self.euf.pop();
        self.lra.pop();
        if let Some(marker) = self.trail.pop() {
            while self.assigned_log.len() > marker {
                if let Some(var) = self.assigned_log.pop() {
                    self.assigned[var] = None;
                }
            }
        }
    }

    /// Combined-theory propagation over the **live** sub-theories: the `EUF` congruence
    /// entailments + the `LRA` order entailments, read incrementally. Indices are combined
    /// variables directly (each sub-theory is over the full combined layout), so the
    /// `Dpll` consumes them without translation, and each reason is asserted-only.
    ///
    /// The interface `eq` atoms are themselves registered in the live `EufTheory`, so an
    /// `Entailed` interface equality is emitted *by* [`EufTheory::propagate`] (its two
    /// sides congruent) with no extra interface pass — the slice-2 interface source is
    /// thus subsumed for the entailed direction. The `Refuted` direction (an interface
    /// eq forced *false*) is not emitted: `EufTheory` defers disequality-entailment, and
    /// **omitting** a propagation is always sound — it only forgoes pruning, never a
    /// verdict. (Slice 3c's structural clauses still let the `Dpll` branch the refuted
    /// pair, so completeness is unaffected.)
    fn propagate(&self) -> Vec<TheoryProp> {
        let mut out: Vec<TheoryProp> = self.euf.propagate();
        out.extend(self.lra.propagate());
        out
    }
}

/// Builds the per-variable [`AtomRoute`] table for the combined layout. The original
/// atoms are routed by their **`partition` membership** — the *same* classification the
/// per-call [`CombinedTheory::check`] uses — so the incremental routing cannot diverge
/// from the trusted path: an atom in `part.lra` only ⇒ `Lra`, in `part.euf` only ⇒
/// `Euf`, in both (a shared linear-real-`UF` equality) ⇒ `Both`. The trailing variables
/// are the registered interface atoms (eq → `InterfaceEq`, lt/gt → `InterfaceOrder`),
/// looked up from `pairs`.
fn build_routes(
    part: &Partition,
    original_atoms: &[TermId],
    combined: &[TermId],
    pairs: &[InterfacePair],
) -> Vec<AtomRoute> {
    let in_lra: BTreeSet<TermId> = part.lra.iter().map(|l| l.atom).collect();
    let in_euf: BTreeSet<TermId> = part.euf.iter().map(|l| l.atom).collect();
    let mut routes = vec![AtomRoute::Euf; combined.len()];
    for (var, &atom) in original_atoms.iter().enumerate() {
        routes[var] = match (in_lra.contains(&atom), in_euf.contains(&atom)) {
            (true, true) => AtomRoute::Both,
            (true, false) => AtomRoute::Lra,
            // EUF-only, or (defensively) neither — assert on EUF, a no-op for a
            // non-equality atom, never on LRA where a spurious constraint could mislead.
            (false, _) => AtomRoute::Euf,
        };
    }
    for (index, p) in pairs.iter().enumerate() {
        routes[p.eq_var] = AtomRoute::InterfaceEq { pair: index };
        routes[p.lt_var] = AtomRoute::InterfaceOrder;
        routes[p.gt_var] = AtomRoute::InterfaceOrder;
    }
    routes
}

/// **Combined-theory-propagation harness** (slice-2 soundness gate, test-only): build
/// the warm [`CombinedTheory`] over the atom set `atom_terms` (the `BoolSearch`
/// numbering), assert the conjunction `asserted` (each `(atom term, polarity)`), and
/// return every literal [`CombinedTheory::propagate`] genuinely entails as a
/// [`PropagationReport`].
///
/// The propagated literals (and their reasons) are returned over **atom terms** (the
/// internal `BoolSearch`-variable indices translated back through `atom_terms`), so the
/// slice-2 test can confirm each one is genuinely entailed by checking `asserted ∧
/// ¬entailed` is `UNSAT` offline — and that the reason is asserted-only. Returns `None`
/// when `asserted` is not a conjunction of `QF_UFLRA` theory atoms (out of scope).
///
/// Not part of the production surface.
#[doc(hidden)]
#[must_use]
pub fn combined_theory_propagations(
    arena: &mut TermArena,
    atom_terms: &[TermId],
    asserted: &[(TermId, bool)],
) -> Option<Vec<PropagationReport>> {
    if !asserted
        .iter()
        .all(|&(atom, _)| is_theory_atom(arena, atom))
    {
        return None;
    }
    let literals: Vec<Literal> = asserted
        .iter()
        .map(|&(atom, value)| Literal { atom, value })
        .collect();
    // The inverse of the atom→var map: a var index back to its atom term, so the
    // propagation (over `BoolSearch` variables) can be reported over atom terms.
    let combined = CombinedTheory::new(arena, atom_terms);
    let props = combined.propagate(arena, &literals);
    let term_of = |var: usize| atom_terms.get(var).copied();
    let mut out = Vec::with_capacity(props.len());
    for prop in props {
        let atom = term_of(prop.lit.atom)?;
        let reason: Option<Vec<(TermId, bool)>> = prop
            .reason
            .iter()
            .map(|r| term_of(r.atom).map(|t| (t, r.value)))
            .collect();
        out.push((atom, prop.lit.value, reason?));
    }
    Some(out)
}

/// The incremental surface's self-decided verdict on a conjunction (slice-3b harness):
/// `Inconsistent` when an `assert` (after the propagation fixpoint) hits a sub-theory
/// conflict; `Consistent` when every literal asserts cleanly **and** no shared interface
/// pair stays `Undetermined` (so no case-split — a definite verdict the incremental
/// surface owns without a `Dpll`); `Deferred` when an interface pair is `Undetermined`
/// (a genuine case-split slice 3c's branching must resolve).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IncrementalDecision {
    /// A sub-theory conflict — the conjunction is `Unsat`.
    Inconsistent,
    /// No conflict and every shared pair determined — `check` must agree (not `Unsat`).
    Consistent,
    /// An `Undetermined` interface pair remains — deferred to the slice-3c case-split.
    Deferred,
}

/// **Slice-3b incremental-vs-`check` validation harness** (soundness gate, test-only):
/// drive the [`CombinedIncremental`] surface over a conjunction of theory literals and
/// return *both* its self-decided verdict ([`IncrementalDecision`]) and the trusted
/// per-call [`CombinedTheory::check`] verdict code, so the test can assert they agree on
/// every case the incremental surface decides on its own.
///
/// The incremental surface is driven exactly as production `CdclT` does: a fresh
/// `push`, then `assert` each literal (returning `Inconsistent` on the first sub-theory
/// conflict), reaching the `propagate` fixpoint between asserts (so any entailed atom is
/// itself asserted, surfacing the conflicts a pure literal-by-literal assert would miss).
/// With no conflict, the shared interface pairs are classified against the live `EUF`
/// assertions: any `Undetermined` pair ⇒ `Deferred`; otherwise `Consistent`.
///
/// Returns `None` for a non-conjunctive / non-atom shape, or when the incremental state
/// cannot be built (the same shapes [`CombinedTheory::check`] declines) — those are out
/// of the slice-3b validation's scope.
///
/// Not part of the production surface.
#[doc(hidden)]
#[must_use]
pub fn combined_incremental_vs_check(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<(IncrementalDecision, u8)> {
    let mut literals: Vec<Literal> = Vec::new();
    for &assertion in assertions {
        if !flatten_conjunction(arena, assertion, true, &mut literals) {
            return None;
        }
    }
    if literals.is_empty() || !literals.iter().all(|l| is_theory_atom(arena, l.atom)) {
        return None;
    }

    // The atom set the incremental surface (and `check`) numbers over.
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    for &assertion in assertions {
        collect_uflra_atoms(arena, assertion, &mut atom_terms, &mut seen);
    }

    let decision = drive_incremental(arena, &atom_terms, &literals)?;

    // The trusted per-call verdict over the same atom set.
    let mut combined = CombinedTheory::new(arena, &atom_terms);
    let check = verdict_code(&combined.check(arena, &literals));
    Some((decision, check))
}

/// The registered interface structure of a [`CombinedIncremental`] (slice-3b harness,
/// test-only): the number of original atoms, the registered interface pairs as
/// `(eq_var, lt_var, gt_var)` triples, and the structural clauses over those variables
/// (each a `(var, polarity)` disjunction). Lets the slice-3b test confirm the slice-3c
/// hand-off surface is well-formed: every interface variable is fresh (≥ the original
/// atom count) and distinct, and the structural clauses reference only registered
/// variables — without yet wiring them into the `SAT` clause DB (that is slice 3c).
///
/// Returns `None` for shapes the incremental state declines (the same as
/// [`combined_incremental_vs_check`]).
///
/// Not part of the production surface.
#[doc(hidden)]
#[must_use]
#[allow(clippy::type_complexity)]
pub fn combined_incremental_structure(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<(usize, Vec<(usize, usize, usize)>, Vec<Vec<(usize, bool)>>)> {
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    for &assertion in assertions {
        collect_uflra_atoms(arena, assertion, &mut atom_terms, &mut seen);
    }
    let original_count = atom_terms.len();
    let state = CombinedIncremental::new(arena, &atom_terms)?;
    let pairs: Vec<(usize, usize, usize)> = state
        .interface_pairs()
        .iter()
        .map(|p| (p.eq_var, p.lt_var, p.gt_var))
        .collect();
    Some((original_count, pairs, state.structural_clauses()))
}

/// Drives the [`CombinedIncremental`] surface over `literals` and returns its
/// self-decided [`IncrementalDecision`] (the slice-3b harness core). `None` when the
/// incremental state cannot be built over `atom_terms`.
fn drive_incremental(
    arena: &mut TermArena,
    atom_terms: &[TermId],
    literals: &[Literal],
) -> Option<IncrementalDecision> {
    let var_of: BTreeMap<TermId, usize> = atom_terms
        .iter()
        .enumerate()
        .map(|(v, &t)| (t, v))
        .collect();
    let mut state = CombinedIncremental::new(arena, atom_terms)?;
    state.push();
    for lit in literals {
        let Some(&var) = var_of.get(&lit.atom) else {
            continue; // an atom outside the numbering — cannot assert it (defer is sound)
        };
        if assert_to_fixpoint(&mut state, var, lit.value).is_err() {
            return Some(IncrementalDecision::Inconsistent);
        }
    }
    // No conflict: a definite verdict only when no interface pair stays Undetermined.
    let euf_assertions = live_euf_assertions(arena, literals);
    let pair_terms: Vec<(TermId, TermId)> =
        state.interface_pairs().iter().map(|p| p.terms).collect();
    let any_undetermined = classify_interface_equalities(arena, &euf_assertions, &pair_terms)
        .iter()
        .any(|c| c.1 == InterfaceStatus::Undetermined);
    Some(if any_undetermined {
        IncrementalDecision::Deferred
    } else {
        IncrementalDecision::Consistent
    })
}

/// Asserts `var := value` then drains the propagation fixpoint, asserting every entailed
/// literal in turn (so a conflict reachable only *through* a propagation is detected, as
/// production `CdclT` would). Returns `Err` on the first sub-theory conflict.
fn assert_to_fixpoint(
    state: &mut CombinedIncremental,
    var: usize,
    value: bool,
) -> Result<(), Vec<TheoryLit>> {
    state.assert(var, value)?;
    loop {
        let props = state.propagate();
        let mut progressed = false;
        for prop in props {
            // `assert` is idempotent at the same value and a no-op once assigned; it only
            // does work for a genuinely new entailment, which is the fixpoint progress.
            let before = state.assigned[prop.lit.atom];
            state.assert(prop.lit.atom, prop.lit.value)?;
            if before.is_none() {
                progressed = true;
            }
        }
        if !progressed {
            return Ok(());
        }
    }
}

/// The asserted `EUF` assertion terms for `literals` (a `true` eq atom is its term, a
/// `false` one its negation) — the input [`classify_interface_equalities`] reads to
/// decide each shared pair. This is the **same** `EUF` view `check`'s preamble classifies
/// against (the partition's EUF split over the original literals), so the Undetermined
/// test the harness uses to gate `Consistent` vs `Deferred` matches `check`'s case-split.
fn live_euf_assertions(arena: &mut TermArena, literals: &[Literal]) -> Vec<TermId> {
    let Some(part) = partition(arena, literals) else {
        return Vec::new();
    };
    build_euf_assertions(arena, &part.euf)
}
