//! Warm, equality-sharing `EUF` + `LIA` theory oracle for the online `QF_UFLIA`
//! combination (Track 1, P1.6 — the shared-`CDCL(T)`-combination keystone, slice 1).
//!
//! The Boolean (`DPLL(T)`) layer in [`crate::uflia_online`] decides each propositional
//! model's conjunction of theory literals with a from-scratch `Nelson–Oppen`
//! combination (`decide_conjunction`): every call rebuilds a fresh
//! [`crate::lia_online::LiaTheory`] (re-linearizing the atoms into the integer atom
//! builder) plus, per shared interface pair, three dynamically registered order/equality
//! atoms, and re-asserts the original `LIA` literals. That cold rebuild is repeated for
//! every early partial-assignment prune and every total model the enumeration tries.
//!
//! [`CombinedTheoryLia`] is the **warm** alternative. It performs the *identical*
//! combination as `decide_conjunction` — the same partition, the same interface pairs
//! (the `QF_UFLIA` **≥1-`EUF`-endpoint** rule, *not* `LRA`'s pure intersection), the same
//! `LiaTheory` atom layout, the same interface case-split DFS
//! ([`crate::uflia_online::run_interface_search`]), the same replay-checked integer leaf
//! model — but **caches** the constructed-and-base-asserted `LiaTheory` across calls. When
//! a subsequent conjunction has the *same* `LIA` atom layout (the common case during the
//! enumeration, where successive models differ only in their `EUF` / Tseitin
//! assignments), the cached theory is reused at its post-base-assert baseline rather than
//! rebuilt. The interface DFS restores the theory to that baseline on exit (every `push`
//! is paired with a `pop`), so the cached state stays reusable.
//!
//! **Soundness / equivalence.** Because the warm path computes the *same* per-call atom
//! layout and drives the *same* DFS over a `LiaTheory` with the *same* variable set as the
//! cold core, it returns the **identical verdict** (`Sat` / `Unsat` / `Unknown`, and the
//! same replay-checked integer model on `Sat`) to `decide_conjunction` on every input —
//! the parallel-run equivalence the slice-1 gate asserts. The warm path changes *only* the
//! lifetime of the theory solver, never the decision procedure. The `EUF` side is
//! stateless here (`euf_unsat` / the leaf's congruence / model build rebuild a small
//! e-graph per call, exactly as the cold core does), so only the `LiaTheory` construction
//! is warmed in slice 1.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use axeyum_ir::{TermArena, TermId};

use crate::backend::CheckResult;
use crate::euf_egraph::{EufTheory, TheoryLit, TheoryProp, TheorySolver};
use crate::lia_online::LiaTheory;
use crate::theory_combination::{InterfaceStatus, classify_interface_equalities};
use crate::uflia_online::{
    Literal, PairAtoms, Partition, build_euf_assertions, collect_uflia_atoms, decide_conjunction,
    decline, euf_unsat, flatten_conjunction, interface_pairs, interface_terms, is_theory_atom,
    partition, run_interface_search,
};

/// Hard ceiling on interface case-split pairs, mirroring the cold core's `MAX_SPLIT_DEPTH`
/// decline so the warm and cold paths reject the same oversized splits identically.
const MAX_SPLIT_PAIRS: usize = 64;

/// Mirror the pure-LIA online large-query threshold: once the combined UFLIA
/// layout reaches this size, the live LIA sub-theory records assignments and
/// performs one feasibility check at the propagation boundary instead of
/// re-solving after every asserted literal.
const DEFER_COMBINED_LIA_FEASIBILITY_ATOMS: usize = 128;

/// The warm `EUF` + `LIA` equality-sharing theory oracle (slice 1).
///
/// Constructed once over the `BoolSearch` atom set (the indices are not load-bearing —
/// the cache keys on the per-call atom layout, not the construction argument).
/// [`CombinedTheoryLia::check`] decides a conjunction of theory literals with the **same**
/// model-based combination as [`decide_conjunction`], reusing a cached `LiaTheory` when
/// the `LIA` atom layout repeats.
pub(crate) struct CombinedTheoryLia {
    /// The cached `LiaTheory` and its provenance, valid at its post-base-assert baseline:
    /// `(lia_atom_terms layout, pairs, pair_atoms, theory)`. `None` until the first
    /// cacheable conjunction. A new call whose `lia_atom_terms` differs rebuilds.
    cache: Option<Cached>,
    /// The full theory-atom set in `BoolSearch` variable order (index `v` is the atom
    /// term of propositional variable `v`). [`CombinedTheoryLia::propagate`] builds its
    /// warm `EUF` / `LIA` sub-theories over this whole set — asserting only the
    /// conjunction — so the sub-theories can entail the *unassigned* atoms, with the
    /// sub-theory atom index equal to the `BoolSearch` variable directly.
    atom_terms: Vec<TermId>,
    /// The inverse of `atom_terms`: each theory-atom [`TermId`]'s `BoolSearch`
    /// propositional variable. Used to assert a literal and to name an interface
    /// equality atom; an atom absent from it has no variable (its interface equality is
    /// then dropped — a sound omission, propagation only ever *adds* assignments).
    atom_var: BTreeMap<TermId, usize>,
    /// Optional wall-clock deadline inherited from the online Boolean driver.
    deadline: Option<Instant>,
}

/// One warm-reusable `LiaTheory` together with the layout it was built for.
struct Cached {
    /// The `LiaTheory` atom layout `[original LIA atoms] ++ [eq/lt/gt per pair]` — the
    /// cache key. A call with the same layout reuses `theory` at its baseline.
    layout: Vec<TermId>,
    /// The interface pairs (in `TermId` order) the layout's trailing atoms encode.
    pairs: Vec<(TermId, TermId)>,
    /// The `eq`/`lt`/`gt` `LiaTheory` indices per pair.
    pair_atoms: Vec<PairAtoms>,
    /// The theory, sitting at its baseline: the original `LIA` literals asserted, no
    /// interface atom on the trail. The DFS restores it here on exit.
    theory: LiaTheory,
}

impl CombinedTheoryLia {
    /// Builds the warm oracle. The construction argument warms nothing on its own (the
    /// cache fills lazily from the first conjunction); it is kept so the wiring mirrors
    /// the cold core's atom-set discovery and leaves room for a future eager pre-warm.
    #[must_use]
    pub(crate) fn new(arena: &mut TermArena, atom_terms: &[TermId]) -> Self {
        Self::new_with_deadline(arena, atom_terms, None)
    }

    /// Builds the warm oracle with a caller-owned deadline. Once that deadline
    /// passes, the nested `LIA` checks become inconclusive instead of producing
    /// conflicts or propagations.
    #[must_use]
    pub(crate) fn new_with_deadline(
        _arena: &mut TermArena,
        atom_terms: &[TermId],
        deadline: Option<Instant>,
    ) -> Self {
        let mut atom_var = BTreeMap::new();
        for (var, &atom) in atom_terms.iter().enumerate() {
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
    /// returning the **identical** verdict (and `Sat` integer model) the cold
    /// [`decide_conjunction`] would — the parallel-run equivalence contract. Reuses the
    /// cached `LiaTheory` when this call's `LIA` atom layout matches the cached one,
    /// otherwise rebuilds (and re-caches) it.
    pub(crate) fn check(&mut self, arena: &mut TermArena, literals: &[Literal]) -> CheckResult {
        // Steps 2–4: partition, interface pairs (the >=1-EUF-endpoint rule), the EUF
        // single-theory short-circuit — bit for bit the cold core's preamble, so a
        // decline / early Unsat here is identical.
        let Some(part) = partition(arena, literals) else {
            return decline("atom outside QF_UFLIA for the online combination path");
        };
        let interface = interface_terms(arena, &part);
        let pairs = interface_pairs(&interface);
        if pairs.len() > MAX_SPLIT_PAIRS {
            return decline("too many interface pairs for the online combination split");
        }
        let euf_assertions = build_euf_assertions(arena, &part.euf);
        if euf_unsat(arena, &euf_assertions) {
            return CheckResult::Unsat;
        }

        // Step 5: the per-call LIA atom layout (the original LIA literals, then three
        // interface atoms per shared pair) — identical to the cold core's `lia_atom_terms`.
        let mut layout: Vec<TermId> = part.lia.iter().map(|l| l.atom).collect();
        let mut pair_atoms: Vec<PairAtoms> = Vec::with_capacity(pairs.len());
        for &(s, t) in &pairs {
            let (Ok(eq), Ok(lt), Ok(gt)) = (arena.eq(s, t), arena.int_lt(s, t), arena.int_gt(s, t))
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
        // LIA literals — the same state the cold core constructs.
        let warm = matches!(&self.cache, Some(c) if c.layout == layout);
        if !warm {
            let mut theory =
                LiaTheory::new_with_opaque_apps(arena, &layout).with_deadline(self.deadline);
            for (index, lit) in part.lia.iter().enumerate() {
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

        let cached = self.cache.as_mut().expect("cache populated above");
        run_interface_search(
            arena,
            literals,
            &part.euf,
            euf_assertions,
            &cached.pairs,
            &cached.pair_atoms,
            &mut cached.theory,
        )
    }

    /// **Combined theory propagation** (slice 2): the literals the warm `EUF` + `LIA`
    /// combination *genuinely entails* under the conjunction `literals`, each expressed
    /// as a [`TheoryProp`] over the **`BoolSearch` propositional variable** numbering.
    /// A `DPLL(T)` loop assigns each without a decision, pruning the search — never
    /// changing the `Sat` / `Unsat` verdict. The integer mirror of
    /// [`crate::combined_theory::CombinedTheory::propagate`].
    ///
    /// Three sound, never-fabricating sources are unioned: `EUF` congruence entailments
    /// ([`EufTheory::propagate`]), `LIA` order entailments ([`LiaTheory::propagate`] —
    /// the LP-relaxation negation probe, sound over ℤ since integer points ⊆ real
    /// points), and interface-equality entailments ([`classify_interface_equalities`]
    /// over the asserted `EUF` state: `Entailed` ⇒ the pair's `(= s t)` atom true,
    /// `Refuted` ⇒ false). Every emitted literal is genuinely entailed and every reason
    /// literal is asserted-only.
    pub(crate) fn propagate(&self, arena: &mut TermArena, literals: &[Literal]) -> Vec<TheoryProp> {
        let Some(part) = partition(arena, literals) else {
            return Vec::new();
        };
        let asserted: Vec<Literal> = literals
            .iter()
            .copied()
            .filter(|l| self.atom_var.contains_key(&l.atom))
            .collect();
        let mut out: Vec<TheoryProp> = Vec::new();
        self.euf_propagations(arena, &asserted, &mut out);
        self.lia_propagations(arena, &asserted, &mut out);
        self.interface_propagations(arena, &part, &mut out);
        out
    }

    /// Source (a): `EUF` congruence entailments, over the whole atom set (atom index =
    /// `BoolSearch` variable), asserting only the conjunction.
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

    /// Source (b): `LIA` order entailments, over the whole atom set, asserting only the
    /// conjunction so [`LiaTheory::propagate`] entails the *unassigned* order atoms.
    fn lia_propagations(
        &self,
        arena: &mut TermArena,
        asserted: &[Literal],
        out: &mut Vec<TheoryProp>,
    ) {
        let mut lia =
            LiaTheory::new_with_opaque_apps(arena, &self.atom_terms).with_deadline(self.deadline);
        for lit in asserted {
            let var = self.atom_var[&lit.atom];
            if lia.assert(var, lit.value).is_err() {
                return; // a base LIA conflict — `check` reports it; nothing to propagate
            }
        }
        self.collect_props(&lia.propagate(), out);
    }

    /// Source (c): interface-equality entailments — the shared pairs the asserted `EUF`
    /// congruence pins `Entailed` / `Refuted`, mapped to the pair's `(= s t)` query
    /// variable, with the asserted `EUF` literals as the (asserted-only) reason.
    fn interface_propagations(
        &self,
        arena: &mut TermArena,
        part: &Partition,
        out: &mut Vec<TheoryProp>,
    ) {
        let interface = interface_terms(arena, part);
        let pairs = interface_pairs(&interface);
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
                InterfaceStatus::Undetermined => continue,
            };
            out.push(TheoryProp {
                lit: TheoryLit { atom: var, value },
                reason: reason.clone(),
            });
        }
    }

    /// Appends the sub-theory propagations (atom indices already `BoolSearch` variables,
    /// since built over the whole atom set) onto `out`, with a bound check that keeps the
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
/// `EUF` literal currently asserted, at its asserted polarity — asserted-only by
/// construction, a sound explanation for any congruence entailment the asserted `EUF`
/// state forces. Literals without a query variable are skipped (they cannot be named).
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
/// `assertions` flatten to a conjunction of `QF_UFLIA` theory atoms, decide it **both**
/// ways — the cold from-scratch [`decide_conjunction`] (the trusted reference) and the
/// warm [`CombinedTheoryLia`] oracle this slice introduces — and return their verdict
/// codes `(cold, warm)`. The test asserts `cold == warm` on every instance: a divergence
/// is the bug slice 1 must not have. The warm oracle is reused across the conjunction's
/// own repeated sub-checks here too (a second `check` on the same instance must hit the
/// cache and still agree). Returns `None` for a non-conjunctive or non-atom shape (those
/// are gated by the separate offline-Ackermann differential).
///
/// Not part of the production surface.
#[doc(hidden)]
#[must_use]
pub fn combined_lia_vs_cold_conjunction(
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

    // The cold reference verdict.
    let cold = verdict_code(&decide_conjunction(arena, &literals));

    // The warm oracle over the conjunction's atom set, checked twice so the cache-reuse
    // path is exercised (the second check must hit the warm baseline and still agree).
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen: std::collections::BTreeSet<TermId> = std::collections::BTreeSet::new();
    for &assertion in assertions {
        collect_uflia_atoms(arena, assertion, &mut atom_terms, &mut seen);
    }
    let mut combined = CombinedTheoryLia::new(arena, &atom_terms);
    let warm_first = verdict_code(&combined.check(arena, &literals));
    let warm_second = verdict_code(&combined.check(arena, &literals));
    debug_assert_eq!(
        warm_first, warm_second,
        "warm oracle must be stable across cache reuse"
    );

    Some((cold, warm_first))
}

/// **Combined-theory-propagation harness** (slice-2 soundness gate, test-only): build
/// the warm [`CombinedTheoryLia`] over the atom set `atom_terms` (the `BoolSearch`
/// numbering), assert the conjunction `asserted` (each `(atom term, polarity)`), and
/// return every literal [`CombinedTheoryLia::propagate`] genuinely entails as a
/// [`crate::combined_theory::PropagationReport`], so the slice-2 test can confirm each
/// is genuinely entailed (`asserted ∧ ¬entailed` `UNSAT` offline) and the reason
/// asserted-only. Returns `None` when `asserted` is not a conjunction of `QF_UFLIA`
/// theory atoms. Not part of the production surface.
#[doc(hidden)]
#[must_use]
pub fn combined_theory_lia_propagations(
    arena: &mut TermArena,
    atom_terms: &[TermId],
    asserted: &[(TermId, bool)],
) -> Option<Vec<crate::combined_theory::PropagationReport>> {
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
    let combined = CombinedTheoryLia::new(arena, atom_terms);
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

// --- Slice 3b-lia: the incremental, backtrackable combined-theory state. -----

/// How a combined-theory atom routes to the live sub-theories (slice 3b-lia). The
/// incremental [`CombinedIncrementalLia::assert`] consults this per propositional
/// variable to fan an assertion out to the owning sub-theory (or both, for a shared
/// atom). The integer mirror of [`crate::combined_theory`]'s `AtomRoute`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AtomRoute {
    /// A pure `LIA` order atom — asserted on the live `LiaTheory` only.
    Lia,
    /// A pure `EUF` (UF-touching, non-linear-integer) equality — asserted on the live
    /// `EufTheory` only.
    Euf,
    /// A linear-integer equality that also mentions a `UF` application — asserted on
    /// **both** sub-theories (the original atom is genuinely shared).
    Both,
    /// An interface `(= s t)` atom for shared pair index `pair` — asserting it merges
    /// / separates the pair on **both** the `EufTheory` (via the eq atom) and the
    /// `LiaTheory` (via its eq interface atom).
    InterfaceEq { pair: usize },
    /// An interface order atom (`s < t` / `s > t`) for a shared pair — asserted on the
    /// `LiaTheory` only (the `EufTheory` has no order relation).
    InterfaceOrder,
}

/// One registered shared-interface pair (slice 3b-lia): its `(s, t)` integer terms and
/// the freshly-allocated propositional variables of its three structural atoms
/// (`eq` / `lt` / `gt`), beyond the original Tseitin `atom_count`. Slice 3c-lia adds the
/// structural clauses (`eq ∨ lt ∨ gt`, mutual exclusion) over these variables to the
/// `SAT` clause DB and lets the generic [`Dpll`](crate::lra_online::Dpll) branch them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct InterfacePair {
    /// The shared integer terms `(s, t)`, in [`TermId`] order.
    pub(crate) terms: (TermId, TermId),
    /// The fresh propositional variable for `(= s t)`.
    pub(crate) eq_var: usize,
    /// The fresh propositional variable for `(int_lt s t)`.
    pub(crate) lt_var: usize,
    /// The fresh propositional variable for `(int_gt s t)`.
    pub(crate) gt_var: usize,
}

/// A structural clause over the registered interface variables (slice 3b-lia output): a
/// disjunction of `(variable, polarity)` literals.
pub(crate) type StructuralClause = Vec<(usize, bool)>;

/// **Incremental, backtrackable combined-theory state** (slice 3b-lia): live `EUF` +
/// `LIA` sub-theories over the **full** atom set `[original atoms ++ interface eq/lt/gt
/// per shared pair]`, with the up-front interface variables registered beyond the
/// original `atom_count`. It [`impl TheorySolver`](TheorySolver) so the generic
/// [`crate::lra_online::Dpll`] (slice 3c-lia) can drive it: each `SAT` trail assignment
/// of a theory atom is forwarded to the owning sub-theory
/// ([`CombinedIncrementalLia::assert`]), decisions backtrack in lockstep
/// ([`push`](CombinedIncrementalLia::push) / [`pop`](CombinedIncrementalLia::pop)), and
/// the combination's entailments are returned by
/// [`propagate`](CombinedIncrementalLia::propagate) reading the **live** sub-theories.
/// The integer mirror of [`crate::combined_theory`]'s `CombinedIncremental`.
///
/// **Atom routing.** Each propositional variable carries an [`AtomRoute`]: a pure order
/// atom goes to `LIA`, a `UF`-touching equality to `EUF`, a shared linear-integer-`UF`
/// equality to both, an interface `(= s t)` variable to both (merge/separate on `EUF`,
/// the `LIA` eq atom), an interface order variable to `LIA`. The fan-out keeps the two
/// sub-theories' shared-equality views in sync — the core of `Nelson–Oppen` combination.
///
/// **Interface-pair rule.** The shared pairs are computed by the `QF_UFLIA`
/// **≥1-`EUF`-endpoint** rule ([`interface_terms`] / [`interface_pairs`]) — *not* the
/// `LRA` pure-intersection rule — because `LIA` is not convex and an integer-tight bound
/// can force an interface equality with a `UF`-argument constant (e.g. `f(1)`) that never
/// appears in a `LIA` atom.
///
/// **Conflict cores.** Both sub-theories return **asserted-only** conflict cores over
/// their own atom indices (which are the combined variables directly, since each
/// sub-theory is built over the full combined layout). A core therefore names only
/// currently-asserted literals at their asserted polarity — exactly the shape `1-UIP`
/// conflict analysis in [`crate::lra_online::Dpll`] consumes.
///
/// **Validation (no [`Dpll`](crate::lra_online::Dpll) yet for 3b).** Slice 3b-lia keeps
/// the trusted per-call [`CombinedTheoryLia::check`] and validates this surface against
/// it (`combined_incremental_lia_vs_check`): driving the incremental surface to a
/// fixpoint and reading its verdict must AGREE with `check` on every case the incremental
/// surface *decides on its own*. Where an interface pair stays `Undetermined` (a genuine
/// case-split that only the slice-3c branching resolves), the incremental surface
/// honestly *defers* to `check` rather than guessing.
pub(crate) struct CombinedIncrementalLia {
    /// Live `EUF` sub-theory over the full combined atom layout (index = combined var).
    euf: EufTheory,
    /// Live `LIA` sub-theory over the same full combined atom layout.
    lia: LiaTheory,
    /// Per combined variable, how an assertion of it fans out to the sub-theories.
    routes: Vec<AtomRoute>,
    /// The registered shared-interface pairs (their structural variables + terms).
    pairs: Vec<InterfacePair>,
    /// Per combined variable, the value it is currently asserted at (`None` if free).
    assigned: Vec<Option<bool>>,
    /// The assignment log (combined variables assigned since the start, in order) —
    /// truncated back to a marker on [`pop`](CombinedIncrementalLia::pop).
    assigned_log: Vec<usize>,
    /// Backtrack trail: the `assigned_log` length saved at each
    /// [`push`](CombinedIncrementalLia::push).
    trail: Vec<usize>,
}

impl CombinedIncrementalLia {
    /// Builds the incremental combined state over `atom_terms` (the `BoolSearch` /
    /// Tseitin atom numbering). The shared-interface pairs are computed **once** up front
    /// from the full atom set by the `QF_UFLIA` ≥1-`EUF`-endpoint rule, and three fresh
    /// propositional variables — `eq` / `lt` / `gt` — are registered per pair *beyond* the
    /// original `atom_terms.len()`. The live `EufTheory` and `LiaTheory` are built over the
    /// resulting combined layout so a sub-theory atom index equals the combined variable
    /// directly.
    ///
    /// Returns `None` when the interface terms cannot be built (an arena failure) — the
    /// caller then falls back to the per-call [`CombinedTheoryLia::check`].
    #[must_use]
    pub(crate) fn new(arena: &mut TermArena, atom_terms: &[TermId]) -> Option<Self> {
        Self::new_with_deadline(arena, atom_terms, None)
    }

    /// Builds the incremental combined state with a caller-owned deadline. The
    /// deadline is forwarded to the `LIA` sub-theory so expensive theory asserts
    /// and model reconstruction degrade to `Unknown` once the caller's budget is
    /// exhausted.
    #[must_use]
    pub(crate) fn new_with_deadline(
        arena: &mut TermArena,
        atom_terms: &[TermId],
        deadline: Option<Instant>,
    ) -> Option<Self> {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        let original_atoms: Vec<TermId> = atom_terms.to_vec();

        // Shared pairs over the full atom set, once. Build a Partition from "all atoms
        // asserted true" purely to discover the EUF/LIA integer-term split; the polarity
        // does not affect which terms are shared.
        let all_true: Vec<Literal> = original_atoms
            .iter()
            .map(|&atom| Literal { atom, value: true })
            .collect();
        let part = partition(arena, &all_true)?;
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        let interface = interface_terms(arena, &part);
        let raw_pairs = interface_pairs(&interface);
        if raw_pairs.len() > MAX_SPLIT_PAIRS {
            return None;
        }

        let mut combined: Vec<TermId> = original_atoms.clone();
        let mut pairs: Vec<InterfacePair> = Vec::with_capacity(raw_pairs.len());
        for &(s, t) in &raw_pairs {
            if deadline.is_some_and(|d| Instant::now() >= d) {
                return None;
            }
            let (Ok(eq), Ok(lt), Ok(gt)) = (arena.eq(s, t), arena.int_lt(s, t), arena.int_gt(s, t))
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

        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        let routes = build_routes(&part, &original_atoms, &combined, &pairs);
        let euf = EufTheory::new(arena, &combined);
        let lia = if should_defer_combined_lia_feasibility(combined.len()) {
            LiaTheory::new_with_opaque_apps_deferred_for_large_search(arena, &combined)
        } else {
            LiaTheory::new_with_opaque_apps(arena, &combined)
        }
        .with_deadline(deadline);
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        let n = combined.len();
        Some(Self {
            euf,
            lia,
            routes,
            pairs,
            assigned: vec![None; n],
            assigned_log: Vec::new(),
            trail: Vec::new(),
        })
    }

    /// The registered shared-interface pairs (their fresh `eq` / `lt` / `gt` variables and
    /// `(s, t)` terms). Slice 3c-lia reads these to wire the structural clauses + the
    /// case-split branching into the generic [`Dpll`](crate::lra_online::Dpll).
    #[must_use]
    pub(crate) fn interface_pairs(&self) -> &[InterfacePair] {
        &self.pairs
    }

    /// The structural clauses over the registered interface variables (slice 3b-lia
    /// output, for slice 3c-lia's `SAT` clause DB). Per shared pair `(s, t)` with
    /// variables `eq` / `lt` / `gt`:
    ///
    /// - **totality** `eq ∨ lt ∨ gt` — exactly one order relation holds over the integers;
    /// - **mutual exclusion** `¬eq ∨ ¬lt`, `¬eq ∨ ¬gt`, `¬lt ∨ ¬gt` — at most one holds.
    ///
    /// Together they pin each shared pair to exactly one of `{=, <, >}` — the trichotomy
    /// the interface case-split branches. (The `EUF` ↔ `LIA` *tie* — that the `eq`
    /// variable's truth equals the pair's `EUF` congruence — is enforced dynamically by
    /// [`CombinedIncrementalLia::assert`] fanning the eq onto both sub-theories and by
    /// [`CombinedIncrementalLia::propagate`]'s interface entailments, not by a static
    /// clause.)
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

    /// Records `var := value` in the assignment log, classifying the assertion against any
    /// existing assignment of `var`: `Fresh` (newly recorded — fan it out), `Repeat`
    /// (idempotent at the same value — a no-op), or `Conflict` (asserting the *opposite*
    /// of an already-asserted value — a theory conflict).
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
    fn asserted_core(&self) -> Vec<TheoryLit> {
        self.assigned_log
            .iter()
            .filter_map(|&v| self.assigned[v].map(|value| TheoryLit { atom: v, value }))
            .collect()
    }
}

fn should_defer_combined_lia_feasibility(atom_count: usize) -> bool {
    atom_count >= DEFER_COMBINED_LIA_FEASIBILITY_ATOMS
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

impl TheorySolver for CombinedIncrementalLia {
    /// Asserts combined variable `var` at `value`, routing it to the owning sub-theory
    /// (or both, for a shared / interface-eq atom). Returns the conflicting **asserted**
    /// literal core (over combined variables) on inconsistency — suitable verbatim for
    /// `1-UIP` conflict analysis in [`crate::lra_online::Dpll`].
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
            AtomRoute::Lia | AtomRoute::InterfaceOrder => self.lia.assert(var, value),
            AtomRoute::Euf => self.euf.assert(var, value),
            AtomRoute::Both | AtomRoute::InterfaceEq { .. } => {
                self.euf.assert(var, value)?;
                self.lia.assert(var, value)
            }
        }
    }

    /// Saves a backtrack point on **both** sub-theories and the interface trail, in
    /// lockstep — so a later [`pop`](CombinedIncrementalLia::pop) restores all three to
    /// this point together.
    fn push(&mut self) {
        self.euf.push();
        self.lia.push();
        self.trail.push(self.assigned_log.len());
    }

    /// Undoes every assertion back to the most recent
    /// [`push`](CombinedIncrementalLia::push), on both sub-theories and the interface
    /// trail, in lockstep.
    fn pop(&mut self) {
        self.euf.pop();
        self.lia.pop();
        if let Some(marker) = self.trail.pop() {
            while self.assigned_log.len() > marker {
                if let Some(var) = self.assigned_log.pop() {
                    self.assigned[var] = None;
                }
            }
        }
    }

    /// Combined-theory propagation over the **live** sub-theories: the `EUF` congruence
    /// entailments + the `LIA` order entailments, read incrementally. Indices are combined
    /// variables directly (each sub-theory is over the full combined layout), so the
    /// [`Dpll`](crate::lra_online::Dpll) consumes them without translation, and each reason
    /// is asserted-only.
    ///
    /// The interface `eq` atoms are themselves registered in the live `EufTheory`, so an
    /// `Entailed` interface equality is emitted *by* [`EufTheory::propagate`] (its two
    /// sides congruent) with no extra interface pass. The `Refuted` direction (an interface
    /// eq forced *false*) is not emitted: `EufTheory` defers disequality-entailment, and
    /// **omitting** a propagation is always sound — it only forgoes pruning, never a
    /// verdict. (Slice 3c-lia's structural clauses still let the
    /// [`Dpll`](crate::lra_online::Dpll) branch the refuted pair, so completeness is
    /// unaffected.)
    fn propagate(&self) -> Vec<TheoryProp> {
        let mut out: Vec<TheoryProp> = self.euf.propagate();
        out.extend(self.lia.propagate());
        out
    }
}

/// Builds the per-variable [`AtomRoute`] table for the combined layout. The original
/// atoms are routed by their **`partition` membership** — the *same* classification the
/// per-call [`CombinedTheoryLia::check`] uses — so the incremental routing cannot diverge
/// from the trusted path: an atom in `part.lia` only ⇒ `Lia`, in `part.euf` only ⇒ `Euf`,
/// in both (a shared linear-integer-`UF` equality) ⇒ `Both`. The trailing variables are
/// the registered interface atoms (eq → `InterfaceEq`, lt/gt → `InterfaceOrder`), looked
/// up from `pairs`.
fn build_routes(
    part: &Partition,
    original_atoms: &[TermId],
    combined: &[TermId],
    pairs: &[InterfacePair],
) -> Vec<AtomRoute> {
    let in_lia: BTreeSet<TermId> = part.lia.iter().map(|l| l.atom).collect();
    let in_euf: BTreeSet<TermId> = part.euf.iter().map(|l| l.atom).collect();
    let mut routes = vec![AtomRoute::Euf; combined.len()];
    for (var, &atom) in original_atoms.iter().enumerate() {
        routes[var] = match (in_lia.contains(&atom), in_euf.contains(&atom)) {
            (true, true) => AtomRoute::Both,
            (true, false) => AtomRoute::Lia,
            // EUF-only, or (defensively) neither — assert on EUF, a no-op for a
            // non-equality atom, never on LIA where a spurious constraint could mislead.
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

/// The incremental surface's self-decided verdict on a conjunction (slice-3b-lia
/// harness): `Inconsistent` when an `assert` (after the propagation fixpoint) hits a
/// sub-theory conflict; `Consistent` when every literal asserts cleanly **and** no shared
/// interface pair stays `Undetermined` (so no case-split — a definite verdict the
/// incremental surface owns without a `Dpll`); `Deferred` when an interface pair is
/// `Undetermined` (a genuine case-split slice 3c-lia's branching must resolve).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IncrementalDecision {
    /// A sub-theory conflict — the conjunction is `Unsat`.
    Inconsistent,
    /// No conflict and every shared pair determined — `check` must agree (not `Unsat`).
    Consistent,
    /// An `Undetermined` interface pair remains — deferred to the slice-3c-lia case-split.
    Deferred,
}

/// **Slice-3b-lia incremental-vs-`check` validation harness** (soundness gate,
/// test-only): drive the [`CombinedIncrementalLia`] surface over a conjunction of theory
/// literals and return *both* its self-decided verdict ([`IncrementalDecision`]) and the
/// trusted per-call [`CombinedTheoryLia::check`] verdict code, so the test can assert they
/// agree on every case the incremental surface decides on its own. The integer mirror of
/// [`crate::combined_theory`]'s `combined_incremental_vs_check`.
///
/// Returns `None` for a non-conjunctive / non-atom shape, or when the incremental state
/// cannot be built (the same shapes [`CombinedTheoryLia::check`] declines).
///
/// Not part of the production surface.
#[doc(hidden)]
#[must_use]
pub fn combined_incremental_lia_vs_check(
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
        collect_uflia_atoms(arena, assertion, &mut atom_terms, &mut seen);
    }

    let decision = drive_incremental(arena, &atom_terms, &literals)?;

    // The trusted per-call verdict over the same atom set.
    let mut combined = CombinedTheoryLia::new(arena, &atom_terms);
    let check = verdict_code(&combined.check(arena, &literals));
    Some((decision, check))
}

/// The registered interface structure of a [`CombinedIncrementalLia`] (slice-3b-lia
/// harness, test-only): the number of original atoms, the registered interface pairs as
/// `(eq_var, lt_var, gt_var)` triples, and the structural clauses over those variables.
/// Lets the slice-3b-lia test confirm the slice-3c-lia hand-off surface is well-formed:
/// every interface variable is fresh (≥ the original atom count) and distinct, and the
/// structural clauses reference only registered variables.
///
/// Returns `None` for shapes the incremental state declines.
///
/// Not part of the production surface.
#[doc(hidden)]
#[must_use]
#[allow(clippy::type_complexity)]
pub fn combined_incremental_lia_structure(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<(usize, Vec<(usize, usize, usize)>, Vec<Vec<(usize, bool)>>)> {
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    for &assertion in assertions {
        collect_uflia_atoms(arena, assertion, &mut atom_terms, &mut seen);
    }
    let original_count = atom_terms.len();
    let state = CombinedIncrementalLia::new(arena, &atom_terms)?;
    let pairs: Vec<(usize, usize, usize)> = state
        .interface_pairs()
        .iter()
        .map(|p| (p.eq_var, p.lt_var, p.gt_var))
        .collect();
    Some((original_count, pairs, state.structural_clauses()))
}

/// Drives the [`CombinedIncrementalLia`] surface over `literals` and returns its
/// self-decided [`IncrementalDecision`] (the slice-3b-lia harness core). `None` when the
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
    let mut state = CombinedIncrementalLia::new(arena, atom_terms)?;
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
/// the slice-3c-lia [`Dpll`](crate::lra_online::Dpll) would). Returns `Err` on the first
/// sub-theory conflict.
fn assert_to_fixpoint(
    state: &mut CombinedIncrementalLia,
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
/// `false` one its negation) — the input [`classify_interface_equalities`] reads to decide
/// each shared pair. This is the **same** `EUF` view `check`'s preamble classifies against
/// (the partition's EUF split over the original literals), so the Undetermined test the
/// harness uses to gate `Consistent` vs `Deferred` matches `check`'s case-split.
fn live_euf_assertions(arena: &mut TermArena, literals: &[Literal]) -> Vec<TermId> {
    let Some(part) = partition(arena, literals) else {
        return Vec::new();
    };
    build_euf_assertions(arena, &part.euf)
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Sort;

    fn iconst(arena: &mut TermArena, n: i128) -> TermId {
        arena.int_const(n)
    }

    fn ivar(arena: &mut TermArena, name: &str) -> TermId {
        let s = arena.declare(name, Sort::Int).expect("declare int");
        arena.var(s)
    }

    #[test]
    fn large_combined_opaque_lia_defers_feasibility_to_propagation() {
        let mut arena = TermArena::new();
        let mut atoms = Vec::new();

        for i in 0..DEFER_COMBINED_LIA_FEASIBILITY_ATOMS {
            let y = ivar(&mut arena, &format!("pad_{i}"));
            let zero = iconst(&mut arena, 0);
            atoms.push(arena.int_ge(y, zero).expect("pad>=0"));
        }

        let f = arena
            .declare_fun("f", &[Sort::Int], Sort::Int)
            .expect("declare f");
        let x = ivar(&mut arena, "x");
        let fx = arena.apply(f, &[x]).expect("f(x)");
        let zero = iconst(&mut arena, 0);
        let one = iconst(&mut arena, 1);
        let fx_le_zero = arena.int_le(fx, zero).expect("f(x)<=0");
        let fx_ge_one = arena.int_ge(fx, one).expect("f(x)>=1");
        let le_var = atoms.len();
        atoms.push(fx_le_zero);
        let ge_var = atoms.len();
        atoms.push(fx_ge_one);

        assert!(should_defer_combined_lia_feasibility(atoms.len()));
        let mut state =
            CombinedIncrementalLia::new(&mut arena, &atoms).expect("combined state builds");

        assert!(
            state.assert(le_var, true).is_ok(),
            "large combined state should record opaque LIA assertions cheaply"
        );
        assert!(
            state.assert(ge_var, true).is_ok(),
            "deferred mode should not re-solve on every opaque LIA assertion"
        );

        let props = state.propagate();
        let conflict = props
            .iter()
            .find(|prop| state.assigned[prop.lit.atom] == Some(!prop.lit.value))
            .expect("deferred feasibility conflict should surface as a propagation");
        let mut core = conflict.reason.clone();
        core.push(TheoryLit {
            atom: conflict.lit.atom,
            value: !conflict.lit.value,
        });
        assert!(
            core.iter().any(|lit| lit.atom == le_var && lit.value)
                && core.iter().any(|lit| lit.atom == ge_var && lit.value),
            "conflict core should name both opaque contradictory bounds: {core:?}"
        );
    }
}
