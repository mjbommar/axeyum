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

use std::collections::BTreeMap;

use axeyum_ir::{TermArena, TermId};

use crate::backend::CheckResult;
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
    pub(crate) fn new(_arena: &mut TermArena, atom_terms: &[TermId]) -> Self {
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
            let mut theory = LraTheory::new(arena, &layout);
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
        let mut lra = LraTheory::new(arena, &self.atom_terms);
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

    // The cold reference verdict.
    let cold = verdict_code(&decide_conjunction(arena, &literals));

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
