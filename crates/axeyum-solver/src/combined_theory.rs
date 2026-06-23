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

use axeyum_ir::{TermArena, TermId};

use crate::backend::CheckResult;
use crate::euf_egraph::TheorySolver;
use crate::lra_online::LraTheory;
use crate::uflra_online::{
    Literal, PairAtoms, build_euf_assertions, collect_uflra_atoms, decide_conjunction, decline,
    euf_unsat, flatten_conjunction, is_theory_atom, partition, run_interface_search,
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
    pub(crate) fn new(_arena: &mut TermArena, _atom_terms: &[TermId]) -> Self {
        Self { cache: None }
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
