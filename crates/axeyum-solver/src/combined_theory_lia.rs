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

use axeyum_ir::{TermArena, TermId};

use crate::backend::CheckResult;
use crate::euf_egraph::TheorySolver;
use crate::lia_online::LiaTheory;
use crate::uflia_online::{
    Literal, PairAtoms, build_euf_assertions, collect_uflia_atoms, decide_conjunction, decline,
    euf_unsat, flatten_conjunction, interface_pairs, interface_terms, is_theory_atom, partition,
    run_interface_search,
};

/// Hard ceiling on interface case-split pairs, mirroring the cold core's `MAX_SPLIT_DEPTH`
/// decline so the warm and cold paths reject the same oversized splits identically.
const MAX_SPLIT_PAIRS: usize = 64;

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
    pub(crate) fn new(_arena: &mut TermArena, _atom_terms: &[TermId]) -> Self {
        Self { cache: None }
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
            let mut theory = LiaTheory::new(arena, &layout);
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
