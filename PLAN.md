# Axeyum plan, status, and next actions

> **Generated; do not edit by hand.** Sources: project-wide sections in
> [`docs/plan/global/`](docs/plan/global/README.md), one file per lane in
> [`docs/plan/status/`](docs/plan/status/README.md). Edit **your lane's file**
> and run `python3 scripts/gen-plan.py`; `--check` is a gate. This file was
> touched 67 times in 24 hours by concurrent lanes on 2026-08-13/14 and one
> lane's edit was swept into another's commit — that is what the split fixes.

**Canonical project tracker.** This is the repository's single mutable source
for current project status, ordered work, blockers, and resume guidance. Read it
first and update it before ending a project-level work session.

- Last consolidated: **2026-08-13**
- Current `main` contains linear A5 through exact commit
  `4b6b765556c4ff1fb4dc47ffd75568a3ed1f9246` by conflict-free fast-forward
- Active A5 large-equality DL repair: code at exact pushed
  `46edad8bac7e193303871d601914fef2115bf721`; its documentation descendant
  `d1b570f91c27f83ef55127ea3d1c8baf700f05a5` passed the full release gate
- Latest full-gate attempt: exact pushed checkpoint `d1b570f91c27f83ef55127ea3d1c8baf700f05a5`
  passed `just check` with external frontier artifacts and exit 0
- Latest comprehensive green exact-commit gate:
  `d1b570f91c27f83ef55127ea3d1c8baf700f05a5` (`just check` exit 0)
- Latest integrated A3 code increments: bounded SMT-LIB `distinct` expansion at
  `63c82a6ef`, typed arithmetic-model reconstruction at `4ff9a82c6`, and
  deterministic string/integer coupling at `db7b426e8`
- Status vocabulary: `TODO` · `WIP` · `BLOCKED` · `DONE`

`STATUS.md` is now a compatibility pointer. There is intentionally no root
`TODO.md`. Detailed phase plans, ADRs, result notes, generated matrices, and
benchmark ledgers remain under [`docs/plan/`](docs/plan/README.md),
[`docs/research/`](docs/research/README.md), and
[`bench-results/`](bench-results/README.md). They provide evidence and task
detail; they do not override the order or current state in this file.

Pre-consolidation journals are immutable in Git at revision `803c08439`.

## Status

**A5 repair history.** Fail-closed LRA/IDL restarts exposed wide-core and
first-solve allocation growth, mixed-numeric parsing, native recursion,
unhonored construction deadlines, and declaration-scale quadratic work. Their
pushed bounded/iterative repairs and every non-credited partial stream are
retained in the
[failure/repair record](docs/plan/qf-linear-a5-wide-core-memory-repair-2026-08-08.md);
the current release returns typed `unknown` on each former abort trigger.

Axeyum is a working research-grade automated-reasoning stack with a pure-Rust
default path, replay-checked SAT models, multiple independently checked UNSAT
evidence routes, broad but uneven theory support, an independent Lean-core
checker/importer, and several consumers. It is not yet a drop-in Z3 replacement
or a replacement for the Lean system.

The [Lean requirements](docs/plan/lean-kernel-requirements-2026-08-13.md) are
**WIP**. Nat is zero-axiom; Int reconstruction remains assumption-bearing.

Exact pushed repairs for the A5 (linear-arithmetic), A3 (string/integer) and
A2 (stale-branch) streams — commit-by-commit, with the non-credited partial
streams retained — are in the
[A5/A3/A2 repair journal](docs/plan/a5-a3-repair-journal-2026-08.md). The
current release returns typed `unknown` on each former abort trigger; A3 yields
to A4.

### A1 arithmetic resource closure

A1 is **DONE**. Resource increment `96ff85930` (merge `14f80a2bf`) resolves the
two measured arithmetic resource defects:

1. ADR-0377 makes arithmetic timeout query-global across sequential exact-real,
   NRA, real-relaxation, NIA-linearization, bounded-blast, and width-ladder
   routes. The same absolute deadline is polled inside solver-local CAD
   polynomial, projection, determinant, exact-division, and rational-cell loops.
   The public QF_NIA `ext-rew-aggr-test` now returns `Unknown(Timeout)` in 0.30 s
   for a 250 ms optimized request instead of 1.10 s; a committed debug regression
   finishes in 0.28 s and requires less than 1 s.
2. Online LRA normalization now has deterministic node, coefficient-work, and
   retained-cache ceilings. Production entry points distinguish deadline expiry
   from resource exhaustion and return `Unknown(Timeout)` or
   `Unknown(ResourceLimit)` rather than constructing a partial theory. The
   existing 1,024-atom front-door cap remains; current `sc-39.base.cvc.smt2`
   declines in 0.10 s at roughly 13 MiB instead of reproducing the historical
   8 GiB abort seen when that cap was experimentally raised.

Focused resource gates are green: deadline 6/6, online-LRA 7/7, CAD 37/37, the
normalization exhausted/near-miss unit, full all-feature solver Clippy, format,
and documentation links. The terminal aggregate solver gate
`CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --all-features --quiet --
--test-threads=2` passed 1,073 library tests and every integration/doctest bin,
including the 397.85-second UFLIA and 286.00-second word-equation differential
tests. `just parity-docs` is independently green at 35 rows, 24 logics, 992
files, 762 decided, 674 oracle-compared, and zero disagreements; its unrelated,
load-sensitive frontier refresh was discarded.

All six required retained lists were rerun fresh from row 1. Results are QF_NIA
34/200 versus 89, QF_LIA 117/200 versus 140, QF_LRA 86/200 versus 146, QF_RDL
105/200 versus 155, QF_IDL 68/200 versus 124, and QF_UFLIA 94/200 versus 180;
all have zero disagreements. The sole lower whole-sweep decision, one QF_LIA
`ex3000...` UNSAT, reproduced 3/3 in isolation at about 8.1 seconds under the
24-second protocol and is classified as load-sensitive sweep timing, not a
semantic loss. The ledger honestly retains 117.

The QF_IDL run exposed and then closed a real fallback-reservation regression.
Commit `4477f2bb9` bounds every probe-front-end phase and uses a measured 12/12
probe/fallback split only for 128–1,024-atom numeric equality gates; a global
12/12 split was rejected after losing five controls. A 171-case QF_IDL/QF_RDL
A/B was monotone. The final full sweep recovers `lpsat-goal-18.smt2` as UNSAT,
retains the BubbleSort gain, adds one SAT graph case, and has no Axeyum loss.

Commit `5ce07c55e` (merge `8ea6a7cad`) also makes parity resume identity
fail-closed: exact committed-list paths are canonical; ambiguous legacy
basenames, duplicate rows, and population drift are rejected. The six accepted
A1 runs were fresh and non-resumed. Full evidence, sidecar hashes, rejected IDL
policies, and gate separation are retained in
[`docs/plan/arithmetic-a1-retained-result-2026-08-06.md`](docs/plan/arithmetic-a1-retained-result-2026-08-06.md).

Disk cleanup preserved every branch and salvaged dirty inactive-worktree deltas
to labelled Git stashes before retiring their checkouts. Reproducible Cargo
artifacts and empty failed-run directories were removed only after ancestry,
cleanliness, and open-file checks. Only clean `main` remains registered; retained
evidence and unrelated temporary projects were untouched.

### Current evidence snapshot

- The committed regression scoreboard contains **35 baselines across 24 logic
  fragments**: **762/992** files decided, **674** oracle-compared, and **zero
  recorded disagreements**. This is bounded regression evidence, not universal
  soundness or representative SMT-LIB coverage. See
  [`bench-results/SCOREBOARD.md`](bench-results/SCOREBOARD.md).
- The refreshed 4-second frontier artifacts report BV reduction **38**
  (baseline 30), LIA cuts **35** (baseline 26), NIA UNSAT **40** (baseline 40),
  NRA degree **40** (baseline 40), and string bound **40** (baseline 8). These
  are load-sensitive local frontier measurements; they do not raise baselines.
- The append-only head-to-head ledger currently covers **eleven divisions**.
  Its weak measured edges are QF_NIA **34/89 = 38.2%**, QF_UFLIA
  **94/180 = 52.2%**, QF_IDL **68/124 = 54.8%**, QF_LRA
  **86/146 = 58.9%**, and QF_RDL **105/155 = 67.7%**. Every credited entry has
  zero disagreements. Read the latest entry per division in
  [`bench-results/PARITY.md`](bench-results/PARITY.md); never copy an older
  entry merely because it has a higher score.
- QF_BV evidence mode decides 130 UNSAT rows: **92/130 certified**,
  **78/130 rechecked from serialized text alone**, and **92/92 certified rows
  independently checked against a fresh re-parse and term arena**. Neither
  check had a failure. The remaining 38 are bare UNSAT decisions because the
  evidence-producing route could not decide them within 60 seconds.
- The broader evidence audit still records **58 uncertified occurrences**,
  **eight independently checked results without Lean reconstruction**, and
  **two QF_NIA `IntPow2` proof-production errors**. Do not combine these
  denominators with the newer QF_BV-only experiment.
- The current official-source proof-family population has a retained local
  Lean 4.30 result of **70/70 accepted**. A corrected remote attestation and the
  exhaustive tier remain open. Lean language, ecosystem, and complete native
  compatibility remain far beyond the current K0/K1 slices.
- The previous 64,345-file full-library candidate is not a result: it produced
  zero admissible raw shards. Resumable/process-free readiness work exists, but
  a representative current-main run has not been admitted or published.

### Recent landed changes that set the next direction

| Date | Commit | Result |
|---|---|---|
| 2026-08-21 | `231a3992e` | Combined every retained Haar level before identity-path localization, reducing the sharp first-endpoint price to one aggregate path with 17 odd or 18 even half-contractions still unproved after the exact translation split. |
| 2026-08-21 | `79e1c4a6e` | Proved that translation `f(x)->f(x+1)` forces exact half balance at identity-path level `2^v_2(n)`, spent that split in the endpoint ledger, and retained the remaining 19-split obligation and power-of-two boundary explicitly. |
| 2026-08-21 | `2da5c9b4c` | Factored each retained Haar layer's polynomial identity share down the nested Witt path, reducing it to 20 half-balanced splits among 190 available levels at the first endpoint and exposing every exact parent/child mass without claiming the open split theorem. |
| 2026-08-21 | `1a9145641` | Reduced the identity-cylinder variance to the polynomial share `16ell^2 F_j(1)<=F_j(global)`, exposed its exponentially permissive weak-kurtosis sufficient form, and added exact implication and fourth-power diagnostics without claiming the open delocalization theorem. |
| 2026-08-20 | `b1b4f407a` | Added exact local/global Haar layer energies, refuted perfect uniform sharing on control rows, and priced a stronger linear local-Carleson diagnostic with exponential endpoint surplus. |
| 2026-08-20 | `79c5c95c8` | Reduced REL to one exact identity-cylinder conditional variance, reconstructed its localized Haar/Carleson energy level by level, and proved that Newton-over-Hodge divisibility by eight gives no endpoint rounding gain. |
| 2026-08-20 | `c59ae115d` | Refuted relative-trace positivity with exact negative odd/even rows after smooth localization, preventing unit local terms from being substituted for the still-required global REL comparison. |
| 2026-08-20 | `838fd5e3e` | Proved that every proper odd-endpoint `Frob*c` orbit collapses to the cone vertex and every projective fixed point is smooth, transverse, and has unit local multiplicity, while retaining the unbounded global trace as REL. |
| 2026-08-20 | `fbeb97a2b` | Proved the odd-endpoint projective cycle eigenlines smooth and transverse with exact Vandermonde Jacobians and tangent weights, while correcting the relative Lefschetz--Verdier source and retaining the distinct `Frob*c` trace as open. |
| 2026-08-20 | `0d6b5a524` | Added bounded binary Hankel `(rho,pi)` characteristics with exhaustive independent rank controls, while proving from source scope that the published divisor variance does not supply the signed prime-weighted higher moment or REL. |
| 2026-08-20 | `7e1c34a41` | Applied the zero-2-rank trace theorem to the exact relative Carlitz Jacobian quotient, proved its endpoint content is only parity, and stopped scalar Artin--Schreier or elementary-abelian bounds from receiving REL credit. |
| 2026-08-20 | `33a259776` | Replaced the uniform TOP-POLY maxima by the exact one-sided relative identity trace, lowered the first endpoint saving price from 1,583 to 626, and rewrote the two-page manuscript around the weaker REL obligation. |
| 2026-08-20 | `604504e20` | Wrote the two-page paper-facing Lemire reduction, marked TOP-POLY as its sole open lemma, and froze the fail-closed manuscript contract in ADR-0571. |
| 2026-08-20 | `2530ff1cb` | Repriced the surviving endpoint argument against the proved Haar triangle, selected the weaker TOP-POLY saving on only the top logarithmic conductor window, and added an exact parity-safe implication through the degree-400 handoff. |
| 2026-08-20 | `c6c0dc238` | Refuted the absolute conductor-layer constant by exact fixed-level recurrence, retained the corrected polynomial-loss theorem, and reduced its open range to growing conductors above the individual-Weil prefix. |
| 2026-08-20 | `d9380f0d7` | Reduced the wild fourth-moment target to exact-conductor delocalization, proved the `C=4` prefix through level three, and added a fail-closed finite diagnostic plus the polynomial-loss endpoint implication. |
| 2026-08-20 | `f729f3ad1` | Translated Hast--Matei into the exact proper-power-aware endpoint normalization, exposed the missing degree-uniform wild constant, and sharpened the even proper-power envelope by eliminating all odd exponent layers. |
| 2026-08-20 | `b01ac7cd6` | Classified every shape-preserving polynomial composition, added certified tower search, and refuted the proposed degree `8 -> 64 -> 512` chain by exhaustive degree-eight controls. |
| 2026-08-20 | `dd6dcd94a` | Corrected the weak fourth-moment target to retain proper-power subtraction, rejected the proposed KLLM/Efron shortcut at theorem and finite-scaling levels, and generalized Capell to every odd monomial power with 371/174 independently reproduced finite seeds. |
| 2026-08-20 | `833806e24` | Expanded exact dyadic fibre `L^2`, proved the inverse-difference parallelogram criterion `h*t*(t+h)=0`, and reduced the conjectural nonpositive defect to a restricted four-shift Mobius correlation without granting endpoint credit. |
| 2026-08-20 | `9a49f2023` | Inserted Wan--Zhang's sharper complete-intersection Betti theorem into the exact Foulkes endpoint ledger and quantified its remaining 6,800-bit miss, isolating cyclic-eigenspace cancellation rather than generic total cohomology as the needed theorem. |
| 2026-08-20 | `6f4a275db` | Audited the proposed Newton-polygon literature at source level, recording its odd-prime or `Z_p`-tower scope and preventing those nearby results from being substituted for the binary product-group theorem. |
| 2026-08-20 | `29f3c4d94` | Stopped the fixed modulo-eight endpoint route after the exact degree-55 counterexample `I_55(1)=4883944`, marked the universal congruence refuted, and returned theorem effort to an aggregate trace estimate. |
| 2026-08-20 | `2233fa65f` | Re-aimed the odd endpoint at exact normalized two-adic traces, proved Carlitz 2-rank zero is insufficient for the required modulo-eight precision, and added exact primitive-character Newton polygons that isolate aggregate low-slope cancellation as the open lemma. |
| 2026-08-20 | `3c332b648` | Replaced the overstrong characteristic-delta common-period target by the exact product of maximal-subfield differences, added charged native support witnesses and an independent field oracle, and retained universal nonvanishing as the explicit open lemma. |
| 2026-08-20 | `40df3c8ee` | Added uniqueness-bounded one-prime odd-endpoint reconstruction, blocked conductor-width power-sum history, executable NTT assumptions, and exact fleet rows through degree 51 without granting the surviving mod-eight pattern theorem credit. |
| 2026-08-20 | `0e9a3ca9d` | Reduced the complete Lemire class to one characteristic-delta convolution period, added dual exact controls, and isolated the universal no-proper-period lemma without granting finite evidence theorem credit. |
| 2026-08-20 | `531ed174a` | Translated Hast--Matei's top long-cycle variance at the exact endpoint, proved its second moment is insufficient, and confined the selected characteristic-two repeated-root defect to square proper powers. |
| 2026-08-20 | `636f9da38` | Classified the projective long-cycle eigenlines, proving that exactly `phi(oddpart(n))` survive and rejecting a free cyclic-torsor shortcut without granting a Frobenius bound. |
| 2026-08-20 | `35b4c6ad2` | Pinned the exact degree-five separation between zero unweighted non-top Euler trace and nonzero binary Frobenius error `-2`, preventing the cone identity from receiving endpoint credit. |
| 2026-08-20 | `ada2c4542` | Closed the purely wild power-of-two Euler row by the homogeneous-cone decomposition and exposed the surviving projective Frobenius--long-cycle trace with exact factor `2^r-1`. |
| 2026-08-20 | `1c517c87f` | Localized the long-cycle Euler trace by its tame/wild decomposition, proving exact non-top cancellation away from power-of-two degrees while retaining the Frobenius-weighted trace as unproved. |
| 2026-08-20 | `18062735c` | Certified the Frobenius-square parity decomposition, its exact squarefreeness criterion, and the failure of the naive irreducibility induction without granting finite complement searches theorem credit. |
| 2026-08-20 | `6c6e36597` | Certified the exact long-cycle cyclic/Foulkes compression, retained odd/even proper-power margins, and isolated a quartic characteristic-two cyclic-Betti theorem that would close every degree after 400 without claiming it. |
| 2026-08-20 | `9a3e77556` | Derived the exact ell-three degree-seven extension trace from characteristic-two period-24 symmetry, reproduced the sharded GF(16) row, and refuted the one-extra-q cutoff repair. |
| 2026-08-20 | `ef5a90f0b` | Added an atomic bounded fleet shard runner and used the exact GF(16) level-three merge to refute the apparent ell^4 connected Adams trace allowance without granting endpoint credit. |
| 2026-08-20 | `6b064750d` | Added deterministic connected extension-field class-vector shards, fail-closed exact merge, CLI JSON workflows, and mutation-tested equality with direct connected Adams traces. |
| 2026-08-20 | `4d162d984` | Classified every binary projective repair of odd-degree Artin--Schreier doubling, reducing it to an impossible translation case, an explicitly reducible transvection case, or the existing cyclotomic/Q candidate. |
| 2026-08-20 | `ac41b35d0` | Added the exact connected high-frequency L2/Cauchy ledger and showed that structural-support Cauchy still requires savings 1425/1483 on pinned endpoint rows. |
| 2026-08-20 | `dfc581025` | Embedded the coarse inverse-additive spectrum into the fine domain, proved every inflated coarse frequency cancels in the connected projector, and exposed the exact surviving high-frequency Möbius sum. |
| 2026-08-20 | `32746e3f4` | Decomposed the connected top-conductor trace exactly by Möbius order and proved on pinned endpoint rows that low orders survive, requiring signed cross-order cancellation. |
| 2026-08-20 | `c949b166f` | Classified every half-shaped standard characteristic-two Q-transform via self-reciprocity and Dickson invariants, proving the certified cubic-to-sextic pair is the sole irreducible exception. |
| 2026-08-20 | `0cbcafe68` | Derived the exact `(ell,n)=(2,5)` connected trace polynomial from the characteristic-two trace/subtrace formula and proved its normalized q-degree exceeds the proposed universal cohomology cutoff by one. |
| 2026-08-20 | `ff09b9baa` | Added exact connected Adams traces over binary extension fields, cross-checked the base field, and used the exhaustive `(ell,n,r)=(2,5,5)` row to refute the universal `ell^4` Betti budget while retaining the separate cutoff question. |
| 2026-08-20 | `702191bff` | Reconstructed the product-one Adams convolution and all three Wick projectors, then exposed the exact degree-`4ell` cohomology cutoff and `ell^4` Betti budget needed for endpoint credit without claiming either. |
| 2026-08-20 | `5bdebc271` | Added bounded generalized Fomenko restriction/Galois packets, proved their exact conductor reconstruction, and refuted a one-square-root-unit bound for both one-coordinate and endpoint-matched logarithmic quotients. |
| 2026-08-20 | `254be42f7` | Proved that Katz's pointwise character fourth moment is a different contraction from the product-constrained Hayes cumulant and retained the missing uniform Betti bound. |
| 2026-08-20 | `a38675b8f` | Expanded the fourth cumulant into exact positive fibre products and proved that the connected target is a signed virtual trace, not an off-diagonal point count. |
| 2026-08-20 | `0b6d6d79a` | Proved that binary monomial power-sum characters cover at most the thin primitive quadratic sector and none of every even conductor layer. |
| 2026-08-20 | `783006fcd` | Added an exact two-prime Galois/Ramanujan orbit trace decomposition, refuted one-unit orbit and coefficient-four order-layer bounds, and retained the connected cross-order target. |
| 2026-08-20 | `0a459d914` | Made the exact Hayes root-number audit fail closed with a quadratic work-cell admission and checked the primitive functional equation coefficient by coefficient. |
| 2026-08-20 | `8b07f7a45` | Added exact integral cyclotomic Hayes L-polynomials and proved that every pinned primitive root-number fibre contains distinct endpoint power sums, rejecting root-number-only Gauss control. |
| 2026-08-20 | `726bd8411` | Audited the 2026 function-field Linnik--Selberg input at equation level and rejected its varying-modulus average as a substitute for the fixed-wild-modulus, Möbius-weighted endpoint sum. |
| 2026-08-20 | `556888c96` | Added the checked cubic Capell criterion and dual-checker audit, proving 138 committed seeds generate 95 infinite degree rays while explicitly retaining the uncovered odd and even 3-free degrees. |
| 2026-08-20 | `f85830458` | Added a bounded characteristic-two Q-transform with independent irreducibility controls, retained its special cubic-to-sextic success and cyclotomic degree family, and proved the standard iterated hypothesis forces a forbidden upper-half coefficient. |
| 2026-08-20 | `6d6e1a7d8` | Added deterministic and hierarchical binary extension-trace sharding, exact Frobenius-orbit compression and Hankel minors, and used the complete `A_7(9,4)` trace to exclude every recurrence of order at most three without claiming endpoint proof credit. |
| 2026-08-19 | `1705eb688` | Proved Gao's binary Hayes L-degree distribution from exact conductors and quantified why its aggregate degree retains the fatal endpoint factor. |
| 2026-08-19 | `0db0c7ffd` | Added bounded native fixed-degree traces over binary extension fields, separating genuine Frobenius-power long-cycle diagnostics from the base-field Hayes population. |
| 2026-08-19 | `9e3cb37a4` | Audited Sawin's characteristic-two singular-support argument, rejected every elementary-abelian Fomenko small-kernel variant, and required genuinely equivariant or higher-Witt input. |
| 2026-08-19 | `1b4f3503f` | Audited Ito--Takeuchi--Tsushima at equation level and required a checked linearized quadratic reduction or new mixed associative cocycle before importing its characteristic-two Heisenberg nondegeneracy. |
| 2026-08-19 | `f01dfe8e0` | Extended both exact endpoint cumulant and local Witt-cylinder concentration diagnostics through `ell=23`, retaining exact ratios, fleet resource provenance, and the non-credit theorem boundary. |
| 2026-08-19 | `540c4d41f` | Retained pairwise second-trace quadratic forms inside simultaneous buckets and refuted the raw high-rank Kerdock model with exact rank-zero/rank-two Gauss witnesses. |
| 2026-08-19 | `9c24671a6` | Reconstructed the pinned dyadic product-discriminant fibre and used its exact mod-four additivity witness to reject every projection-preserving central extension. |
| 2026-08-19 | `d56410d21` | Certified the exact dyadic auxiliary-unit quadratic projector, including its cyclotomic Gauss identity, polarization, radicals, and squareful-zero cancellation. |
| 2026-08-19 | `786a16b5c` | Summed the exact top-conductor character second moments and showed that direct Cauchy loses factors 304/633 at the pinned endpoints, selecting a phase-preserving argument instead. |
| 2026-08-19 | `74c40427e` | Refuted a blanket supersingular decomposition of every new Carlitz conductor layer using the exact level-ten degree-22 trace-divisibility obstruction. |
| 2026-08-19 | `7cb9c1ce3` | Identified the connected top-conductor trace with a relative Carlitz point trace, checked its Artin--Schreier tower and genus ledger, and quantified the exact linear saving still missing beyond relative Hasse--Weil. |
| 2026-08-19 | `7582fbf7b` | Telescoped the identity path into one signed relative top-conductor trace, added a quarter-scale connected endpoint budget, and retained all cross-conductor cancellation before absolute values. |
| 2026-08-19 | `9c146dcc9` | Combined exact-conductor Fourier inversion with the proved individual Weil bound, reducing the open square-root-fibre estimate from every level to only `ceil(log2 ell)+1` top conductor levels. |
| 2026-08-19 | `039d905a6` | Reconstructed every endpoint population from raw binary Witt sibling imbalances, added an exact sufficient Haar triangle, and isolated a buffered square-root-fibre bound that closes both symbolic endpoint ledgers. |
| 2026-08-19 | `b24120651` | Proved the naive first-slot projection across all binary Witt blocks has kernel order `2^floor(ell/2)`, rejecting a direct growing-conductor Fomenko generalization before expensive `L`-factor work. |
| 2026-08-19 | `07ed9bb8d` | Rejected direct magic-square gcd matrices for the full connected character tuple, then added an exact local Witt-cylinder concentration ledger whose root and singleton boundaries independently recover the fourth/second moments. |
| 2026-08-19 | `1a75298ea` | Expanded every endpoint discrepancy by convolution order, subtracted all three Wick pairings cellwise, and exactly reconstructed the connected fourth cumulant as the signed symmetric order tensor required for gcd stratification. |
| 2026-08-19 | `1b4d42d60` | Applied the exact primitive modulo-eight autocorrelation criterion to every affine fibre, found zero generalized-bent fibres in the pinned obstruction, and pivoted from fibrewise Heisenberg rank to connected fourth-cumulant/gcd strata. |
| 2026-08-19 | `8e3ec9324` | Rejected positive four-phase complementarity by exact integer autocorrelation, pinned the large off-identity mass, and preserved the indefinite Gauss combination as the only viable phase-level input. |
| 2026-08-19 | `09d70c7f5` | Retained the full modulo-eight phase in the connected Witt object, reconstructed the signed spectrum by a mutation-checked four-phase Gauss identity, and showed every primitive additive phase still has full Fourier support in the pinned witness. |
| 2026-08-19 | `84ea01df2` | Embedded every signed valuation layer into one checked Witt group before absolute values, computed exact spectral moments and conductor support, ruled out sparse/imprimitive support in the pinned witness, and recorded the missing cocycle boundary for a valid Heisenberg rank. |
| 2026-08-19 | `4527543a4` | Exposed the connected off-diagonal square-root target, pinned the necessary factor-two boundary, and checked that the conjectural bound would imply the desired endpoint energy scale without claiming the remaining cross-order theorem. |
| 2026-08-19 | `a226f25ef` | Aggregated exact dyadic autocorrelation fibres by shift/inverse pair, the checked Artin--Schreier product parameter, and valuation; exposed the large finite cancellation while refuting the simplest valuation envelope. |
| 2026-08-19 | `ebdfc678d` | Reconstructed the product-discriminant phase on every exact affine autocorrelation fibre and showed that nonquadratic fibres are substantial, moving the dyadic target to cancellation across shift/inverse-difference parameters. |
| 2026-08-19 | `125b2131e` | Computed every integral discriminant residue modulo eight by fraction-free elimination, reconstructed its exact coefficient ANF, and proved its full-support coefficient is always odd, ruling out a global bounded-degree phase shortcut. |
| 2026-08-19 | `c43e7bb68` | Extended the Swan sign to the universal identity `mu(f)=(-1)^degree chi_8(Disc(F))`, including squareful zeros, and checked its exact four-phase cyclotomic Fourier expansion. |
| 2026-08-19 | `11e781a03` | Exposed the native odd-generator factors as checked truncated binary Witt blocks and projected every simultaneous coset onto all order-two characters, showing the failed translation witness is not confined to a tiny real sector. |
| 2026-08-19 | `a0b13e7a6` | Cross-checked every squarefree binary polynomial Mobius sign by factor parity, integral discriminant modulo eight, and second-trace Arf invariant through degree ten, while preserving squareful zero weights and the boundary against claiming cancellation. |
| 2026-08-19 | `43da1d4c1` | Averaged the combined Berlekamp/inverse shift energy exactly over annihilators, proved its squarefree diagonal, refuted the constant-one scale, and exposed global and fibrewise conjectural targets with exact endpoint ledgers. |
| 2026-08-19 | `b9eebcdab` | Reduced every inverse-coset shift fibre to a truncated binary Artin--Schreier equation, proved its exact kernel dimension, and attached a checked unsigned support ceiling to every energy row. |
| 2026-08-19 | `0aeeb68d8` | Moved the extended endpoint-energy sweep behind an explicit ignored probe while retaining bounded theorem checks in the ordinary gate. |
| 2026-08-19 | `e587bb854` | Added an exact Berlekamp-plus-inverse stationary-fibre and Cauchy ledger for the residual aggregate, checked the squarefree phase boundary, and pointed the universal Autogenesis fact at the live Möbius-convolution obligation. |
| 2026-08-19 | `381748943` | Replaced the crude binary divisor factor by an exact finite-degree optimizer, carried the proved wrapped-energy ceiling through every endpoint Vaughan row, and showed the former ideal tail is not yet rigorous. |
| 2026-08-19 | `85e9ba5cd` | Regrouped the signed Möbius convolution exactly by Fourier annihilator depth, added the odd-endpoint buffered-tail margin ledger, and isolated the weighted summation-by-parts obligation. |
| 2026-08-19 | `0cf536a9d` | Added exhaustive endpoint Vaughan tables across every convolution order and source split, confirming the pointwise transition while retaining all suppressed-loss and non-credit boundaries. |
| 2026-08-19 | `b4c13c14e` | Proved the wrapped `q=2,F=x^r` inverse-energy envelope by exact valuation, lift, and divisor ledgers; corrected the no-wrap strictness and added loss-aware bilinear substitution. |
| 2026-08-19 | `9c891a0a6` | Completed replayable Bagshaw Type-I Case-1 and Case-2 ledgers with exact integer domains, binary completion exponents, and independently enumerated optimizer controls. |
| 2026-08-19 | `2a21ca519` | Proved inverse-additive energy stabilizes for `ell>=3d`, classified the rational collision fibres to obtain `E_inv<=2^(2d+o(d))`, and added an exact energy-to-Type-II exponent ledger. |
| 2026-08-19 | `d33c43e5e` | Scoped the binary Bagshaw Case-5 obstruction to its actual domain, proved it is empty for every Lemire cutoff, and checked that Hsu's older half-coefficient shorthand does not close the exact endpoint. |
| 2026-08-19 | `eef2032e5` | Completed the source-level Bagshaw dependency audit and added exact non-credit-bearing exponent ledgers that isolate the binary Type-I Case-5 obstruction and the uncovered endpoint interval range. |
| 2026-08-19 | `e0398d06a` | Added exact inverse-additive interval energy and Walsh fourth moments with independent collision controls, a characteristic-two source audit, and an explicit boundary against finite no-wrap inference. |
| 2026-08-19 | `329e842c6` | Recorded the exact inverse-additive Fourier and reciprocal-polynomial bridge in the canonical research note and lane status. |
| 2026-08-19 | `3c3be779a` | Added the exact inverse-additive Möbius Walsh spectrum, annihilator reconstruction, and frequencywise direct controls for the reciprocal-polynomial and ramified-`x` bridge. |
| 2026-08-19 | `c021db86a` | Added a direct Berlekamp-factorization oracle for every endpoint convolution term through level 5, with mutation controls for inverse-class and interval-weight errors. |
| 2026-08-19 | `53eeeda49` | Reduced the endpoint discrepancy to one exact signed Möbius-convolution sum, added a one-table native reconstruction with endpoint controls, and exposed the remaining uniform bound as an uncredited ledger obligation. |
| 2026-08-19 | `0e9bacef9` | Added exact signed classwise polynomial-Mobius distributions with dual-modulus reconstruction, independent Berlekamp-factorization controls, and an explicit boundary against unproved weighted cancellation. |
| 2026-08-19 | `88288f006` | Exposed the stationary-phase bound as an uncredited formal fact obligation so Autogenesis can see it without mistaking bounded tests for a universal certificate. |
| 2026-08-19 | `6e02ac7d6` | Proved the uniform binary wild-Kloosterman amplitude bound by stationary phase, exposed its bounded native CAS report, and pinned exhaustive direct controls through level 9. |
| 2026-08-19 | `afec92512` | Isolated the top inverse-coefficient plateau-spectrum candidate, its exact connection to `V_(ell-1)^2`, and dual local/fleet evidence through `ell=26` without granting theorem credit. |
| 2026-08-19 | `0513b1a22` | Generalized the equal-degree product energy to every ordered interval-degree pair, proved the two closed-form regimes, and checked all mixed collision tables through `ell=8`. |
| 2026-08-19 | `31b862946` | Added the exact closed-form principal-unit product energy and Fourier fourth moment, with direct native collision-table controls and an explicit boundary against the still-open Mangoldt moment. |
| 2026-08-19 | `5fac62cbb` | Added the bounded exact half-interval Möbius identity, pinned its first positive-composite parity counterexample with native Berlekamp factorization, and ruled out Porritt's explicit bound at `q=2`. |
| 2026-08-19 | `77209a5ee` | Added exact fourth moments/cumulants, checked the conditional implication and low control, retained level-23 evidence, and recorded open facts. |
| 2026-08-19 | `068e0fbff` | Added the exact resource-bounded fourth-moment conductor filtration, quotient-projection controls, public diagnostic, and literature boundary refresh. |
| 2026-08-19 | `fd9b3633d` | Corrected the fourth-moment ledger contract from an impossible irreducible mean to the exact Mangoldt-weighted population used by the CAS and conditional proof. |
| 2026-08-19 | `448be3674` | Added bounded exact Hayes prime-power inversion, exposing and invariant-checking the native identity-class irreducible count without an external CAS. |
| 2026-08-19 | `7cba6d63f` | Reduced every odd endpoint exactly to `N_(2ell+1)(1)>1`, with a bounded divisor certificate and full-inversion controls; closed `f -> x f+1` as an even-degree bridge. |
| 2026-08-18 | `cf998788b` | Automated the exact authoritative B-then-A chain; two isolated fixed-budget runs matched all 56 retained artifact bytes and passed Autogenesis-1. |
| 2026-08-18 | `2d65f19d8` | Froze the leakage-safe nursery contract and the Autogenesis-1 longitudinal partition; readiness remains explicitly false with zero evaluation facts and nine blockers. |
| 2026-08-18 | `bd7b55bff` | Extracted 9,729 proof-isolated Mathlib Nat/Int statements externally and selected 240 outcome-blind source candidates across twelve families without vendoring bulk exports. |
| 2026-08-18 | `30e7e6ec3` | Projected 95 direct Mathlib candidate dependencies into 146 whole leakage components without exposing proof terms or freezing evaluation splits. |
| 2026-08-18 | `f4dc0d4f1` | Registered and cleanly exercised the exact axiom-free authoritative B operation, whose durable event made A newly ready. |
| 2026-08-17 | `67960fc1c` | D3 grouping refuted at the point of execution: arithmetic-as-a-directory grows the largest dependency cycle 58,215 → 103,514 lines. `analyze_solver_group_collapse.py` + mutation controls; no files moved. |
| 2026-08-17 | `d23a9d883` | `Nat.exists_prime_dvd` — every `m ≥ 2` has a prime divisor — admitted axiom-free in a new `nat_prelude::primes` module, with `Nat.le_of_dvd`, `Nat.two_le_succ_or_eq_one` and `Nat.least_divisor_search` beneath it (137 Nat theorems, up from 133). Recorded as `F:nat-exists-prime-dvd`, whose `kernel-term` checker pins the entire rendered type rather than the name — verified against the `1 ≤ p` weakening, which the kernel accepts and a name-only grep would not catch. |
| 2026-08-17 | `8f8c12dce` | ℕ-induction wired into `solve` as the last rung of the quantified ladder (`unknown` → `unsat` only, on `original_assertions` because normalization + skolemization have erased the negated universal by that point). New `tests/nat_induction_adversarial.rs`: 22 adversarial shapes, hand-derived truths, measured on the route and through the front door, 0 violations. Fixed an index-out-of-bounds panic in `is_nonneg_guard` on one-argument guards. `nat_induction_corpus` re-measured (3 contradictions → 0) and its gate widened to the front-door column. Both suites mutation-verified. Blast radius: `--lib` 1159 unchanged, `corpus_regression` 152/0 DISAGREE unchanged, whole crate 285 suites / 3861 tests green, clippy and fmt clean. |
| 2026-08-17 | `7337f708` `caaf2906` | A SKOLEMISED refutation certifies: the elimination is recorded POSITIONALLY (binder counts, anchor by index, a binding as "the k-th witness of assertion i"), so the checker re-runs the eliminator in its own arena and no producer-side id is trusted. `F:barber-no-such-barber` closes on `smt-clausal` with a NON-EMPTY axiom footprint naming skolemisation and universal instantiation. The negative control failed on purpose and moved to `F:no-integer-square-is-minus-one`; the gate now sweeps 18/18. |
| 2026-08-17 | `ae13cd6e` | A kernel fact's `depends_on` is DERIVED from the proof term, not transcribed: `Kernel::theorem_dependencies` keeps the half of the constant closure `axiom_footprint` discards. 18 edges were missing — two of them on facts proved the same day, by hand. Isolation 65 → 62. Restraints pinned by tests; the vacuity floor had no test until mutation-checking found it killed zero. |
| 2026-08-17 | `07ffe852` `9853fb6c` `28755674` | The e-matching route certifies, on the third design. It first shipped `certified=1` on evidence whose independent re-check said FAIL (one instance passed by `TermId` coincidence, two did not); reverted, then made portable — instances rebuilt in the checker's arena, ground set rebuilt rather than stored. `tests/certified_implies_revalidatable.rs` is the guard that caught it and now licenses it. |
| 2026-08-17 | `c2365718` `4cd5d6f0` `c5f4c04b` `078b2776` | The Lean gate stops overstating: 41 of 74 crosscheck families hand Lean an `axiom P` shim, so the headline is split, the reasoning half floored, and every fragment's class pinned by name. `qf_bv` was a WIDTH, not a defect — enumeration beats bit-blasting below ~16 bits — so `qf_bv_wide` now exercises the real reconstruction (33 theory / 41 attestation). |
| 2026-08-17 | `3cc574c7` `502c0503` | Both counted proof-production errors closed (`int_blast`'s deliberate `int.pow2` decline was mapped to a backend error, losing a verdict `check_auto` decides in 0.13ms), and settled SMT-route facts gated on certification rather than verdict — 17 of 17, enforced. |
| 2026-08-17 | `ea9500bc` `e97db72b` `2c535667` `f40f7dc4` | Gate repairs: `check-parity-docs.py` crashed before running a single check (hiding 14 failures); CI's crosscheck grep still pinned 73 families; and `PLAN.md`'s sources were 24 KB over a 52 KB budget, journal moved to result notes. |
| 2026-08-17 | `07de6526` | Mathematics strand's primary metric derived and gated: 36 of 101 capabilities name an external artifact checker, across 11 of 23 logics, against a documented 4 of 26. Control: disabling the external tier drops it to 0 and the floor fires. |
| 2026-08-17 | `pending` | Denominator counts LOGICS not `area` strings: a compound like `QF_UFLIA/UFLRA` spans two, and its abbreviated second element named a phantom `UFLRA`. The 12 logics with no external check are now an explicit queue. |
| 2026-08-17 | `f18904db7` | R3: reachability census re-derived and committed as `artifacts/reachability/r3-census.tsv` (190 rows over both corpora); the ranked tables in `04-reachability.md` are now a generated view of it, gated by `scripts/check-reachability-census.py` inside `check-foundational-resources.sh`. 13 guards, each with its own rejection path; mutation-verified that deleting any one kills exactly one test. Corpus coverage checked in both directions and reported SKIPPED, never passed, when the sibling checkout is absent. Stale numbers corrected in `04` and `05`. |
| 2026-08-16 | `pending` | Claim dashboard regenerated and gated: `gen-claims-dashboard.py --check` added and wired into `generated-trackers` (justfile) and `check.sh`; `validate-claims.py` now type-checks `frontier.known` / `would_settle` / `attack_notes` against `claim.schema.json`; the one schema-violating claim normalised. DASHBOARD.md goes from a stale 38 claims / 1 family / 81 rows to the actual 104 / 3 / 266. Both negative controls exercised. |
Older landed changes (including the 2026-08-06 A1/A2 closure commits) remain
in Git and their dated result notes; this table is deliberately bounded to
changes that still determine the immediate queue.

## Next Actions

Work in this order unless new evidence reveals a wrong verdict, crash, data-loss
risk, or invalid gate. Those are P0 and preempt the queue.

The ordered ten-item programme remains A2 through A11. A1 and A2 are retained
here as closed evidence boundaries. A3 remains incomplete, but all currently
preregistered bounded mechanisms are closed negatively. A4 has now also yielded;
A5 is the first active item.

**Autogenesis-1 is frozen; the nursery is truthfully not ready.** Commit
`2d65f19d8` reserves the exact B-to-A chain as a longitudinal regression and
adds component-, family-, proof-shape-, and mutation-safe train/development/
held-out rules. The executable baseline has zero evaluation facts and nine
named blockers. This is intentional: the current 110-fact ledger has only 23
direct proof-derived kernel edges across ten consequents, and relabelling it
would leak the known Nat component rather than measure generalization.

**Mathlib source harvesting is proof-isolated.** Commit `bd7b55bff` binds exact
Mathlib/Lean/extractor identities, retains 9,729 statement-only Nat/Int rows
externally, and commits 240 source candidates across twelve families. The
extractor never emits theorem values, and the candidate selector reads no
checkout, full export, proof, or Axeyum outcome. These rows are not nursery
facts and do not change the nine-blocker readiness result.

**Dependency leakage is now measured.** Commit `30e7e6ec3` derives 95 direct
candidate-to-candidate proof edges from an evaluation-only Mathlib pass and
groups all 240 candidates into 146 indivisible weak components. The durable
projection contains names and edges only; its state remains explicitly
`dependency-metadata-not-frozen-split`.

**Next:** review statements and aliases, author statement-strength mutations,
label proof-shape risks from statement structure, then freeze whole dependency/
mutation groups into train/development/held-out membership. Do not expose proof
bodies to search, treat Mathlib proof as Axeyum construction, or begin proof-plan
work before fixed-budget nursery episodes identify the dominant seam.

**D3 grouping is BLOCKED, not queued (`BLOCKED`, solver-arith-group,
2026-08-17).** Sent to execute the one D3 group the 2026-08-17 edge measurement
supported (arithmetic; the other three were refuted). Re-measured first, and did
not move any files — two reasons, both in
[`03-solver-decomposition.md`](docs/refactor-2026-08/03-solver-decomposition.md)
under "Measured 2026-08-17 (second pass)".

1. The first pass committed no script, so its membership rule is unrecoverable
   and its arithmetic verdict does not survive re-derivation: sweeping plausible
   boundaries moves the degree-matched p from <0.0001 (23 modules) to 0.377 (39),
   crossing out of significance **at the 34–35 modules the first pass itself
   reported** (p = 0.110). Only the `strings` row reproduces exactly, because
   zero internal edges pins the set.
2. The move fails the gate for every membership. A directory is *one* node in
   `analyze_solver_module_graph.py`, so grouping merges nodes and creates cycles
   no member had. Best case (23-module core): `mbp` newly enters the theory
   core's cycle and the largest cycle grows **58,215 → 103,514 lines**, 25.8% →
   45.8% of the crate, while its module count moves 24 → 25. Every wider
   membership also adds `arith -> reconstruct`, destroying D1's precondition.

Landed the measurement as code instead — `scripts/analyze_solver_group_collapse.py`,
exit status is the finding — so the next lane decides this before moving a file
rather than after.

**Next:** not this. The blocker is the arithmetic ↔ `auto` / `reconstruct`
cycle; D3's sequencing item 3 now depends on item 4 (`D1` narrowing), not the
other way round. Whoever takes that: run
`scripts/analyze_solver_group_collapse.py --group arith-core --check` and watch
it go green — that is the exit criterion, and it is currently red.

**Both of Euclid's missing ingredients are in; `F:nat-exists-prime-gt` is one
slice from closing** (`WIP`, nat-prime-divisor, 2026-08-17).
`Nat.exists_prime_dvd : ∀ m, 2 ≤ m → ∃ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) ∧ p ∣ m`
is admitted axiom-free, recorded as `F:nat-exists-prime-dvd`. It did **not** go
through `lt_well_founded`, which is what the previous lane's note predicted:
strong induction on `m` has to *decide* primality of `m`, and a bounded `∀` is
not decidable constructively without a bounded search anyway — so the search is
done directly, by ordinary `Nat.rec` on the bound, returning the **least**
divisor `≥ 2`. Leastness is what makes primality free; a proper divisor of the
least divisor would be a smaller divisor of `m`. Each step decides `succ j ∣ m`
by reducing `beq (mod m (succ j)) 0`, with the branches separated by the checked
`div_mod_remainder_eq_zero_iff_dvd`. Nothing classical, nothing well-founded.

**A theorem-only slice is kernel-guarded, but its *statement* is not.** No
`Definition` was added, so there is no degenerate computation rule to fear — the
kernel refuses a false theorem and a non-prime witness never gets in. What the
kernel cannot see is a statement weaker than intended. Measured: spelling the
primality bound `1 ≤ p` instead of `2 ≤ p` still type-checks, still admits, and
passes every pre-existing test including axiom-freedom and the determinism
count — and is satisfied by `p = 1`. That mutation was run and killed **exactly
one** test, the new one, which compares the admitted type against an
independently built term. The fact's `kernel-term` checker greps the whole
rendered type for the same reason; a name-only grep survives the mutation.

**Next.** Close `F:nat-exists-prime-gt`. Two small steps remain, both resting
only on already-admitted axiom-free lemmas: (1) `1 ≤ Nat.factorial n` (induction,
`one_le_mul` at the successor), which is what makes `2 ≤ 1 + n!` and so lets
`exists_prime_dvd` apply to it at all; (2) the assembly — take `p` prime with
`p ∣ 1 + n!`; if `p ≤ n` then `dvd_factorial_of_le` gives `p ∣ n!`, `add_comm`
reshapes the sum, `dvd_add_right_cancel_of_pos` yields `p ∣ 1`, and
`not_dvd_one_of_two_le` refutes it; `le_total` then leaves `n ≤ p` and
`lt_or_eq_of_le` sharpens it to `n < p`.

**ℕ-induction is in dispatch; the front door now decides 4 of the 12 corpus
instances where it decided 1** (`WIP`, induction-dispatch, 2026-08-17).
`prove_by_nat_induction` had been built, exported, and deliberately kept out of
`solve` because it applied ℕ-induction to goals quantified over all of `Int` and
answered `unsat` for satisfiable sets. `a32280b6a` made a recognised `n >= 0`
guard mandatory; this lane re-measured that fix, attacked it, and wired the route
in as the last rung of the quantified ladder.

Re-measurement of `corpus/regression/uflia_induction` (12 instances): the three
`unguarded_*` rows are declines and the four unique `unsat` decisions survive —
**0 status contradictions, down from 3**. The route decides `guarded_linear_
closed_form`, `guarded_linear_nonneg`, `guarded_monotone_step` and
`guarded_parity_range`; the two nonlinear-step instances (`guarded_sum_gauss`,
`guarded_product_factorial_bound`) still overrun.

**No wrong `unsat` was found, and one crash was.** The new
`tests/nat_induction_adversarial.rs` carries 22 shapes chosen because a plausible
recogniser gets them wrong, each with a hand-derived truth and its witness — a
`<= n 0` guard, `>= 0 n`, `>= n (- 5)`, `>= (+ n 1) 0`, a guard on a *different*
variable, a vacuous `true` guard, a disjunctive guard admitting `-1`, nested
binders, a conclusion carrying its own quantifier, binders shadowing free
symbols, nested and n-ary implications, three multi-goal orderings. Every one
declines, on the route alone and through the front door. The defect that surfaced
was arity, not soundness: `is_nonneg_guard` bound `(args[0], args[1])` before
matching the operator, so a one-argument guard (`(=> (not (= n 5)) …)`, legal
SMT-LIB) panicked — unreachable while the route sat outside dispatch, a
front-door crash the moment it did not.

Both suites are mutation-verified, not assumed live. Restoring the
pre-`a32280b6a` fall-through turns 8 of 22 probes into wrong `unsat` and kills
exactly one test; disabling the dispatch rung kills exactly one test in each of
the two suites that assert it fires, and nothing else.

One thing worth carrying forward: **`corpus_regression` could not have caught
this either way.** That gate calls `check_auto` — the quantifier-*free* dispatch
— while the rung lives in `solve`, so its 152 files / 0 DISAGREE is unchanged and
structurally blind to this change. The `nat_induction_corpus` gate now checks the
front-door column as well as the route's own, because a wrong `unsat` from a
wired rung is a shipped verdict.

**Next.** Two things the measurement names. (1) The nonlinear step obligations:
`2·s(n) = n(n+1)` and `fact(n) ≥ 1` both time out in the step, so the rung stops
exactly where NIA does — that is a NIA task, not an induction task. (2) The
recogniser declines any goal whose *other* assertions include a quantifier it
cannot instantiate, which is why all three multi-goal probes decline; widening
`hypotheses` to carry a universal it cannot instantiate as an assumption rather
than dropping the goal would reach them. Neither is a soundness item.

**WIP** (`gf2-lemire`, 2026-08-21).  The non-strict statement is independently
checked through degree 400.  Bounded native CAS operations now cover Hayes
populations, moments/conductor filtration, and exact prime-power inversion.
At odd endpoints they certify `N_(2ell+1)(1)=1+(2ell+1)I_(2ell+1)(1)`; hence
only the strict analytic bound `N_(2ell+1)(1)>1` remains there.  Even endpoints
still require the checked general proper-power subtraction.  The CAS now also
has proved closed forms for every pair of principal-unit interval degrees:
exact mixed product energies and nonprincipal Fourier `L^2 x L^2` moments.
The phase-two conductor audit reduced the wild fourth-moment target to one
exact-conductor delocalization estimate `(SUP-L)`.  A native
integer diagnostic retains the finite rational constant without theorem
credit, while a separate symbolic checker proves that any fixed polynomial
loss yields `M_4<=625 C ell^(a+4)2^(3ell)` and completes the degree-400
handoff.  The initially selected absolute constant is now refuted exactly at
`(ell,n,j)=(27,56,4)`, with an arbitrary-precision recurrence witness at
`(343,688,4)` beyond the finite handoff; compact-torus recurrence proves that
no absolute constant can be uniform in the conductor.  The corrected target
allows the squared polynomial loss `4ell^4`; ordinary Weil then discharges
every level with `2^(j-1)<=4ell^4`.  Only the growing range above roughly
`4log2(ell)+3` remains for that sufficient route.  Exact repricing against the
already proved Haar triangle removes one factor of `ell` and most conductor
levels: `(TOP-POLY)` asks only for a `12ell/5` improvement over individual
Weil on the top `4ceil(log2 ell)+1` levels.  It remains sufficient, but the
paper has now been repriced against the exact identity path.  The selected
`(REL)` target keeps the top `ceil(log2 ell)+2` conductor levels in one signed
Carlitz trace and bounds only its harmful negative direction.  A native exact
implication spends the complete proved low-Weil envelope; at `ell=200` it
reduces the required separate-Weil saving from 1,583 to 626, asymptotically
`4ell+O(log ell)`.  The two-page LaTeX manuscript carries a fail-visible
warning, states `(REL)` as its sole open lemma, and contains the checked Haar,
parity, proper-power, and finite-handoff implications needed once that lemma
lands.  The relative quotient's zero `2`-rank has now been priced at source
level rather than treated heuristically: Cramer--Xing supplies only trace
parity because its relative abelian dimension exceeds the endpoint extension
degree.  The resulting rounding gain is at most one integer, versus REL's
factor-626 saving at `ell=200`.  Scalar Artin--Schreier code bounds and
elementary-abelian point-count bounds do not apply to the complete
non-elementary Witt zero fibre.  The fixed-`q` Hankel route is now natively
representable by an exact bounded binary `(rho,pi)` rank primitive, exhaustively
cross-checked against independent row-span enumeration.  Its source theorem is
only a divisor-function second moment: the higher-moment extension retains the
all-quasi-regular additive stratum, and `Lambda=mu*deg` restores the signed
cross-order convolution.  It therefore supplies representation, not REL.
The odd long-cycle eigenlines are now locally complete: their endpoint
Jacobians are full-rank Vandermonde matrices, and their exact projective
tangent weights prove smooth isolated transversality.  Independent binary
extension-field elimination checks the literal Jacobians.  This does not
localize the different `Frob*c` correspondence: its ordinary fixed locus is
the original short-interval count.  A source audit also corrected the relative
Lefschetz--Verdier pointer to Lu--Zheng arXiv `2005.08522`; that functorial
theorem supplies no numerical REL estimate, while the previously cited arXiv
`2309.02587` is a singular-support paper.  The actual odd-endpoint `Frob*c`
fixed locus is now locally complete as well.  Every proper Frobenius-orbit
stratum has odd multiplicity, lies inside the triangular zero-prefix range,
and collapses to the affine cone vertex.  Consequently every projective fixed
point has a full distinct-root orbit, Vandermonde Jacobian rank `ell`, and a
transverse unit local term because Frobenius has zero differential.  Literal
extension-field enumeration independently checks the collapse.  This removes
all odd singular local corrections, but the sum of the unit terms remains the
unknown global point count and supplies no REL saving.  Exact relative traces
also refute a positivity shortcut: `C_(5,11)=-608` in the already smooth odd
regime, and `C_(7,16)=-4608`.  A native regression pins both signs and the
positive underlying populations.  The remaining virtual comparison can be
negative even when every local term at each individual level is positive.
The selected positive-square continuation is now exact rather than heuristic.
Inside the single coarse identity cylinder, the connected trace is the
identity child's displacement from the cylinder mean; the sharp zero-sum
point inequality reduces `(REL)` to one conditional variance.  The cleaner
premise `V_id<=2^(2ell-2)` implies `(REL)` for both endpoint parities at every
`ell>=200`.  Its native report also reconstructs the exact localized Haar
identity `R V_id=sum_j 2^(j-c_0-1)sum_p H_j(p)^2`, level by level.  The clean
premise is false on some small rows but holds at both endpoints for every exact
row `14<=ell<=23`; this remains finite evidence, not a theorem.  The missing
statement is now a local Carleson-energy estimate on one ramified Witt subtree.
Exact pricing weakens that bridge substantially: it is enough that the identity
cylinder carry at most `1/(16ell^2)` of each retained level's global Haar
square energy.  The native `(PL2)=>(ICV)=>(REL)` report checks both endpoint
parities through `ell=1024`.  Equivalently, Cauchy reduces `(PL2)` to a global
normalized Haar kurtosis as large as `2^c_0/(256ell^4)`, so neither Gaussian
behavior nor an absolute fourth-moment constant is required.  The exact report
now retains the global fourth powers and tests this weak threshold without
division.  A second exact factorization now follows the nonnegative square
mass of each retained Haar layer down the nested identity Witt path.  It is
enough to find `ceil(log2(16ell^2))` half-balanced binary splits on each path;
at `ell=200` this is only 20 of 190 available coarse levels.  The alternative
three-quarter split price is 47.  The typed report reconstructs every parent
and child mass and checks both implications without floating point.  These are
implication checkers and finite diagnostics; the half-balanced path lemma and
`(PL2)` remain unproved polynomial-delocalization theorems.  Pinned fleet runs at
`19<=ell<=23` preserve the stronger `(LC2)` on all ten endpoint rows while
refuting perfect uniform sharing on 39 retained layers, so the diagnostic is
non-vacuous but remains non-credit-bearing.
One path split is now a theorem rather than a diagnostic: translation
`f(x)->f(x+1)` forces exact half balance at level `2^v_2(n)` whenever that
level lies in the coarse path.  Lucas parity and the triangular coefficient
action prove the statement; exact populations independently replay it.  This
reduces the first endpoint price from 20 unknown half splits to 19, but gives
no split when `n` is a power of two and therefore does not prove `(PL2)`.
The retained Haar levels no longer need separate localization.  Their exact
conditional-variance weights now form one aggregate nested identity path whose
terminal mass is the full conditional-variance numerator.  Pricing that path
against the sharp one-sided `(REL)` allowance lowers the first endpoint from
20 separate half splits to 18 aggregate splits for `n=401` and 19 for
`n=402`; translation leaves 17 and 18 respectively.  This is the selected
positive-square bridge, but the remaining aggregate contractions are still an
unproved uniform theorem rather than finite proof evidence.  Exact-source
fleet controls at `e046d1d05` cover both endpoints for `19<=ell<=23`: every
one of the 140 aggregate steps satisfies the weaker three-quarter contraction,
while 69 are half-balanced.  This directly tests the selected candidate but
remains non-credit-bearing finite evidence.
The companion characteristic-two Newton-over-Hodge result has also been
priced conditionally: it forces only divisibility of the connected endpoint
trace by eight.  At `ell=200` the existing envelope is already divisible by
eight, so it saves zero; divisibility-only rounding would need exponent 409,
leaving 406 bits missing.  It receives no `(REL)` proof credit.

**Next:** prove `(REL)`, encode it as replayable evidence, remove the
manuscript's fail-visible warning, and perform the final source audit.  The
active sufficient form is the polynomial identity-cylinder Haar share `(PL2)`
from ADR-0580.  ADR-0581's stronger but more local continuation needs only
`O(log ell)` half-balanced splits per retained layer; the stronger linear
local-Carleson pattern is diagnostic only.
Any proof must control the complete relative Witt
weight/zero-fibre distribution before characterwise absolute values; zero
`2`-rank, a scalar minimum distance, or an elementary-abelian cover theorem is
not sufficient.  At the odd endpoint, merely smoothing or counting the cycle
eigenlines and the complete `Frob*c` fixed locus is also finished and
insufficient: a geometric continuation must bound the global trace on the
smooth exact-orbit locus, rather than compute more local terms.  A Hankel
continuation must prove a signed prime-weighted
all-quasi-regular estimate and immediately discharge the endpoint ledger;
rank-only or divisor-only tables receive no proof credit.  The stronger
sufficient fourth-moment bound is
experimentally true for `6<=ell<=23` but remains an open fact; curve positivity
alone is non-strict.  The exact half-level Möbius sieve now has a native
positive-composite counterexample, so the elementary divisor-density route
requires genuine Type-II/bilinear cancellation.  Sparse and elementary
degree-raising shortcuts have also been closed negatively.  The new mixed
energies are genuine Type-II inputs, but they do not control the connected
cross-degree terms in the required Mangoldt fourth moment.  The exact
diagnostic through `ell=26` led to a uniform proved wild-Kloosterman amplitude
bound for the extremal pair `V_(ell-1)^2`, now exposed as a bounded native CAS
report and as an explicitly uncredited Autogenesis fact obligation.  The
stronger exact plateau support formula remains finite evidence only, but is no
longer a dependency.  The odd-degree Artin--Schreier doubling fallback is now
closed under all six binary projective changes of variable: the three
involution classes are impossible at half shape, explicitly reducible, or
reduce to the already known `x^(2n)+x^n+1` cyclotomic/Q candidate.  This is a
checked construction obstruction and gives no aggregate endpoint credit.  The
Kloosterman estimate is unweighted, while a Vaughan
decomposition is Möbius-weighted; substituting one for the other has now been
closed as invalid.  Exact signed classwise Möbius distributions are exposed as
a bounded native diagnostic with independent factorization controls.  Proving
a weighted binary bilinear estimate, a recurrence-wide Möbius bound, or the
aggregate endpoint estimate remains open.  Group-ring logarithmic
differentiation now reduces that choice to one exact short signed
Möbius-convolution sum; the CAS reconstructs it from a single recurrence table
and the ledger exposes its still-unproved uniform endpoint bound without
granting finite experiments theorem credit.  A direct small-degree
factorization oracle now checks each convolution term and detects inverse- and
weight-dropping mutations independently of the transform reconstruction.  The
exact additive-Fourier bridge is now native: a checked Walsh spectrum recovers
every inverse-interval fibre, while a direct factorization oracle validates
the reciprocal-polynomial and ramified-`x` identity frequency by frequency.
The source-level characteristic audit isolates the reusable Hölder/energy
core from the odd-characteristic complete-sum input.  Exact inverse-additive
energy is now a separate native diagnostic with a direct collision oracle;
the fleet-suggested no-wrap regime is now proved for `ell>=3d` by clearing
denominators.  A second native route classifies reduced rational collisions
and proves the explicit bound `E_inv<=2^(2d+o(d))`; a symbolic Hölder ledger
shows this closes the small/small Type-II region beyond total interval
exponent `r/2`, but not the full decomposition.  The no-wrap modulus condition
has been corrected to the strict inequality `3d<r`.  A new internal
valuation/lift/divisor proof now supplies the wrapped binary prime-power energy
bound
`E_inv(x^r,m)<=2^(2m+o(r))+2^((7m-r)/2+o(r))` for every `m<=r`, including
`3m=r`.  Its CAS report retains the full finite divisor envelope, and a
loss-aware bilinear ledger shows that the small boundary does not close merely
by erasing that envelope or epsilon reserve.  The source dependency table
and exact exponent ledger are now complete.  Dedicated CAS reports replay the
full integer ranges and binary replacements in Bagshaw Type-I Cases 1 and 2;
both retain a genuine saving wherever their ranges are nonempty.  They also
show that direct substitution of the proved binary wild-Kloosterman maximum
loses all uniform saving in Bagshaw's Type-I Case 5.  Exact variable mapping
also shows that Case 5 is empty here because every Lemire cutoff has
`N>ell+1>=r0`.  The actual endpoint gap is that even the published
zero-epsilon exponent pair would pointwise cover only the tail
`d>(14/15)ell+O(1)`.  An exhaustive Vaughan table now checks every endpoint
convolution order, effective modulus, and Type-I/Type-II split; Cases 4 and 5
are empty and all seven relevant rows occur.  At `ell=300` it confirms the
same first strict degrees `283` and `284`, with only a `15/16`-bit initial
margin before finite energy loss, epsilon/constants, and factor `d`.  The CAS
now computes the exact maximum binary polynomial divisor count at each finite
degree and carries the resulting proved energy ceiling through every
energy-using Vaughan row.  Direct factorization through degree ten checks the
optimizer.  This honest column has no strict pointwise order at `ell=300`;
even `d=299` is `106/16` bits above target.  Consequently the margin-aware
odd ledger's zero-reserve tail from `d=293` fits only in the ideal-energy
column, not the proved explicit one.  The exact cross-order Fourier regroup is
also native.  It shows that the relevant nesting is low-bit annihilator depth,
not multiplicative conductor alone, and verifies the regrouped identity at
both endpoints through `ell=8`.  Summation by parts reduces the next proof
step to a weighted `B` combination plus its boundary term on these annihilator
layers.  Proving that aggregate bound, together with a buffered explicit tail,
is now the precise blocker.  Carmon's original characteristic-two equations
have now been checked directly: on the squarefree locus the Möbius sign is the
additive Berlekamp-discriminant phase, while squareful inputs retain weight
zero.  A bounded native diagnostic measures the combined Berlekamp-plus-
inverse phase on low-coefficient shift fibres, counts stationary versus
oscillating pairs, and returns the exact van-der-Corput/Cauchy bound.  At the
pinned `(ell,k,s)=(4,9,4)` control every frequency improves on the trivial
bound, but this remains finite evidence.  The next theorem obligation is a
uniform shift-fibre energy bound on the annihilator frequencies and residual
degree block, immediately substituted into the aggregate budget.  Additive
orthogonality now converts the entire annihilator average into one exact
signed simultaneous input/inverse-coset energy.  Its shift decomposition has
the proved diagonal `(2^k-(-1)^k)/3`; the stronger `2^(k-1)` energy target is
refuted by exact energy `309=171+138`, so the obstruction is genuinely
off-diagonal.  Two explicitly uncredited targets survive both endpoints
through `ell=9`: global energy at most `2^k`, and the local square-root bound
`b_(C,D)^2<=2d #bucket`.  Exact ledgers show that they would start the
`ell=300` pointwise tail at `d=207/208` and `d=210`, respectively, but neither
controls the complementary signed convolution block.  Proving the local
two-sided fibre estimate or finding its first counterexample is the current
bounded task; finite controls remain non-evidence.  The inverse-coset support
is no longer opaque: cancelling the common valuation reduces every nonzero
shift to `z^2+hz=a` in a truncated binary local ring, whose kernel dimension
is exactly `v+1` for `2v<r` and `floor(r/2)` otherwise.  Every shift row now
carries the resulting proved support ceiling, exhaustively checked in all
quotient rings through modulus degree twelve.  This classifies the affine
fibres needed by a Berlekamp argument, but does not yet prove cancellation of
the Möbius signs on them.  A single-translation pairing route has now been
closed negatively: its exact defect inequality already fails at
`(ell,k,d)=(9,11,8)`, even though the stronger local signed target still holds
there.  Twenty selected fleet rows through `ell=12` continue to satisfy the
global and local energy targets, but remain uncredited finite evidence.  The
binary Möbius sign now has three independently checked exact realizations on
the squarefree locus: factor parity, Stickelberger--Swan discriminant modulo
eight, and the Arf invariant of the second trace form (with the degree-class
correction).  Exhaustive agreement through degree ten validates this algebraic
bridge and keeps squareful inputs at weight zero.  Since the per-polynomial
second-trace Gauss sum merely re-encodes the same sign, the next theorem must
control the joint quadratic system after imposing the affine inverse-coset
constraints; full rank of each isolated trace form is not itself endpoint
cancellation.  The existing odd-generator factors are now exposed and
roundtrip-checked as truncated binary 2-typical Witt blocks.  Every order-two
character is projected inside the simultaneous cosets with exact conductor
and quotient Parseval.  At the failed `(9,11,8)` translation row, its 32 real
modes have total energy `20832=32*651` spread across all conductors, so a fixed
tiny exceptional-real sector is not supported by that witness.  The Swan
coordinate also extends through squareful inputs exactly:
`mu(f)=(-1)^degree chi_8(Disc(F))`, where the dyadic character vanishes on an
even discriminant.  Fraction-free integer elimination now computes every
residue modulo eight, derivative gcd checks its parity independently, and an
exact cyclotomic identity rewrites the weight as four additive modulo-eight
phases.  This removes the squarefree gate from a joint Artin--Schreier--Witt
sum, but the unrestricted phase is provably not low degree: its full-support
multilinear coefficient is odd in every degree because the exact constant-one
squarefree population is odd.  Thus the next rank theorem must act after
restriction to the affine inverse fibres, or cancellation must be retained
across convolution orders.  Exact restriction does not yield a uniform
quadratic phase either.  At `(ell,k,d)=(9,11,8)`, all `18,884` exact
shift/inverse-difference sets are checked affine, but `2,297` nonquadratic
fibres contain `61,264` of `130,048` points and reach support degree seven.
Their signed correlation is `-202` versus `8,622` after fibrewise absolute
values, while the full off-diagonal total is `-68`.  The remaining dyadic
cancellation is therefore cross-fibre in this witness: the next bounded task
is to estimate the now-checked aggregate layers.  Combining first by exact
`(shift,inverse difference)`, then by the normalized Artin--Schreier product
parameter `h_0/w_0=f(f+h)`, and finally by common valuation reduces the pinned
absolute totals from `33,680` to `16,972`, `3,956`, and `388`, before the
signed total `-68`.  The tempting valuation bound `2^(d+1)` is already false
at the even `(9,12,8)` row (`672>512`), so the next theorem must use
cross-valuation/Witt orthogonality.  The stronger coefficient-one
valuationwise square-root scale also drifts above target, while the connected
candidate `abs(offdiag)^2<=2^(k+d+1)` survives the endpoint matrix through
`ell=9` and the selected tail through `ell=11`.  Its exact arithmetic checker
shows that a proof would imply `E<=2^k` at both endpoints; the factor two is
necessary already at `(6,9,5)`.  This remains an unproved local lemma and
still does not control the complementary signed cross-order block.  The next
bounded experiment now has one connected signed Witt spectrum: blockwise
Verschiebung is checked injective/additive, all valuation layers combine
before absolute values, and exact second/fourth moments plus general-character
conductors are replayable.  The pinned `214` parameters occupy `184` Witt
classes and retain signed total `-68`, but all `512` characters are nonzero,
closing sparse/imprimitive support as the mechanism.  The full modulo-eight
residue populations are now retained at every embedded class.  All four
primitive additive-phase transforms reconstruct the signed spectrum through a
mutation-checked Gauss identity, but each also has full support at both native
primes in the pinned witness.  A primary-source audit shows that a Heisenberg
rank still requires an explicit central-extension cocycle; neither the integer
spectrum nor these phase lifts define one.  The next bounded task is therefore
to retain the affine-fibre variables and test an explicit associative cocycle;
the cheaper exact complementary-family stopping test already fails, with
off-identity autocorrelation about `0.7735` of the identity and total square
mass about `26.89` times the complementary value.  Positive spectral powers
therefore erase essential indefinite Gauss cancellation.  If no natural
joined-domain cocycle survives, pivot to the connected fourth-cumulant/gcd
strata rather than computing more unrestricted spectra.  The exact primitive
autocorrelation test now supplies that stopping result: zero of `18,884`
original affine fibres are generalized bent in the pinned row, despite
`16,587` having at-most-quadratic ANF.  The simple fibrewise Gauss/Heisenberg
route is therefore closed, and connected fourth-cumulant/gcd stratification is
the active bounded task.  The class discrepancy is now decomposed exactly into
all convolution-order vectors, with the three Wick pairings subtracted in
every symmetric fourth-order tensor cell.  Multiplicity-weighted cells
reconstruct the direct cumulant.  At `(ell,n)=(9,19)`, individual connected
cells are over thirty times larger than their signed total, confirming that
gcd strata must be recombined across orders before absolute values.
The primary-source audit then closed a direct magic-square implementation:
those gcd matrices parametrize a two-sided product equation from one character
and its conjugate, whereas the connected remainder has four characters subject
only to one product constraint after its pairing diagonals are removed.  The
whole-cumulant route is now the exact conductor martingale.  A new local
Witt-cylinder ledger measures its exact fourth-over-second concentration.  The
provisional ceiling eight is refuted by the even `ell=12` and `ell=15` rows;
the replacement linear ceiling `R_j(b)<=ell` survives both endpoint parities
through `ell=19`.  A stronger max-to-average reduction is already refuted at
the pinned `ell=8` root, so the proof must retain descendant distribution.  A
checked implication turns the conjectural local bound into
`M_4<=16 ell^5 2^(3ell)` and closes the
symbolic endpoint ledger after the finite degree-400 handoff, but the uniform
local bound itself remains unproved and receives no theorem credit.
The exact local statement is now an explicit conjectured fact-ledger
obligation, with no proof route or evidence, so Autogenesis can dispatch the
actual frontier without mistaking the bounded report for a certificate.
The primary aggregate target is now the equivalent connected inequality
`K_4<=M_2^2`, or root ratio `R_0<=4`.  Unlike a cellwise estimate, it retains
all signed convolution-order cancellation.  Both endpoints satisfy it through
`ell=21` and the completed odd `ell=22` row does as well; these are uncredited
finite diagnostics.  The exact implication yields
`M_4<=64 ell^4 2^(3ell)` and closes the same degree-400 handoff.  A conjectured
fact exposes this aggregate obligation to Autogenesis without a proof route.
The first conductor proof decomposition is now exact and mutation-checked.
The naive geometric bound on every layer fails at conductor one for even
`ell=20`; buffering all levels below `ceil(ell/2)` and applying the geometric
bound above it survives both `ell=20` endpoints, and the two allowances sum
exactly to the required `3 M_2^2`.  It fails at `ell=8` and both `ell=13`
endpoints, but holds at `ell=12` and both endpoints for every `14<=ell<=20`, so
its ledger statement starts only at `ell=200`.  Every conductor energy now
also reconstructs as `2^(j-1)` times an exact sum of squared binary-cylinder
mass differences, isolating refinement imbalance as the analytic input.  This buffered split is a separate
conjectured fact and remains the live uniform lemma.
The elementary-abelian generalization of Fomenko's fixed-coordinate map is now
closed structurally: every map to a binary vector space factors through the
maximal quotient `E_ell/2E_ell`, whose checked rank is `ceil(ell/2)` and whose
minimum kernel has dimension `floor(ell/2)`.  The first-slot map attains that
minimum, and exhaustive controls verify every fibre and homomorphism pair
through `ell=8`.  Thus no alternative selection of additive binary
coordinates can supply Fomenko's small-kernel gain; a surviving variant must
retain non-elementary higher-Witt structure and prove cross-block
orthogonality.  The aggregate connected-cumulant/Witt-imbalance lemma remains
the proof frontier.  Garefalakis's dedicated consecutive-zero theorem
was also checked directly and fails Lemire's `m=n`, `l=floor(n/2)` endpoint in
its stated sufficient condition.
An exact first-moment alternative now reconstructs every Mangoldt class
population from the signed sibling differences in the binary Witt quotient
tree.  The weighted `L1` Haar triangle is sufficient for the `2^ell`
discrepancy bound and passes both endpoints for every fleet-tested
`16<=ell<=20`; the level-4 odd failure is pinned so this is not tautological.
The buffered square-root-fibre target
`H_j^*<=3j 2^ceil((n-j)/2)` implies the odd endpoint from `ell=13` and the even
endpoint from `ell=15`.  Its sharper coefficient-two predecessor is explicitly
refuted at `(ell,n,j)=(19,40,4)`.  The coefficient-three statement is a new
conjectured Autogenesis fact, not theorem credit; proving it by relative
Artin--Schreier--Witt or long-cycle geometry would finish the endpoint without
the fourth moment.  Exact Fourier inversion and the standard individual Weil
bound now discharge every level below `ell-ceil(log2 ell)`.  A proved hybrid
Haar calculation reduces the conjectured square-root-fibre estimate to only
the logarithmic top-conductor window; at the degree-400 handoff this is the
nine levels `192<=j<=200`.  Gorodetsky--Kovaleva's high-conductor theorem and
appendix bound do not supply the remaining family gain: the former restricts
primes only for one special power-sum character, and the latter is an
individual-character estimate that loses `2^(j/2)` after exact-conductor
Fourier inversion.  The selected target is now weaker still and respects the
earlier cross-layer warning.  Along the identity path, the top
`ceil(log2 ell)+2` weighted increments telescope to one signed relative trace
`2^ell N_ell(1)-2^(a-1)N_(a-1)(1)`.  Bounding its absolute value by
`2^(2ell-2)`, while using individual Weil below `a`, closes both endpoints
with reserve for every `ell>=200`.  This asks for only a polynomial saving
over the relative Weil trace and preserves cross-conductor cancellation.
Exact fine/coarse reconstruction, the symbolic implication, and both fleet
endpoints through `ell=20` pass; the statement remains a conjectured fact, not
theorem credit.
The connected trace is now also represented exactly as the point-count
difference between the Carlitz curves of conductors `t^(ell+1)` and `t^a`.
A native geometry ledger checks the chain of quadratic Artin--Schreier steps,
the relative Galois degree, and the relative genus.  The genus reproduces the
entire separate-Weil envelope: at `ell=200` a proof must save exactly
`50641/32`, with integral ceiling `1583`, asymptotically about `8ell`.  The
available Ito--Takeuchi--Tsushima Heisenberg theorem concerns a single
quadratic `y^2-y=xR(x)` curve and a length-two Witt torsor, so it is not
credited for this growing relative chain without a new checked reduction.
The strongest such reduction is now refuted by an exact-conductor rather than
whole-curve witness.  Supersingularity would force the degree-`2m` trace to be
divisible by `2^m`, but the native level-ten degree-22 trace is `-5120`, with
remainder `1024` modulo `2048`.  Thus the new layer itself cannot consist only
of supersingular quadratic Heisenberg pieces; a useful argument must isolate a
smaller cancelling subquotient or handle non-supersingular relative
cohomology.
A direct family-second-moment shortcut is also now quantified and rejected as
the selected route.  At `ell=12`, exact Cauchy across the 4032 top characters
exceeds the connected allowance squared by factors about `303.92` and
`632.42` at the two endpoints, even though the signed traces themselves pass.
The native ledger reports the exact moments, thresholds, and integral savings
`304/633`; any next lemma must retain phase alignment rather than take an
absolute square across the full character family.
The dyadic auxiliary-unit projector proposed by the bridge audit is now a
proved native CAS fact.  Over `(Z/8Z)^x=<3,5>`, all eight discriminant
residues satisfy the exact four-phase projector, polarization
`(-1)^(D u u')`, and the claimed radical classification.  This preserves the
Möbius zero/sign cancellation in one quadratic Gauss object.  It still does
not supply the larger joined fibre/valuation/Witt group law: the next
fail-fast condition is additivity of the discriminant difference modulo four.
That fail-fast condition now rejects every projection-preserving central
extension of the pinned worst fibre, not merely the direct product.  The
native exact table independently reproduces its full-support coefficient `6
mod 8` and finds `d(1)=1`, so `d(1 xor 1)=0` differs from `d(1)+d(1)=2 mod 4`.
Any surjective homomorphic projection would force quotient additivity; hence a
viable joined law must genuinely mix fibre multiplication with auxiliary,
valuation, or Witt coordinates before its commutator rank is meaningful.  This
is a construction-class obstruction and grants no endpoint cancellation
credit.
The bridge audit's independent second-trace/Kerdock route has now received its
stopping test.  The native CAS retains every second-trace quadratic form inside
the simultaneous coefficient/inverse buckets, computes pairwise polar ranks
and radicals, and independently checks the corresponding exact Gauss sums.  At
`(ell,k,d)=(9,11,8)`, 28,830 pairs occupy ten types and realize every even rank
from zero through ten; five nonzero correlations have rank only two and
radical dimension nine.  Degrees eight and nine already contain distinct
phase-trivial rank-zero pairs.  Thus the raw forms are not a uniformly
high-rank Kerdock family.  Any Arf-based rescue must aggregate the same
low-rank sectors across fibres or orders, so the selected proof architecture
returns to the connected cross-order Witt-Haar/fourth-cumulant estimate.
An equation-level audit of Ito--Takeuchi--Tsushima also closes direct import
of their characteristic-two Heisenberg group: it assumes a linearized `R` and
quadratic phase `xR(x)` before constructing its cocycle, whereas the retained
Lemire fibres have degree-seven phases, no generalized-bent fibres, rank-zero
second-trace differences, and the separate mod-four projection obstruction.
Future use requires a checked reduction of the complete connected sum to
their quadratic form or a genuinely new mixed-domain associative cocycle;
nondegeneracy cannot be imported as an assumption.
An equation-level audit of Sawin's short-interval geometry likewise rejects a
naive half-parameter recursion.  His characteristic-two logarithmic derivative
only bounds the image of the bad locus at infinity, while the generic smoothing
used for the vanishing-cycle theorem is not `S_n`-equivariant.  The resulting
ordinary cohomological support bound therefore cannot be projected onto the
long-cycle virtual character.  A Sawin route now requires an equivariant
smoothing, a direct Frobenius--long-cycle trace theorem, or a recursive complex
with checked stalk multiplicities; the fixed-point identity alone is the
original Mangoldt population and is circular as an estimate.
The distinct fixed-degree extension-field diagnostic is now native rather
than conflated with the base-field Hayes count.  Certified binary field
moduli, exact `GF(2^r)[T]` Rabin tests, inseparable/odd prime-power recognition,
and pre-enumeration population limits produce exact long-cycle errors.  Small
controls recover `A_r(5,2)=(-4)^r-(-2)^r` through `r=3` and
`(A_1,A_2,A_3)(9,4)=(5,129,-1771)`;
the ignored release probe independently enumerated the 33,554,432-candidate
four-coefficient `GF(32)` row in 206.15 seconds and recovered
`A_5(9,4)=-28675`.  This refutes the two-mode recurrence but remains finite
diagnostic evidence, not an ordinary-gate or uniform theorem.
The binary Hayes `L`-degree pattern from Gao's examples is now proved for
every level from the exact conductor filtration and exposed as a bounded
native report.  Exact level `j` contributes `2^(j-1)` characters of degree
`j-1`, hence `D=(ell-2)2^ell+2`; direct mixed-radix enumeration checks the
classification through level six.  This closes the source's conjectural
degree-distribution pattern but also proves that the refined characterwise
Weil ledger retains the fatal linear factor.  It does not move the connected
top-trace obligation or grant Lemire theorem credit.
The fixed-degree long-cycle diagnostic now has deterministic JSON sharding,
exact coefficientwise-Frobenius orbit compression, a fail-closed hierarchical
collapse, and native exact Hankel minors.  A 640-child fleet run computes
`A_7(9,4)=-2,479,675` over the complete `128^5` interval.  Together with the
six lower traces, its nonzero `4 x 4` Hankel determinant rigorously excludes
every recurrence of order at most three for this finite row.  This closes the
tiny-zeta shortcut negatively; it does not bound recurrence order uniformly
or move the endpoint proof frontier.  Characteristic-zero smooth-projective
and real semi-algebraic symmetric-cohomology bounds are explicitly rejected
as substitutes for the missing characteristic-two compact-support hook
theorem.
The published function-field Linnik--Selberg average has now also been audited
at equation level. It cancels Kloosterman sums over varying monic moduli of a
fixed degree, while the endpoint inverse phases all live modulo the single
wild modulus `x^(ell+1)` and vary their arguments with a Möbius weight. The
same source says that the twisted/divisibility extension is open and lacks
explicit parameter dependence. ADR-0532 therefore grants it no endpoint
credit; a useful spectral argument would have to prove a new fixed-wild-
modulus Voronoi/Kuznetsov statement that preserves the cross-order weight.
The characteristic-two `Q`-transform bridge is now audited from its exact
equations.  A bounded native Lucas-submask expansion independently certifies
the special shaped success `x^3+x+1 -> x^6+x^3+1`, but its next iterate loses
the half-degree window.  More generally, the standard indefinitely iterated
irreducibility hypothesis forces the transformed coefficient of degree
`2n-1` to be one, so it cannot produce a shaped degree-`2n` polynomial.
The cyclotomic trinomials `Phi_(3^r)` give the honest infinite degree family
`2*3^(r-1)`, not arbitrary-degree coverage.  This closes the cheap recursive
construction bridge without moving the connected endpoint proof obligation.
A separate checked Capell route now turns any even-degree shaped seed with a
noncube root into the full tower `d*3^k`.  The standalone audit replays all 400
committed source artifacts and both output-certificate checkers: 138 selected
seeds qualify, occupying 95 distinct 3-free rays; 200 odd degrees are
structurally ineligible and 62 selected even roots are cubes.  The iteration
is exact, since both the root order and `2^(3d)-1` gain one 3-adic factor at
each step.  This establishes infinitely many additional degrees but leaves
every odd degree and infinitely many even 3-free bases, so the uniform
connected trace obligation is unchanged.
The multi-minute endpoint sweep is now an explicit ignored,
environment-selected research probe; the ordinary theorem gate keeps the
bounded `ell<=7` controls.  Three exact-commit fleet probes extend both the
root connected target and the stronger local linear cylinder ceiling through
both endpoints at `ell=23`; every new row still rejects the max-to-average
shortcut.  The canonical note retains their exact ratios, resource use, and
log hashes.  These results remain uncredited finite evidence and do not move
the universal proof frontier.
The primitive/imprimitive Gauss-sum template now has a decisive exact stopping
test.  A native integral `Z[zeta_(2^r)]` evaluator constructs every primitive
Hayes `L`-coefficient and logarithmic power sum, with both NTT primes as
independent controls.  At conductor level five and endpoint degree eleven,
all six functional-equation root-number fibres contain different power sums;
the pinned pair has common leading coefficient `-4` but sums
`-32+32 zeta_8^2` and `-32-32 zeta_8^2`.  Thus root-number data and
cyclotomic zeta factorization alone cannot control the connected endpoint
trace.  A surviving characteristic-two argument must retain the full
coefficient vectors and their signed cross-character cancellation; this exact
obstruction grants no Lemire theorem credit.  The same audit now checks the
coefficientwise primitive functional equation exactly and prices its direct
enumeration as `4^level` work cells, declining before allocation when the
caller's explicit ceiling is exceeded.
The full character data now also has an exact Galois/Ramanujan decomposition.
Odd powering partitions every primitive conductor family into rational
cyclotomic orbits; two NTT primes reconstruct each integral orbit trace, and
exact-order regrouping independently recovers the conductor layer.  The
one-Weil-unit orbit target is refuted at `(j,n)=(7,15)`, where 18 of 28 orbits
violate it and the maximum is `1696>256`.  Delaying absolute values until
exact character order helps but does not give a fixed small constant: the
`(11,24)` order layer `663552` needs coefficient 17 relative to
`(j-1)2^ceil(n/2)`.  Both endpoint parities are pinned through level 12.
Thus a viable order-layer theorem must expose and ledger its conductor growth,
or cancellation must remain across character orders inside the selected
connected Carlitz trace; no theorem credit moves.
The special high-trace symmetry has now been bounded at the character-family
level as well.  Over `GF(2)` every monomial power-sum character is quadratic,
and its multiplicative span cannot leave the order-two subgroup.  Exact
mixed-radix enumeration proves that an odd primitive level `j` contains only
`2^((j-1)/2)` quadratic characters among `2^(j-1)` total, while every even
primitive level contains none.  Thus the maximum eligible coverage is
`32/1024` at level 11 and `0/2048` at level 12.  Gorodetsky--Kovaleva's
monomial image/kernel identity cannot reach the full higher-Witt family or
the connected fourth cumulant; the whole-family target remains unchanged.
The complete fibre-product formulation is now exact and fail closed.  Raw
`r`-fold characteristic-polynomial fibres give the positive counts
`C_r=sum_e N_e^r` for `r=2,3,4`; centering and subtracting all three Wick
pairings reconstructs the existing `M_2`, `M_4`, and `K_4` independently.
The pinned `(9,19)` connected value is `-2086965956608`, proving that the live
cumulant is a signed virtual Frobenius trace rather than an honest
off-diagonal point count.  A geometric proof must control the centering
complex and pairing projectors, or the equivalent conductor-Haar differences;
irreducibility of only the raw fourfold fibre product is insufficient.
Katz's universal big-Witt sheaf has the expected large `SL` monodromy, but an
exact native comparison now proves that its ordinary pointwise fourth moment
is a different tensor contraction.  The CAS reconstructs
`sum_chi |S_chi|^4` from spatial autocorrelations, separately reconstructs the
full product-constrained sum `2^(3ell)M_4`, and retains the connected numerator
`2^(2ell)K_4`; the two fourth moments already differ at the level-seven odd
endpoint.  Katz's effective equidistribution also fixes conductor while the
field grows and leaves a compactly-supported Betti constant uncontrolled in
the growing-conductor regime.  A viable monodromy bridge therefore needs a
convolutional four-design theorem and uniform Betti bounds over fixed
`GF(2)`, not the standard pointwise large-field limit.
Fomenko's coefficient-zero restriction now has a sound growing-conductor
generalization as well: restriction fibres are closed under cyclotomic Galois
before two-prime CRT reconstruction, and their signed packets independently
recover each primitive conductor trace.  The one-square-root-unit packet
bound is false.  At `(ell,t,n)=(12,5,26)`, 29 of 32 logarithmic packets
violate it and the worst needs coefficient 65; packetwise absolute values are
`6433280` against signed total `933888`.  The exact quotient is reusable, but
Fomenko's decisive fixed-level degree-two `L`-polynomial formula has not
generalized, so the endpoint still requires cross-packet/cross-conductor
cancellation.
The product-constrained fourth moment is now represented exactly as the
identity value of a fourfold character convolution, with all three Wick
pairings retained and independently checked against the spatial fourth
cumulant.  Adams operations turn this into a precise geometric budget rather
than a generic monodromy slogan: after removing the `2^(2n)` Adams weight, a
mixed connected complex with `H_c^i=0` above degree `4ell` and total normalized
Betti number at most `ell^4` would prove the accepted endpoint envelope.  At
`ell=200` this means cancelling the possible cohomology degrees from `1200`
down through `801`.  Literal support on the Wick diagonals is explicitly not
claimed; proving or refuting this uniform cohomological cutoff is the active
geometric stopping test.
The first genuine extension-field connected trace now separates that cutoff
from its proposed Betti coefficient.  A bounded native operation retains all
`q^ell` class populations over `GF(2^r)`, reconstructs the Wick-subtracted
trace, and agrees exactly with the independent base-field Hayes transform.
At `(ell,n,r)=(2,5,5)` its exhaustive `32^5` row needs normalized coefficient
26, refuting the universal `ell^4=16` Betti budget.  The exact
trace/subtrace formula then closes the weight question at this level:
`T_r=q^12(q-1)(q^2-6q+6)` has normalized degree five, one above the proposed
degree-four cutoff.  Thus the cutoff itself is also false as a universal
all-level lemma, not merely under-budgeted.  This does not refute a new theorem
proved only for `ell>=200`.  The active geometric task is now to identify the
surviving top-weight stratum for general `ell` and determine whether another
endpoint-relevant cancellation removes it before any Betti estimate is used.
The connected extension-field operation now has deterministic JSON shards and
an exact class-vector merge.  Missing, duplicate, noncontiguous,
parameter-mutated, truncated, and total-mutated inputs fail closed; the merged
Mangoldt population must equal `q^n` before moments are formed.  The CLI
roundtrip reproduces the direct level-two trace exactly.  This enables larger
fleet stopping rows but does not promote any finite row to theorem evidence.
The standard Q-transform constructive fallback is now closed completely, not
only for its published iteration hypotheses.  Self-reciprocity forces every
half-shaped irreducible Q-output to be `x^(2n)+x^n+1`, whose unique source is
`D_n+1`.  Even `n` makes that source a square; odd `n>=5` leaves a forbidden
`x^(n-2)` term.  Independent Rabin certificates confirm that
`x^3+x+1 -> x^6+x^3+1` is the sole exceptional shaped irreducible pair.  A
constructive completion therefore needs a genuinely different degree-changing
transform rather than another choice of standard Q-source.
The connected top-conductor projector is now decomposed exactly by Möbius
convolution order before absolute values.  At `ell=8`, order one survives at
both endpoint parities; all seven orders survive in the odd row and six in the
even row.  Thus the projector creates no high-order support cutoff.  Any
endpoint proof must retain the signed cancellation across convolution orders
as well as conductors; the bounded report reconstructs the selected trace but
grants no asymptotic theorem credit.
The first fleet-sharded level-three extension-field stopping row is now
complete.  Its exact `GF(16)` merge covers all `16^7` monic polynomials and
has minimum normalized coefficient `250`, refuting the apparent `ell^4=81`
connected Adams trace allowance that survived through `GF(8)`.  The weaker
one-extra-field-factor allowance survives this row but remains unproved; the
result neither tests the separate binary Witt off-diagonal inequality nor
controls the signed cross-order endpoint sum.
The level-three field sequence is no longer empirical: Gorodetsky's exact
period-24 symmetry reduces degree seven to a two-valued degree-one class
distribution, and the native closed form proves
`T_r=q^16(q^2-1)(q^4-6q^2+6)`.  Its normalized `q`-degree is eight, refuting
both the degree-six cutoff and the one-extra-`q` repair (explicitly by
`q=128`).  The theorem's own nonperiodicity boundary at four prescribed
coefficients prevents treating this fixed-level compression as the growing
endpoint result.
Quotient-compatible unit inversion now embeds the coarse additive Walsh
spectrum into the fine one and cancels all `2^(a-1)` inflated coarse
frequencies before any absolute value.  The resulting exact high-frequency
formula retains every Möbius order and then groups by annihilator depth.  Its
support still has size `2^ell-2^(a-1)`, and the orderwise and depthwise
triangle losses are cross-cutting, so this sharpens the selected analytic
object without proving its uniform cancellation bound.
The final high-frequency vector now carries an exact structural-support `L2`
ledger.  Direct Cauchy still misses the connected allowance on the pinned
`ell=8` endpoints: the exact square sums require further integral savings
`1425/1483`, despite the signed traces already satisfying the target.  This
closes another phase-erasing shortcut; a surviving proof must keep the final
frequency signs or prove an explicit large-`ell` norm collapse with that loss
absorbed.
The independent Sawin route now has an exact cyclic/Foulkes compression rather
than a heuristic representation slogan.  Ramanujan orthogonality reconstructs
the von Mangoldt long-cycle character as
`p_n=sum_(k|n) mu(k) Ind_(C_n)^(S_n) theta_(n/k)`, with exact coefficient mass
`2^omega(n)`.  A bounded native ledger recomputes every Ramanujan coefficient
from two formulas, checks all power-sum and grouped coefficients, and inserts
the exact characteristic-two endpoint weight.  It proves that a hypothetical
uniform effective cyclic Betti bound `B(n,r)<=n^4` would close every degree
after the certified 400 handoff; twelve base rows, odd/even proper-power
reserves, and a strict twelve-degree induction step are replayable.  Sawin's
published generic bound still fails, and the new quartic cyclic-eigenspace
statement is recorded as conjectured with no evidence.  The representation
compression has been proved; the characteristic-two cohomology estimate has
not.
The newly proposed even--odd recursion has also been reduced to its exact
content and stopped before finite search was mistaken for induction.  Every
half-shaped binary polynomial is reconstructed as
`E(x)^2+xH(x)^2`, and the native report proves
`gcd(f,f')=gcd(E,H)^2`.  The leading parity component remains half-shaped, but
irreducibility of `f` forces only component coprimality: the certified shaped
irreducibles `x^5+x^2+1` and `x^6+x^3+1` already have reducible leading parity
components.  Conversely, the simplest odd lift with complement one always
has the root one when the smaller component is irreducible.  Any useful
recursive construction therefore needs a genuinely new uniform complement
theorem; the active universal frontier remains the connected signed trace.
The long-cycle geometry now has one further exact theorem.  Writing
`n=2^a b` with `b` odd, Deligne--Lusztig finite-order reduction and a
triangular coefficient calculation collapse the odd-part fixed locus to one
point whenever `b>1`.  Hence the non-top long-cycle complex has alternating
Euler trace zero at every non-power-of-two degree.  The homogeneous-cone
decomposition removes the remaining unweighted power-of-two exception: the
punctured `G_m`-torsor has Euler trace zero and the vertex contributes one.
With Frobenius inserted, however, the fibre factor becomes `2^r-1`, which is
already one over the binary base field.  The remaining geometric bridge is
therefore a bound for the projective Frobenius--long-cycle trace, not another
unweighted fixed-locus count.
That projective action is now classified far enough to reject a second false
shortcut.  A projective fixed point is a cycle eigenline, not necessarily an
affine fixed vector.  If `n=2^a b` with `b` odd, exactly the primitive
`b`th-root eigenlines survive the endpoint equations, so the reduced
projective fixed locus has `phi(b)` points and is never empty.  The native
report checks every divisor order and retains wild scheme reducedness and the
Frobenius-weighted estimate as unproved.  Hence no free cyclic-torsor quotient
is available; the positive weighted trace theorem remains the frontier.
The Hast--Matei bridge is now translated at the exact endpoint rather than
invoked schematically.  Their explicit two-polynomial top-weight
representation leaves exactly `ell-1` hook characters on two long cycles, so
its idealized global second moment is `(ell-1)2^n`; Cauchy misses the odd and
even endpoints by squared ratios `(ell-1)/2` and `(ell-1)/4`.  The same native
report classifies every repeated-root stratum compatible with one long-cycle
Frobenius condition.  Odd uniform multiplicity gives triangular recovery of
the base polynomial from its leading coefficients, while even multiplicity
is a genuine Frobenius-square proper power with coefficient stride
`2^v2(n/e)`.  Thus the characteristic-two defect in the selected sector is
confined to square proper-power strata.  Proving that the connected virtual
projector cancels or separately controls those square strata, with an
effective bound on the remaining triangular sector, is now the precise
Hast--Matei route; no weighted-trace credit has yet been granted.
An independent algebraic reduction now writes the full Lemire coefficient
indicator as the DFT of
`Gamma=*_(j=1)^ell(delta_0+delta_j)` on `Z/(2^n-1)`.  The
Tuxanidy--Wang support theorem would prove Lemire whenever the least period of
`Gamma` does not divide the proper-subfield exponent.  Exact native
convolution has maximum period through degree twelve, and a direct
extension-field oracle agrees through degree eight.  The universal period
lemma remains conjectural: maximum period of each separate factor cannot be
multiplied blindly, as the degree-eight product including the middle
coefficient has period `15` rather than `255`.  Proving the weaker
no-proper-subfield-period statement would still suffice, but it is exact only
at prime-power degrees.  The selected minimal target now applies
`product_(p|n)(1+tau_(2^(n/p)-1))` to `Gamma`; Fourier inversion proves this
iterated difference is nonzero exactly when the coefficient-zero support
contains an element outside every maximal proper subfield.  The native report
computes that exact difference with charged work, distinguishes nested from
mixed subfield lattices, and agrees with a direct extension-field oracle.
Nonvanishing through degree twelve is only a control: the universal
nonvanishing theorem, like the connected trace, remains open.
The odd-endpoint stopping path now uses the exact identity
`N_(2ell+1)(1)=1+(2ell+1)I_(2ell+1)(1)` twice: its candidate-count bound makes
one admitted `75161927681` NTT residue the unique integer population, while a
conductor-width circular recurrence halves the retained power-sum history.
The new route agrees with the independent two-prime/full-inversion path through
`ell=12`; its modulus and primitive root are executable checks.  On `s6` it
certified `I_51(1)=1315030=6 mod 8` in 961.748 seconds at 13,371,736 KiB peak
RSS.  Thus the observed odd-count 2-adic nonvanishing survives this new row but
remains an unproved congruence and supplies no universal endpoint credit.  The
characteristic-delta period lemma and the connected trace remain the two
honest universal frontiers.
The congruence route is now stated at its actual geometric precision.  The
binary Carlitz cover has 2-rank zero by Deuring--Shafarevich, but recovering
`I_(2ell+1)(1) mod 8` requires its raw point count modulo `2^(ell+3)`, so
2-rank alone loses the normalized higher-slope information.  A charged native
report records the exact odd residue, valuation, curve normalization, and
precision ledger.  Exact cyclotomic arithmetic also computes every primitive
character Newton polygon through repeated `(1-zeta)` division, independently
checked against field norms and exact conductor traces.  Levels four and
eight already contain slopes `1/4` and `1/8` with large multiplicity; hence a
near-half characterwise cutoff is false.  The declared stopping row has now
terminated this route: the exact `ell=27`, degree-55 computation gives
`I_55(1)=4883944=0 mod 8`, with valuation three.  This refutes universal
fixed-modulo-eight nonvanishing while strongly certifying existence in that
row.  The Newton machinery remains a diagnostic for a possible
degree-dependent law, but theorem effort returns to a genuine aggregate trace
estimate; no endpoint credit came from the refuted congruence.
The nearest local-to-global Newton references do not change that verdict:
their primary statements assume an odd prime or a `Z_p`-tower, while the
binary Hayes group is a finite product of cyclic 2-groups.
Wan--Zhang's newer general complete-intersection Betti theorem does apply to
Sawin's ordered-root variety and is now inserted exactly into the Foulkes
ledger.  It improves the old generic bound but still misses the first two
post-400 endpoint margins by 6,829 and 6,851 bits, confirming that the needed
saving is cyclic-eigenspace or signed long-cycle cancellation rather than a
better total-Betti constant.
The dyadic fibre report now retains its exact `L^2` mass and proves that
inverse-difference equality is equivalent to the base-point-independent
nilpotent condition `h*t*(t+h)=0` modulo `x^(ell+1)`.  This turns the proposed
nonpositive fibre defect into one restricted four-shift Mobius correlation.
The candidate survives exhaustive endpoint rows through `ell=7` and the
maximal-interval fleet rows through `ell=14`, but remains conjectural and
would not by itself close the cross-order convolution.  The next audit must
also use the review sweep's favorable corrections.  The genuinely sufficient
weak fourth-moment allowance is now encoded with the necessary proper-power
margin; the positivity-only version is rejected.  Exact Efron--Stein masses
and a primary-source KLLM audit close the proposed constant-three shortcut:
the cited theorem controls a strongly noised, coordinate-count-graded
function, while even the hypothetical `C=2` log-order proxy misses the weak
allowance by four to six orders of magnitude on fleet rows through `ell=17`.
The cubic Capell operation is now generalized to every odd monomial power.
At a 20,000,000-prime cutoff, native and independent bit-polynomial audits
agree on 371 eligible committed seeds, including 174 odd degrees, and every
eligible seed generates a proved infinite ray.  This corrects the old claim
that monomial constructions omit all odd degrees, but the union is still not
an all-degree proof.  The power-of-two non-monomial composition window is now
classified exactly: for `sigma=x^k+t` and a shaped source of degree `n`, the
largest proper degree of `sigma^n` is
`kn-(k-deg(t))*2^v2(n)`.  Hence a nonmonomial substitution can preserve shape
only when the source degree is a power of two and the substitution is itself
shaped.  Exhausting every shaped irreducible degree-eight source and every
nonmonomial shaped degree-eight substitution finds four certified degree-64
images but no degree-512 continuation.  This refutes the proposed
`8 -> 64 -> 512` chain: the separately observed finite hits do not form an
inductive family.  The analytic obligation remains the proper-power-aware
weak fourth moment.  Its closest published analogue is now translated exactly:
Hast--Matei's `m=4` theorem has the required `2^ell H^3` scale, but fixes
`n,h`, permits its constant to depend on them, takes `q` to infinity, and
excludes `p=2`.  The actual target is therefore a degree-uniform wild
characteristic-two estimate with exact allowed constant
`(H-P_n)^4/(2^ell H^3)`, tending to two and four at the two endpoints.  The
CAS exposes this rational constant and does not credit the published
fixed-degree theorem.  The even proper-power envelope is also sharpened:
odd exponent layers are empty, moving the exact strong-target crossover from
`ell=17` to `ell=13`.  Replacing the tame singular-locus argument and proving
degree-uniform equivariant cancellation are both still open.
Full definitions,
proofs, controls, and literature record:
`docs/research/10-cas/lemire-half-degree-irreducibles.md`.

**Claim-dashboard gate, finding-8 re-measurement, and PLAN.md returned under its
ceiling** (`WIP`, ledger-integrity, 2026-08-16). Three defects behind a dashboard
reporting 38 claims against an actual 104; finding 8 re-measured as remediated
(177/177 checker runs can fail) after a regex audit of my own produced 19 false
positives; and `plan-authority` taken from 233,888 bytes to 46,820 by archiving
finished lanes to [`docs/plan/archive/`](docs/plan/archive/README.md). Full record:
[`diary-ledger-integrity.md`](docs/refactor-2026-08/diary-ledger-integrity.md).

**`int_prelude` is axiom-free.** `Int.euclidean_decomposition` is a theorem;
`Int: 54 derived (54 with an EMPTY axiom footprint), 0 still asserted`, trusted
surface `34 → 6 → 1 → 0`. Measured downstream under real Lean: the Diophantine
reconstructions now depend on **no library axiom at all**, and `check_one_lean`
gates that. Fourteen `kernel-lean` fact checkers were rebound from a whole-suite
run to their own theorem.

**Next.** ℚ, scoped in
[`02-the-library.md`](docs/mathematics-2026-08/02-the-library.md): build it as a
normalised structure (as Lean core itself does), not a setoid quotient. First
slice is `Int.natAbs`, then `Int.div`/`Int.mod` specified against the
freshly-proved decomposition.

**Certification is now gated on being re-derivable, not on being claimed**
(`WIP`, evidence-certification, 2026-08-17). Full record:
[`diary-evidence-certification.md`](docs/refactor-2026-08/diary-evidence-certification.md).

Three measurements drove the day, each a claim that was true in a way that read
as stronger than it was:

- **Ledger.** Settled SMT-route facts test the *verdict* (`… | tail -1` =
  `unsat`) and are blind to certification. 17 of 17 happened to be
  `certified=1`; nothing enforced it. Now gated, with the barber instance as a
  real negative control — genuinely unsat, genuinely uncertified.
- **Lean gate.** Of 74 crosscheck families, **41 hand Lean a structural
  attestation** — an axiom pair it cannot fail on the merits. The gate reported
  one undifferentiated total; it now prints both halves and floors the
  *reasoning* one, because flooring the sum lets reasoning be swapped for
  attestation with the headline unmoved. `qf_bv` was one of the 41: not a defect
  but a **width**, since enumeration beats bit-blasting below ~16 bits.
  `qf_bv_wide` now exercises the real reconstruction (33 theory / 41 attestation).
- **My own claim.** I wired the e-matching route to `Evidence` and shipped
  `certified=1` on evidence whose independent re-check said FAIL. Reverted, then
  fixed properly: the certificate is portable now — instances are rebuilt in the
  checker's arena rather than trusted by `TermId`, and the ground set is rebuilt
  rather than stored. One/two/four instances all `certified=1 arena=ok`.

**Next.** A6's remainder, now scoped: the "38 QF_BV bare-UNSAT rows" are
evidence-production TIMEOUTS (`PARITY.md` 92/130), and the per-file detail is
gitignored — so it is a measurement run, not desk analysis.

**Two standing cautions for anyone quoting these numbers.** `certified=` and Lean
reconstruction are *independent axes* — a fact can be certified with no Lean
module, and 41 of 74 Lean-checked families prove nothing about their proposition
— so the two must never be summed. And `just check` is red independently of this
lane: `check-plan-authority.py` budgets the `PLAN.md` sources at 52 KB and they
were already 57 KB before this lane existed.

**The mathematics strand's primary metric drifted 4 → 11 areas unnoticed**
(`WIP`, capability-assurance, 2026-08-17). Detail:
[`01-decide-vs-certify.md`](docs/mathematics-2026-08/01-decide-vs-certify.md).

```
CAPABILITY_ASSURANCE|entries=101|areas=23|external=36|self=48|differential=2|unclassified=15
```

It asks "can a third party check without trusting us?" and calls that the
strand's primary metric — but the answer lived in 101 prose `evidence` fields,
so nobody could count it. Seven areas beyond the documented four had gained
external checking, mostly via Carcara. Agreement with an oracle is tiered
separately so it cannot inflate the number; 15 entries stay `unclassified`
rather than being sorted into a flattering bucket. Now floored.

**Next.** Items A (generate the table) and C (explicit "decided, not certified"
status) are the real fix — this checker is a heuristic over prose and says so.

**R3 done; the census is an artifact now, and `17` was not one** (`WIP`,
math-r3, 2026-08-17). The 2026-08-13 misconception audit's `census.tsv` was
never committed, so its headline "17 out of fragment" reached both
[`04`](docs/mathematics-2026-08/04-reachability.md) and
[`05`](docs/mathematics-2026-08/05-the-mathematics-dag.md) with nothing behind
it. Re-derived against the sibling `math-education` graph at `ce3e2a5`
(unchanged since, so this is not drift): **85 / 16 / 46**, not 86 / 17 / 44.
One of the 17 was a *distractor form inside* a file counted as a separate
corpus row; one genuine out-of-fragment row (`infinity-minus-infinity-is-zero`)
was missing; one (`angle-size-depends-on-arm-length`) reduces to a polynomial
identity and is moved to A, marked CONTESTED rather than asserted. Also: the
graph carries **1,567** concepts, not 1,566 — a locale collation artefact
(`sort -u` folds `C:trend-line` and `C:trendline`; `LC_ALL=C` does not).

**The adversarial corpus ranks something else first.** Censused the graph's 42
`techniques` — proof *shapes*, not propositions: 11 reachable, 19 out of
fragment, 12 heuristics (exactly the 12 the corpus itself marks
`epistemic_status: empirical`). **16 of the 19 want one thing: induction over ℕ
as a discharged schema**, against 7 for limits. Induction is the one entry on
the ranked list that is not a missing logic — the kernel has an inductive `Nat`
with an ι-computing `Nat.rec`, while the curriculum map records the `induction`
node's fragment as `LIA / BV (base + step instances)`: instances, not the
schema. So the largest single item the mathematics asks for is automating an
arrow the flywheel already has, not adding a theory.

**Next.** The obvious slice is the one the ranking names: a goal → induction
schema → reconstructed kernel term route, tested first on the technique rows
that are pure ℕ schemas (`telescoping`, `parity-argument`, `pigeonhole` at
fixed hole count). Second, the census wants a third corpus — its two are both
school-and-olympiad, adversarial along the *shape* axis but not the
*difficulty* axis.

### A1 and A2 — `DONE`, archived

Both completed. Moved to
[`docs/plan/archive/30-a1-a2-completed-programme-items.md`](docs/plan/archive/30-a1-a2-completed-programme-items.md)
so this file carries actions that are next.
### A3 — Re-certify and deepen QF_NIA (`WIP`, P1)

**Why now.** The current clean entry is 34/200 versus 89/200 (38.2%), a material
gain over the former 21-decision entry but still the weakest retained arithmetic
ratio. Twelve Axeyum-only decisions also make replay and causal classification
important, not just score growth.

**Completed checkpoint.** The exact 67-row causal census and 13-row diagnostic
are retained. Giant `distinct` expansion is bounded and typed. Model
reconstruction no longer erases oracle declines or fabricates a default model.
Probe-model reuse failed its seven-target retention gate and its temporary code
was removed. Focused SMT-LIB, solver, explanation, DPLL, NIA-linearization,
route-trace, integration, Clippy, docs, and link gates are green. One aggregate attempt found the
load-sensitive coupling deadline; the repaired attempt passed all code, solver,
frontier, CAS, rustdoc, resource, policy, resume, and Lean suites but found a
one-field stale generated CI-workflow identity at final parity-docs. Both defects
are repaired. Exact topic `3586c41d9` passed one uninterrupted external-frontier
`CARGO_BUILD_JOBS=2 just check` with exit 0 and a clean tracked tree. Topic push,
merge `0c31baf97`, and combined-main `just check` are complete and green.
Exact-SHA docs run `31190516093` and CI run `31190517748` are terminal failures
at the registered-`just` path lookup, while every non-doc CI job is green.
Repair `259797459` is integrated at `bd413357c`; exact-SHA docs run
`31192792512` and CI run `31192792245` are terminal green. This remote gate is
separate from the green solver gates.
The reconstruction-deadline diagnostic then measured both targets with
size-inadmissible dense Gomory and zero B&B nodes after deadline expiry. Its
follow-up root-repair discriminator was route-unstable under host contention,
so the cluster was rejected and every temporary solver edit removed. See the
[`v1 result`](docs/plan/qf-nia-a3-reconstruction-deadline-cluster-v1-result-2026-08-07.md).
The next cluster confirmed repeated size-admission broad cores on `SAT14/1051`
(3/3) and `SAT14/1280` (2/3). Its preregistered four-group deletion mechanism
made clauses narrower but spent up to four extra exact-theory calls per
conflict, moved both budget stops earlier, and decided neither target. The
implementation was rejected and fully removed. See the
[`large-core v1 result`](docs/plan/qf-nia-a3-large-core-cluster-v1-result-2026-08-07.md)
and
[`group-deletion v2 result`](docs/plan/qf-nia-a3-large-core-group-deletion-v2-result-2026-08-07.md).

The cheaper
[`relevance-activated bound-ladder experiment`](docs/plan/qf-nia-a3-relevant-bound-ladders-v1-result-2026-08-07.md)
then activated hundreds of checked adjacent implications without an additional
theory-oracle call, but all six target observations remained `unknown`. Its
target gate failed, controls and aggregate runs were not authorized, and all
temporary solver code was removed. The resulting
[`typed-budget partition`](docs/plan/qf-nia-a3-budget-partition-v1-result-2026-08-07.md)
classifies all 52 deferred rows as 37 mixed width timeouts, 11 all-SAT
pre-lowering estimate refusals, three UNSAT combined-theory timeouts, and one
UNSAT replay-detected model overflow. Fresh current-baseline traces show the
four-row UNSAT tail is downstream of the owning exact-search stop and cannot be
recovered soundly by the SAT-only width ladder.

**Next slice.** None is currently evidence-authorized. The v1/v2
[`clause-estimate result`](docs/plan/qf-nia-a3-clause-estimate-attribution-v2-result-2026-08-07.md)
closed the final selected route at its complete-record gate without changing
production code. Preserve the 34/200 ledger, every negative control, the
64,000,000 pre-allocation ceiling, and original-term replay, then move to A4.
Resume A3 only when independent new evidence identifies a bounded mechanism;
do not revive probe-model reuse, reconstruction reservation, group deletion,
relevance ladders, or fresh-parse clause attribution, and do not raise general
caps.

**Exit.** One preregistered cluster improves a fresh whole-list result without
losing any of the 34 decisions; all SAT answers replay on the original terms and
the ledger remains disagreement-free.

**Stop.** Do not optimize on the 12 Axeyum-only cases as if they were reference
failures, and do not raise general caps to convert time into apparent breadth.

### A4 — Deepen QF_UFLIA combination (`WIP`, yielded, P1)

**Why now.** QF_UFLIA is 94/180 (52.2%) with zero Axeyum-only decisions and 86
reference-only cases, making it the clearest combined-theory depth gap.

**Next slice.** None is evidence-authorized. The theory-model reuse result
stopped negatively; revisit only with deterministic-work evidence for the
conjunctive LIA probe. The 26 wide-integer rows remain ADR-0376 controls.

**Exit.** One preregistered, replay-checked cluster improves the clean full-list
result without losing any of the 94 decisions or weakening retained controls.

**Stop.** No general cap increase, speculative recursive MBQI, or unchecked SAT
model credit.

### A5 — Consolidate linear arithmetic after warm simplex and DL (`WIP`, P1)

**Why now.** QF_LRA, QF_IDL, and QF_RDL improved sharply but remain strict
subsets of their references. The newest architecture has not yet received one
cross-division residual census.

**Next slice.** Restart and derive the complete V2 census from the fully gated
classifier repair. Only after a zero-loss
derivation may normalization failures,
unsupported difference shapes, disequalities, explanation blowups, and
ordinary search failures be classified across the three current ledgers. Treat
the repaired high-memory LRA normalization case and the rejected global 12/12
DL split as permanent controls before adding new DL syntax. The
[`v2 cross-division census preregistration`](docs/plan/qf-linear-a5-cross-division-census-v2-preregistration-2026-08-09.md)
freezes all three populations and historical sidecars, makes all 259 retained
decisions monotonicity controls, and authorizes only fresh current-Axeyum traces
plus lossless derivation. No production change is yet authorized.

**Exit.** A/B measurement is monotone across all three divisions, exact
Farkas/DL evidence checks pass, deep input returns without recursion abort, and
the retained arithmetic fuzz suites execute nonzero cases.

### A6 — Close proof-production errors and evidence gaps (`TODO`, P1)

**Why now.** Definitive answers without checkable evidence violate the product's
core direction even when verdicts are sound.

**Next slice.** Fix the two QF_NIA `IntPow2` production errors first. Then use
route provenance—not query syntax alone—to split the 38 QF_BV bare UNSAT rows
and the broader arithmetic/string-sequence proof gaps.

**Exit.** Zero production errors; every newly credited certificate passes its
own independent checker; text-only recheck, arena-backed check, Lean
reconstruction, and bare-result counts remain separate fields.

**Stop.** Never relabel arena-backed checking as serialized proof replay or
generate proof credit through query-only re-derivation.

### A7 — Finish route observability before searched policy (`TODO`, P1)

**Why now.** `RouteTrace::to_json` landed, but the bench path and quantifier
preamble are incomplete. The proposed exploration tracker also incorrectly
placed T3.5 before its own G1 phase-3 gate.

**Required order.** Accept or revise the blocking ADRs; complete T0.2 route
registry; complete T0.6 recorder sites and `solve_explained`; finish T0.1 bench
persistence; add T2.5 public-corpus coverage; run T2.3/G1; only then consider
T3.5 policy-v0 equivalence.

**Exit.** Every registered route has a stable ID, the representative corpus
covers the catalogue or records explicit gaps, legacy dispatch replays exactly,
and G1—not enthusiasm—decides whether searched policy proceeds.

**Stop.** The exploration track remains proposed and may not preempt A2–A6.
See [`docs/plan/exploration-track/`](docs/plan/exploration-track/README.md).

### A8 — Implement SMT-LIB ordered command/event capture (`TODO`, P2)

**Why now.** The checked conformance matrix has six absent command families,
seven accepted no-ops, and zero interactive textual-session rows.

**Next slice.** Accept or revise ADR-0342, then implement S1 capture-only ordered
command/event IR with scoped declarations/definitions, reset epochs, exact query
snapshots, immediate options, and atomic continued errors before rendering.

**Exit.** The registered 14 invariants and 20 fixtures/107 commands pass through
the product path; malformed commands cannot partially mutate session state.

**Stop.** Do not add isolated output helpers and call them textual conformance.

### A9 — Restore official Lean execution and shrink the prelude (`TODO`, P2)

**Why now.** The local host currently has neither `lean` nor `elan`; remote
70/70 attestation remains open; seven ledger rows are already classified as
derivable theorems.

**Next slice.** Provision the checksum-pinned Lean 4.30 executable, prove it
runs outside the repository working directory, obtain the remote 70/70 result,
then replace the seven derivable axioms with theorem terms in dependency order.

**Exit.** Kernel tests, official Lean, generated ledger counts, declaration
order, parity docs, and mutation controls all pass; no hard-coded old count
survives.

**Stop.** Do not widen into String literals, quotient computation, or broad
ecosystem claims during this bounded trust-reduction slice.

### A10 — Build the SMT-LIB product surface after S1 (`TODO`, P2)

**Why now.** Production replacement requires more than solver depth. Once A8
freezes session semantics, add canonical response rendering and the missing
command families in dependency order.

**Next slice.** Use the generated conformance matrix to choose the first absent
family whose semantics and reset/scoping behavior are already representable.

**Exit.** End-to-end textual fixtures compare ordered outputs and state changes,
errors remain atomic, and API helpers and text mode share one semantic core.

### A11 — Make worktree and build-cache retirement routine (`WIP`, P2)

**Why now.** Accumulated per-worktree Cargo targets and the agent-target cache
filled the filesystem until a valid post-merge build failed at 585 MiB free.
The bounded cleanup recovered about 885 GiB without deleting dirty or unmerged
work, but the same failure will recur without a documented retention loop.

**Next slice.** Add a read-only inventory command or script that reports each
worktree's branch, dirty/merged state, target size, last activity, and safe
cleanup classification. Document an operator procedure that uses `cargo clean`
before worktree removal and requires explicit review for every dirty, unmerged,
detached, or cache-tag-missing path.

**Completed checkpoint.** The manual bounded cleanup and post-A3 retirement
proved the safety procedure for clean merged worktrees and reproducible Cargo
targets. The later authorized cleanup salvaged inactive dirty deltas, removed
the inactive checkouts, and retired the merged A3 targets. On 2026-08-12 all
refs were captured in a verified external Git bundle before old local/remote
branches and salvage stashes were removed. Only clean `main` is registered and
published. Automation and fixture coverage remain open.

**Exit.** The inventory is deterministic and tested against dirty, merged,
unmerged, detached, missing-target, and malformed-cache fixtures. A dry run
identifies disposable bytes without mutation; cleanup requires explicit exact
targets and preserves branches and live work.

**Stop.** Never recursively delete a worktree root, infer safety from age alone,
or remove dirty/unmerged state to meet a free-space target.

## Workstream state

| Workstream | State | Current boundary / next action |
|---|---|---|
| Integration and gates | `DONE`; 2026-08-12 | Linear A5 through `4b6b76555` is on `main` by conflict-free fast-forward. Integrated code, frontier, CAS, rustdoc, Glaurung, resource, resume, Lean, and parity gates are green; volatile frontier timings were not credited. Verify the remote ref before resume; hosted CI is separate. |
| Arithmetic deadline reliability | `DONE` | Shared deadline, CAD polls, LRA ceilings, bounded DL probing, exact resume identity, and six fresh retained divisions are complete; see the 2026-08-06 closure note. |
| Full-library measurement | `WIP`; A2 readiness `DONE` | The R1--R5 readiness stack is integrated by `8ed5ad089` and focused/aggregate/scoped/topic/full-main green; the real registered offline-build smoke passed. No live run, preparation root, or launch authority exists. A later live C0/F2 step requires separate review. |
| QF_NIA breadth | `WIP`, yielded | Current clean result remains 34/200 versus 89/200. Reconstruction, large-core deletion, relevance activation, and bounded clause-estimate attribution are closed negatively without production solver code. The final diagnostic failed its exact pipeline-boundary record gate; no mechanism or 200-row run is authorized and the 64,000,000 ceiling remains. Move to A4 unless independent new NIA evidence appears. |
| QF_UFLIA breadth | `WIP`, yielded | Historical 94/180 remains; the exact-commit restart produced 93/200 because one SAT case is wall-clock unstable. No sidecar or new result was credited. |
| LRA/IDL/RDL | `WIP`; V2 failed | QF_LRA passed; QF_IDL lost two decisions. Replay confirmed both. B1 failed and was removed; G1 found a nearby existing DL boundary. Preregister separate follow-ups; QF_RDL is forbidden. |
| QF_BV/QF_SLIA/UF/QF_ABV | `WIP`, strong selected cells | Preserve current ledgers; do not prioritize small score gains above A2–A6. |
| Evidence and Lean reconstruction | `WIP` | A6 and A9; distinct certificate/check/reconstruction claims. |
| Route exploration | `BLOCKED` beyond catalogue work | Proposed track; T0.2/T0.6/T0.1/T2.3 precede T3.5. |
| SMT-LIB/API conformance | `WIP` | A8 then A10; S1 command/event IR first. |
| CAS parity | `BLOCKED` by deliberate pause | Wave-24 code `01d47334` and pause commit `245d8f25` are ancestors of current main. Do not start wave 25 until the user resumes it and retained specialized gate evidence is re-audited. |
| Consumer apps / verified systems | `WIP`, non-critical path | Existing EVM, verifier, property, reflection, and symbolic-execution slices remain useful; do not preempt A2–A7 without measured demand. |
| Foundational resources | `WIP`, separate content lane | Keep generated-resource gates green; record only project-level priority changes here. |
| Public documentation and examples | `DONE`, current comprehensive pass | Public/crate/consumer/prover/curriculum/contributor front doors are indexed; all 76 Cargo examples and the consumer 48-case aggregate are guarded. Corrected built/planned, Lean 4.30/offline quotient, strings/P2.7, proof assurance, `i128` LRA/Farkas, native-CDCL/BatSat, RUP-only LRAT, online combination/fallback, CAS-local-vs-solver evidence, route-specific FP/datatype/nonlinear/quantifier boundaries, optional EVM/verifier certificate fields, and source-comment UNSAT-proof overclaims. Source-backed guards require nonzero full-feature tests across cookbook, learner, contributor, foundational-resource, and rules docs. Generated authorities remain canonical; reopen only for concrete drift. |
| Worktree and build-cache hygiene | `WIP`, recovered | A11; only clean `main` is registered and published. A verified 2026-08-12 external Git bundle preserves the retired refs/stashes; all old branches, salvage stashes, inactive checkouts, and their large Cargo targets are removed. Next automate deterministic read-only inventory and exact-target cleanup classification. |

## Resume protocol

1. Read this file first. Do not reconstruct current priority from historical
   result notes, old status journals, branch names, or worktree age.
2. Verify live state:

   ```sh
   git status --short --branch
   git fetch origin
   git rev-parse HEAD origin/main
   git worktree list
   gh run list --limit 10
   ```

3. If `main` is dirty, diverged, or owned by another lane, create an isolated
   worktree from current `origin/main`. One writer, one branch, one worktree.
4. Select the first unblocked item in **Next Actions**. Read its detailed phase,
   ADR, result notes, foundational DAG implications, and named handoff before
   editing.
5. During iteration, run the narrowest relevant crate or script tests. Run the
   aggregate pre-merge gate once on the finished branch. Confirm nonzero test
   counts and retain real exit codes.
6. Commit and push owned paths only. Integration requires conflict preview,
   green branch gates, merge, green main gates, pushed main, and remote-ref/CI
   verification.
7. Update this file in the same bounded increment:
   - status and exact evidence;
   - next executable action;
   - blocker or stop condition;
   - committed/pushed/integrated/remote states separately.

For concurrency and resource rules, follow
[`docs/contributor-guide/multi-agent-operations.md`](docs/contributor-guide/multi-agent-operations.md).

## Planning rules

- **One mutable project tracker:** update this file only. Root `STATUS.md` is a
  pointer; do not create root `TODO.md`; subsidiary `STATUS.md` files may retain
  local historical evidence but may not claim project-wide priority.
- **Evidence outranks prose:** benchmark JSON/TSV, generated matrices, test
  output, Git objects, remote refs, and CI results determine status. Correct this
  file when they disagree.
- **Wrong verdicts preempt everything:** reproduce, root-cause, regress, and
  repair before breadth or performance work.
- **No false green:** a focused pass is not a full gate; a running job is not a
  pass; a process-free readiness artifact is not launch authorization; a
  local commit is not integration.
- **No journal growth:** result detail belongs in a dated note under
  `docs/plan/` or a committed benchmark artifact. Keep only the current state,
  ordered queue, and a short recent-change table here.
- **Decisions require ADRs:** public operators, rewrites, encodings, backends,
  evidence artifacts, logic fragments, or priority-changing architecture need
  the applicable research question and ADR resolved first.
- **Determinism and replay are product promises:** stable order, explicit seeds
  and limits, original-term SAT replay, and independent UNSAT checking remain
  mandatory.

## Durable detail map

- **Archived lane status** (43 lanes of the 2026-08-13→15 campaign, each with the
  next action it left behind): [`docs/plan/archive/README.md`](docs/plan/archive/README.md).
  `PLAN.md` carries only lanes with work in progress; a finished or cut-off lane
  keeps its file there verbatim and is restored by moving it back into
  `docs/plan/status/`.
- Short public implementation account: [`docs/PROJECT-STATE.md`](docs/PROJECT-STATE.md)
- Full plan index: [`docs/plan/README.md`](docs/plan/README.md)
- Foundation roadmap: [`docs/research/08-planning/roadmap.md`](docs/research/08-planning/roadmap.md)
- Foundational dependency DAG: [`docs/research/08-planning/foundational-dag.md`](docs/research/08-planning/foundational-dag.md)
- Open research questions: [`docs/research/08-planning/research-questions.md`](docs/research/08-planning/research-questions.md)
- ADR index: [`docs/research/09-decisions/README.md`](docs/research/09-decisions/README.md)
- Capability matrix: [`docs/research/08-planning/capability-matrix.md`](docs/research/08-planning/capability-matrix.md)
- Scoreboard and parity: [`bench-results/SCOREBOARD.md`](bench-results/SCOREBOARD.md), [`bench-results/PARITY.md`](bench-results/PARITY.md)
- Proof gaps: [`docs/plan/generated/proof-gap-matrix.md`](docs/plan/generated/proof-gap-matrix.md)
- SMT-COMP lane: [`docs/plan/smtcomp-full-library-workstream/README.md`](docs/plan/smtcomp-full-library-workstream/README.md)
- Lean implementation: [`docs/plan/lean-system-implementation-plan-2026-07-21.md`](docs/plan/lean-system-implementation-plan-2026-07-21.md)
- Exploration proposal: [`docs/plan/exploration-track/README.md`](docs/plan/exploration-track/README.md)
- CAS pause handoff: [`docs/plan/cas-parity-handoff-2026-07-22.md`](docs/plan/cas-parity-handoff-2026-07-22.md)

## Consolidation record

The 2026-08-05 consolidation removed two conflicting append-only root journals
and one subsidiary live tracker from active use. It corrected these stale
claims:

- CAS wave 24 was described as unpushed and unintegrated; its code and pause
  commits are both ancestors of current main.
- An August 1 shell-failure resume block remained active after later green CI
  and clean parity reruns.
- The reality summary still said seven measured parity divisions after the
  ledger reached eleven.
- The exploration tracker called T3.5 next while its own G1 gate blocked all of
  phase 3.
- Repository instructions disagreed about whether `PLAN.md` or `STATUS.md` was
  the mutable source.

The containing commit establishes this file as the only current project-level
authority. Historical claims remain reviewable through Git and the dated result
notes they cite.
