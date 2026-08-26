# Five open-problem programme, August 2026

## Purpose

This is the durable Axeyum-side control document for the five targets surveyed in
[`docs/open-problems-2026-08/`](../../open-problems-2026-08/).  The problem-specific
narrative, literature diary, drafts, and bulky outputs live in sibling research packages;
only generic machinery and schema-valid, independently checkable evidence belong here.

The programme is not complete when a solver prints an answer.  Each lane must exercise the
full route appropriate to its claim:

1. pin the mathematical statement and external-status evidence;
2. generate the instance deterministically;
3. search with an explicitly untrusted producer;
4. replay a positive witness against the original semantics or check a negative
   certificate independently;
5. bind hashes, commands, versions, limits, and checker outcomes into an Axeyum claim or
   fact;
6. when the result is a formal identity, reconstruct it into the Lean kernel and measure
   its axiom footprint;
7. retain a falsifying control showing that the checker can fail.

“Use all of Axeyum” means use every applicable layer and explicitly record why an
inapplicable layer is not part of the assurance route.  For example, a DRAT refutation does
not become stronger by wrapping it in a structural attestation that assumes both sides.

## Packages

| Lane | Axeyum brief | Sibling research package | First end-to-end milestone |
|---|---|---|---|
| Rado / Schur | `01-rado-schur-frontier.md` | `../rado-schur-frontier/` | Replay and re-certify one settled cell, then push one named frontier |
| Bilinear rank | `02-bilinear-f2-p6.md` | `../bilinear-f2-p6/` | Encode and independently check a small known tensor decomposition before `P_6` |
| S-box optimality | `03-sbox-optimality-trio.md` | `../sbox-optimality/` | Reproduce one published SAT and one published UNSAT boundary with checked evidence |
| SIMD shuffles | `04-simd-shuffle-minimality.md` | `../simd-shuffle-minimality/` | Differentially validate AVX2 semantics and settle a constructed length-2 control |
| Bound certification | `05-certification-lane.md` | `../optimization-bound-certification/` | Independently check one small exact-rational PSD/dual certificate |

## Capability worklist

These are hypotheses until the first vertical slices measure the actual gaps.

- A reusable finite-domain circuit-synthesis encoding with deterministic variable maps,
  symmetry constraints, witness extraction, and original-semantics replay.  Bilinear,
  S-box, and shuffle lanes must share this instead of growing three encoders.
- A public GF(2) tensor/bilinear identity checker, followed by a kernel reconstruction route
  when the coefficient identity is small enough. ADR-0556 now supplies the first half: sparse
  portable rank-one terms, independent target generation, bounded dense coefficient replay,
  and a finding-dependent CLI. The published `P_6` rank-17 witness passes all 396
  coefficients; a one-entry mutation fails at `[0,0,0]`. Kernel reconstruction remains open.
- A proof-carrying Boolean-circuit synthesis envelope: circuit witness on SAT, DRAT plus
  instance pin on UNSAT, and no success state for mere solver completion. ADR-0558 supplies
  the positive half: named shared wires, explicit MSB order/gate semantics, complete truth
  tables, bounded exhaustive replay, and stable gate counts. ADR-0561 completes this for
  multiplicative complexity: deterministic affine-between-AND CNF, replayed model lifting,
  and backward-checked DRAT. ADR-0569 adds full lexicographic AND-operand ordering to the
  truth-CNF, direct-ANF-CNF, and portable-ANF routes, with witness canonicalization before
  replay. This is Zhang--Huang prior art and did not decide the known MC=6 control at 300
  seconds. General bit-gate complexity remains open.
  ADR-0570 now supplies the trusted algebraic bridge that was missing from the external
  Bosphorus experiment: deterministic definitional ANF-to-CNF lowering, source-model
  projection/replay, and file-backed checked DRAT. Its retained MC=6 refutation independently
  reproduces the known lower endpoint, so Axeyum now checks the published `[7,8]` bracket;
  the seven-AND frontier itself remains open.
  ADR-0543 now makes splitter-blind cube composition public in `axeyum-cnf`, including a
  file-backed retained-proof route. Its first MC=7 application produced and checked exhaustive
  cover proofs, but the live leaves remained undecided at 600 seconds. This is reusable
  certification infrastructure and hardness telemetry, not a frontier bound.
- Exact-rational matrix certificates with dimension/resource admission, fraction-free or
  BigInt arithmetic, independently checked `LDL^T`, and explicit PSD semantics. ADR-0557
  now removes the arithmetic-width blocker: bounded `BigRational` symmetric elimination
  reports exact pivots or declines on dimension/input/intermediate growth. The graph-bound
  dual envelope and rationalisation producer remain open.
- A typed external-certificate adapter for VeriPB as an import/replay calibration or coverage
  extension. Lane 5c does not survive as a novelty claim: Dold et al. (CP 2026) already
  proof-log ZykovColor and formally check the result with CakePBcolour.
  ADR-0555 now supplies the lower-assurance shared import boundary: hash-pinned checker and
  artifact bytes, bounded process isolation, finding-dependent exit status, and a
  content-addressed receipt.  It intentionally grants no fact-ledger or kernel authority;
  a format-specific independent checker remains necessary for that tier.
- Domain-semantics differential harnesses, especially hardware/emulator comparison for SIMD.
  ADR-0559 supplies the first reusable boundary: exact 32-byte provenance tags, faithful
  unary `vpshufb` and same-source `vperm2i128` semantics, sequence replay, complete
  one-instruction family eligibility, and checked DRAT lower bounds. A separate intrinsic
  program confirms the constructed sequence on AVX2 hardware. Broader instruction coverage
  and a generic multi-step control encoder remain open.

No capability becomes public merely because a target needs it.  Public surface still needs
the foundational DAG, semantics, model/proof lifting, replay, resource limits, determinism,
tests, and (where architectural) an ADR.

## Initial evidence and uncertainty

Live repository audit at `06c0eb5dc52c6e599bd289d60d55ad3d9a052f94` found the existing
Rado pipeline, claim ledger, proof-producing SAT core, backward DRAT checker, cube-cover
machinery, and SOS/PSD examples.  It did not find a reusable bilinear-rank, S-box-synthesis,
SIMD-shuffle, VeriPB, or exact-rational matrix-certificate component by those names.  That is
a discovery result, not yet proof that adjacent generic machinery cannot be reused.

The primary-source and Google Scholar/SERP searches on 2026-08-25 confirmed the 2022/2025
Rado papers, interval semantics and table entries in IACR ePrint 2023/1721, Wang's
arXiv:2603.07280v10 `R_F2(P_6) in [16,17]` source, and Krpan--Povh
arXiv:2607.11726v1's clique upper bounds 73/115/168.  Scholar initially missed both 2026
records, so exact arXiv identifiers and primary texts are mandatory.  Wang publishes a
lower-bound verifier and certificates; these must be ingested and independently checked
before Axeyum builds a separate rank-16 existence encoding.  Krpan--Povh's arXiv record has
an ancillary archive; the claim that no exact certificate exists remains uncredited until
that archive is inventoried.

The first settled-cell calibration re-certified `R_3(x-y=z)=14`: deterministic regeneration
gave 42 variables and 356 clauses, the in-tree producer emitted a 25-step text DRAT proof,
and the backward checker verified it after a disk round trip.  Changing the stored DIMACS
header caused exit 3 with `cnf-mismatch` before search.  The aggregate claim-certificate
sweep reported 104 claims re-checked with zero errors and 25 rows explicitly not re-checked;
that last denominator is retained because “zero errors” is not complete coverage.

The first bilinear positive-certificate slice is also complete. The published unconstrained
rank-17 decomposition was transcribed from Wang certificate record 546 into a versioned
portable artifact. Axeyum independently generated
`sum_(i,j<6) a_i tensor b_j tensor c_(i+j)` and matched every one of its 396 coefficients.
Deleting the first summand's `c0` entry exits one at the first coefficient. This reproduces
the known upper bound; it neither closes nor narrows the open interval `[16,17]`.

The exact published `P_6 >= 16` verifier also completed successfully on the pinned certificate
and backtracking archive: 26:08.34 wall, 35,357.66 user seconds, 2,255% CPU, 17,532 KiB peak
RSS, and a final lower bound 16 / `OK. Verified`. Raising the first flattening claim from 6 to
7 made the same binary recompute 6 and abort with exit 134 in under one second. This is a
faithful replay of Wang's deliberately smaller verifier, not yet an independent Axeyum proof.
The separate ADR-0555 run completed in 1,547,630 ms, revalidated the checker/certificate/archive
hashes, required both semantic findings, and emitted a `verified` receipt with canonical hash
`d5153faca4462aad95d32902e7b558d86117b221825e7efa86afa9a332145eda`.

The Krpan--Povh ancillary audit is also complete. Its sole 2.31 MB archive contains 584 run
logs, 231 graph/text files, source, and presentation scripts, but no primal/dual matrix,
MOSEK task, interval proof, or rational factorization. The solver code retains floating
objective scalars, applies `1e-9` offsets before rounding, and discards the task. Thus the
published package contains no independently replayable certificate for 73/115/168. ADR-0557
adds the missing bounded arbitrary-precision PSD checker; obtaining/rationalising a dual
matrix and checking graph-specific affine constraints remain required.

ADR-0560 now supplies that graph-specific envelope for the standard clique-theta primal.
The checker validates the exact graph, rational objective, and sparse multipliers supported
only on non-edges; it independently reconstructs `t I + Y - J` before invoking ADR-0557's
PSD decision. Tiny complete- and empty-graph controls verify, a false complete-graph bound
and detached/malformed multiplier controls fail, and resource policy remains three-valued.
The target bounds remain uncertified because their published producer retained none of the
dual variables required to populate this now-complete checking envelope.

The colouring premise was corrected on 2026-08-26 after a through-date search found Dold et
al., *End-to-End Certified Graph Colouring* (LIPIcs CP 2026, article 21). Their official
Zenodo archive contains a VeriPB-logging CertifyingZykovColor, the VeriPB and formally
verified CakePBcolour checkers, exact run commands, and result logs. Its tables contain all
137 DIMACS and 1,000 Erdős--Rényi attempts and 759 filtered checker rows. Thus “no proof
logging of any kind” is only historical for the 2025 ZykovColor release and cannot support a
2026 novelty claim. The maximum-clique theta, job-shop, and nurse-rostering targets remain
separate; filename overlap between DIMACS colouring and clique suites proves no certificate
transfer.

The first S-box positive control is now independently replayed. Zhang--Huang's Appendix C.1
`PRIMATEs^-1` circuit matches the inverse of the original specification's 32-row table under
both sources' MSB-first convention. ADR-0558 counts 8 AND, 35 XOR, and 2 NOT gates; changing
the first XOR to XNOR fails row 0 (`expected=1`, `observed=23`). This reproduces the known
upper endpoint 8 and does not close `[7,8]`.

ADR-0561 now binds that positive witness to the exact lower-bound search formula. The
complete affine-between-AND encoding has 9,326 variables and 31,712 clauses at MC=8; the
published circuit normalizes to 222 selector coefficients, whose pinned formula solves,
lifts, and independently replays all rows. Exhaustive tests over all sixteen two-input
functions reproduce the exact affine-versus-one-AND boundary, with checked DRAT for the
zero-AND negative control. Search readiness is not yet established: unpinned MC=8 interrupted
at 30 seconds and the published-control MC=6 query interrupted at 120 seconds. Those are
undecided calibration outcomes; MC=7 was not run and remains open.

The first SIMD calibration is complete. Lane-local `vpshufb` reversal followed by a
same-source `vperm2i128` half swap realizes global reversal of all 32 distinct provenance
tags. Neither instruction family can realize that target alone: the former cannot cross
128-bit lanes and the latter preserves offsets within each selected half. The corresponding
two-selector, four-clause CNF has a serialized/reparsed DRAT refutation accepted by Axeyum's
independent backward checker. A native AVX2 intrinsic oracle matches all bytes; changing the
first control byte from 15 to 14 fails at output byte 16. This proves exact length two only
for the explicitly declared two-family unary subset and carries no novelty claim.

The same-day literature refresh corrected the SIMD brief's broad framing. HieraSynth
(OOPSLA 2025) reports complete superoptimization and proven optimality for 19 of 26 RVV
programs; its pinned official artifact includes adjacent-pair/quad swaps and distance-1/4
sorting stages built from vector lane movement. Minotaur and MISAAL add further SIMD
synthesis prior art. Any publishable gap must therefore be stated as an exact intersection of
ISA, target set, operand forms, cost model, and independently checkable evidence—not as the
first minimal SIMD sequence result.

## Resume order

1. Complete provenance files with exact source versions and forward-citation searches.
2. Finish the shared finite-domain synthesis design using the now-measured bilinear, S-box,
   and SIMD vertical slices; add model lifting and proof envelopes before frontier search.
3. Add deterministic boundary encodings for the S-box lower endpoints and multi-step SIMD
   sequences, retaining complete original-semantics replay.
4. Obtain or regenerate graph-bound dual matrices for lane 5a; the arbitrary-precision PSD
   checker exists, but the published archive contains no matrix to check.
5. Schedule frontier-scale searches only after their evidence route and resource envelope
   have passed a smaller mutation-controlled instance.
