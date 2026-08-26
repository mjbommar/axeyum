# ADR-0564: Bounded GF(2) tensor-rank search lifts and replays models

Status: accepted
Date: 2026-08-26
Index-summary: Encode complete bounded GF(2) tensor rank in SAT and admit models only after independent coefficient replay

## Context

ADR-0556 established a portable sparse decomposition and an independent dense coefficient
checker, but Axeyum could only check a witness supplied by another project. The bilinear
open-problems lane needs a complete existence question for arbitrary small tensors, a canonical
matrix-multiplication target generator, and a path from an untrusted SAT model back to the
portable checked artifact. A positive search result without model lifting would not establish
the tensor identity; an UNSAT solver status without proof checking would not establish a lower
bound.

## Decision

Add `Gf2Tensor::matrix_multiplication(m,n,p)` using row-major input and output bases, and expose
bounded validation/dense expansion for sparse targets. Add a deterministic SAT encoding of
“tensor rank at most r”: each summand has factor-selector variables, each coefficient product
is an exact three-input AND, and an XOR chain equates their parity to the target coefficient.
All construction dimensions have explicit ceilings.

A SAT assignment is accepted only after the original CNF evaluates true, its factor selectors
are lifted into `Gf2TensorDecomposition`, zero summands are removed, and ADR-0556's independent
checker replays every coefficient. A supplied witness can be pinned with unit clauses only
after that witness first passes independent replay. UNSAT is credited only when a DRAT proof is
accepted against the exact generated formula; the example uses the file-backed backward checker
for large textual proofs.

This first complete encoding deliberately has no term-permutation or basis-symmetry breaking.
Those transformations need separately tested model-lifting contracts before they may alter the
formula.

## Evidence

- The pinned Strassen rank-7 decomposition for the `2 x 2 x 2` matrix tensor solves, lifts, and
  replays; rank zero distinguishes a zero tensor from a nonzero one.
- Wang's published rank-20 `<3,2,4>` decomposition, after the documented output-dual basis
  permutation `k*3+i -> i*4+k`, checks all 576 coefficients. Its pinned formula has 22,984
  variables and 90,952 clauses, solves in 26 ms, lifts to rank 20, and replays. Removing one
  support index is rejected at coefficient `[0,0,0]`.
- The complete `<2,2,2>` rank-6 formula has 776 variables and 2,880 clauses. CaDiCaL 3.0.1
  returned UNSAT in 39.35 seconds and emitted a 234,288,465-byte textual DRAT proof. Axeyum's
  file-backed backward checker accepted that exact proof in 3:16.98 wall at 385,920 KiB peak
  RSS. This reproduces the known lower boundary; it is not novel.

## Consequences

- Axeyum can now express and check both sides of a bounded tensor-rank experiment end to end.
- The encoding is complete but intentionally baseline-grade. Failure to solve before a resource
  limit is telemetry, not a rank lower bound.
- Matrix witnesses using the common trace-dual `c(k,i)` convention must record and apply their
  basis permutation before replay against Axeyum's row-major output convention.
