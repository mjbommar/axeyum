# Lane: open-problems-programme — five end-to-end research targets

<!-- plan-section: lane-status -->

**WIP, open-problems-programme, 2026-08-26.** Five durable research packages now own the
Rado/Schur, GF(2) bilinear-rank, S-box optimality, SIMD-shuffle minimality, and optimization
bound-certification targets.  The Axeyum-side programme contract is
`docs/research/10-cas/open-problems-programme-2026-08.md`: pin current literature status,
generate deterministically, run untrusted search, independently replay/check, bind evidence,
and reconstruct formal identities into the kernel where applicable.  Next: finish
primary-source currency checks; then specify the shared
finite-domain synthesis interface against bilinear, S-box, and shuffle controls before adding
public surface.  The settled-cell calibration is now green for `R_3(x-y=z)=14` (42 variables,
356 clauses, 25 checked DRAT steps); a mutated DIMACS header fails closed, and the aggregate
claim sweep reports 104 claims re-checked / 0 errors / 25 rows explicitly not re-checked.
Frontier claims remain open.

**Shared import boundary, 2026-08-25.** ADR-0555 adds a non-authoritative, hash-pinned
external-certificate replay runner for all five packages.  It validates checker and artifact
bytes before execution, hard-kills a timed-out process session, requires an observable finding
in addition to exit zero, and emits a content-addressed three-outcome receipt.  Four focused
tests cover success, pre-execution mutation rejection, false-success rejection, and timeout;
format-specific independent checking is still required before any imported result gains
Axeyum evidence or kernel authority.

**Bilinear upper-certificate slice, 2026-08-25.** ADR-0556 adds a public bounded exact
`GF(2)` rank-one tensor-decomposition checker and independent full-polynomial target
generator. Wang's published rank-17 `P_6` witness matches all 396 target coefficients; a
one-entry mutation exits 1 at `[0,0,0]`. This independently reproduces the known upper bound
17 but does not narrow `[16,17]`. The pinned published lower-bound verifier has now replayed
`P_6 >= 16` in 26:08 wall / 17,532 KiB peak RSS; raising an early flattening claim from 6 to
7 aborts in under one second after recomputing 6. The separate hash-pinned replay completed
in 1,547,630 ms with verdict `verified` and canonical receipt hash `d5153fac...145eda`.
This is upstream-checker reproduction, not an independent Axeyum lower-bound proof.

**Certification arithmetic and source audit, 2026-08-25.** Krpan--Povh's sole arXiv
ancillary was completely inventoried: it contains graphs, scalar logs, and source, but no
primal/dual matrix or certificate; its source rounds floating MOSEK objective bounds with a
`1e-9` offset and discards the task. ADR-0557 adds a bounded exact `BigRational` PSD checker
alongside the existing checked-`i128` route. Large coefficients succeed, indefinite controls
fail, and intermediate growth declines explicitly. Producing and graph-binding an exact dual
matrix remain open.

**S-box positive-certificate slice, 2026-08-26.** ADR-0558 adds a portable named-wire
Boolean-circuit artifact and bounded complete truth-table checker. The published
`PRIMATEs^-1` witness matches all 32 independently sourced rows with 8 AND, 35 XOR, and 2 NOT
gates; changing its first XOR to XNOR exits 1 on row 0. This reproduces the known upper bound
8, not optimality or a new result. A deterministic synthesis CNF and checked boundary UNSAT
remain open.

**SIMD semantic/minimality calibration, 2026-08-26.** ADR-0559 adds exact provenance-tag
semantics for unary AVX2 `vpshufb` and same-source `vperm2i128`. Global 32-byte reversal
replays in two instructions; the complete one-step family query is a deterministic
2-variable/4-clause CNF whose serialized one-step DRAT proof is accepted by the independent
backward checker. A GCC intrinsic oracle agrees on all 32 bytes on AVX2 hardware, while a
one-control mutation exits 1 at byte 16. This establishes minimal length 2 only in the named
two-family subset and is a calibration, not the open ISA-wide result. Multi-step synthesis
with lifted controls and additional instruction families remains open.
