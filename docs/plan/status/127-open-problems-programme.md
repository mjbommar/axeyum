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

**Certification novelty correction, 2026-08-26.** The brief's ZykovColor claim is no longer
current: Dold et al., CP 2026, already add VeriPB logging to ZykovColor and formally check
the result with CakePBcolour. The official 13,145,463-byte Zenodo archive (SHA-256
`5aa7f082...232e75`) contains the producer, VeriPB, CakePB, command wrapper, and experimental
logs; its tables cover 137 DIMACS and 1,000 random-graph attempts. Target 5c is therefore a
reproduction/import or coverage-extension candidate, not a first. This does not touch 5a:
the overlapping `C2000.9` stem in a colouring corpus is not a certificate for the
Krpan--Povh maximum-clique theta bound.

**Instance-bound theta duals, 2026-08-26.** ADR-0560 closes the graph/objective/PSD binding
gap: `sos::theta::check_theta_clique_dual` validates an undirected graph and sparse exact
non-edge multipliers, reconstructs `t I + Y - J`, and accepts only if ADR-0557's bounded
BigRational checker proves the slack PSD. `K_3 <= 3` and empty-three <= 1 verify; false
`K_3 <= 2`, edge-supported or duplicate multipliers, malformed graphs, and resource-policy
controls fail or decline in their distinct channels. The published target solver discarded
its dual variables, so none of 73/115/168 is certified yet.

**S-box positive-certificate slice, 2026-08-26.** ADR-0558 adds a portable named-wire
Boolean-circuit artifact and bounded complete truth-table checker. The published
`PRIMATEs^-1` witness matches all 32 independently sourced rows with 8 AND, 35 XOR, and 2 NOT
gates; changing its first XOR to XNOR exits 1 on row 0. This reproduces the known upper bound
8, not optimality or a new result. General bit-gate synthesis and a checked target-boundary
UNSAT remain open.

**Multiplicative synthesis envelope, 2026-08-26.** ADR-0561 adds the complete deterministic
affine-between-AND SAT encoding, model-to-ADR-0558 lifting with exhaustive replay, and
backward-checked DRAT for UNSAT. All 16 two-input functions reproduce their exact affine/
one-AND boundary. The published PRIMATEs-inverse MC=8 circuit normalizes into the same
9,326-variable / 31,712-clause formula; 222 selector units solve, lift, and replay. Unpinned
MC=8 at 30 seconds and the known MC=6 lower-bound control at 120 seconds both interrupted,
so no MC=7 frontier result is credited. Symmetry/performance work is next.

**SIMD semantic/minimality calibration, 2026-08-26.** ADR-0559 adds exact provenance-tag
semantics for unary AVX2 `vpshufb` and same-source `vperm2i128`. Global 32-byte reversal
replays in two instructions; the complete one-step family query is a deterministic
2-variable/4-clause CNF whose serialized one-step DRAT proof is accepted by the independent
backward checker. A GCC intrinsic oracle agrees on all 32 bytes on AVX2 hardware, while a
one-control mutation exits 1 at byte 16. This establishes minimal length 2 only in the named
two-family subset and is a calibration, not the open ISA-wide result. Multi-step synthesis
with lifted controls and additional instruction families remains open.

**Boolean-ANF control route, 2026-08-26.** ADR-0562 adds canonical resource-bounded Boolean
polynomials, deterministic Bosphorus interchange, and a sparse coefficient-DAG formulation of
the complete affine-between-AND search. The PRIMATEs-inverse MC=6 control is 738 variables / 759
equations / 8,835 monomials before external preprocessing. Bosphorus 1.2.12 reduced it to 586
free variables / 603 equations / 6,157 monomials and emitted a 5,782-variable / 62,674-clause
CNF. CaDiCaL on the independent truth CNF and CryptoMiniSat on that external CNF both remained
undecided after 300 seconds; Bosphorus solve mode overran its requested deadline and was
interrupted. External rewrites have no UNSAT authority without a checked equivalence chain, so
the published MC=6 lower control remains unreproduced and MC=7 has not been attempted.
