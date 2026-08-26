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

**SIMD five-family bounded synthesis, 2026-08-26.** ADR-0566 closes that named next step with
a complete multi-step SAT encoder for permutation-preserving unary `vpshufb`, `vpermd`,
`vpermq`, same-source `vpalignr`, and same-source `vperm2i128`. Global byte reversal's
one-step query is 2,663 variables / 87,940 clauses; CaDiCaL's 957,982-byte DRAT proof is
accepted by Axeyum. The 4,302-variable / 159,912-clause two-step query lifts and independently
replays a `vpermd; vpshufb` program. A hardware oracle agrees with every modeled family and
rejects a direction mutation. This proves minimum length two only in the exact unary language;
LLVM already records a two-operation AVX2 byte reverse, and current Scholar/arXiv/web searches
do not justify a novelty-priority claim. Multi-source and weighted-cost synthesis remain open.

**Boolean-ANF control route, 2026-08-26.** ADR-0562 adds canonical resource-bounded Boolean
polynomials, deterministic Bosphorus interchange, and a sparse coefficient-DAG formulation of
the complete affine-between-AND search. The PRIMATEs-inverse MC=6 control is 738 variables / 759
equations / 8,835 monomials before external preprocessing. Bosphorus 1.2.12 reduced it to 586
free variables / 603 equations / 6,157 monomials and emitted a 5,782-variable / 62,674-clause
CNF. CaDiCaL on the independent truth CNF and CryptoMiniSat on that external CNF both remained
undecided after 300 seconds; Bosphorus solve mode overran its requested deadline and was
interrupted. External rewrites have no UNSAT authority without a checked equivalence chain, so
the published MC=6 lower control remains unreproduced and MC=7 has not been attempted.

**External Rado-bound correction, 2026-08-26.** ADR-0563 adds generic palette
canonicalization and a dual-route colouring witness CLI: independent defining-relation replay,
then evaluation against the freshly regenerated CNF. A live search located Li's public
296-point `R_5(3)>296` witness at pinned commit `e0b30e5...75a74`; Axeyum verifies its
equivalent `3(x-y)=z` colouring and the 1,480-variable / 125,222-clause formula. A one-colour
mutation fails at monochromatic `[1,22,63]`. This supersedes Axeyum's 251-point retained best
and removes any novelty claim for that weaker bound. A 144-million-move probe across all five
warm extensions and a cold start found no 297-point witness; that is explicitly not an upper
bound.

**Bilinear bounded-rank search, 2026-08-26.** ADR-0564 adds row-major matrix tensor generation
and a complete resource-bounded `GF(2)` rank SAT encoding whose models lift into ADR-0556
artifacts and independently replay. Wang's `<3,2,4>` rank-20 witness, after an explicit
output-dual basis permutation, matches all 576 coefficients and passes the pinned 22,984-
variable / 90,952-clause path; a one-support mutation fails at `[0,0,0]`. The known
`<2,2,2>` rank-6 control generated 776 variables / 2,880 clauses; CaDiCaL refuted it in 39.35
seconds and Axeyum's file-backed backward checker accepted its 234,288,465-byte DRAT proof in
196.98 seconds. The open `<3,2,4>` rank-19 baseline (21,806 variables / 85,824 clauses)
reached 300 seconds without a model or proof, so its verdict is interrupted and the bracket
remains `[19,20]`.

**Job-shop certificate route, 2026-08-26.** ADR-0565 adds strict OR-Library parsing,
independent schedule replay, complete bounded-makespan SAT with machine-order/prefix clauses,
untrusted model lifting, and file-backed DRAT checking. The public `ft06` control is now
certified end to end: a 3,692-variable / 15,958-clause SAT model lifts to a replayed makespan-
55 schedule, while the 3,620-variable / 15,640-clause makespan-54 formula has a 375,015-byte
DRAT proof accepted by Axeyum; a precedence mutation fails. This reproduces optimum 55 and is
not advertised as a first result despite finding no earlier artifact in current searches.
The target `abz7@655` formula fits at 381,418 variables / 4,343,486 clauses, but its lower
run and the `@656` witness run both reached 300 seconds without proof/model. Both verdicts are
interrupted, so `abz7 = 656` is not yet certified here.

**Bilinear term-order symmetry, 2026-08-26.** ADR-0567 adds an opt-in complete breaker for
permutation of rank-one summands while leaving all retained baseline formulas byte-stable.
It lex-orders concatenated factor bits, canonicalizes padded witnesses, and passes an
exhaustive comparator test plus reversed-Strassen and Wang rank-20 replay controls. The open
rank-19 formula is 22,688 variables / 89,388 clauses; CaDiCaL reached 300.19 seconds and
7,140,981 conflicts without model/proof. This is interrupted telemetry, not rank evidence,
and it shows that the `19!` term labels are not the whole obstruction. Search found explicit
prior term ordering, so no technique-novelty claim is made; stabilizer/basis symmetry is next.
