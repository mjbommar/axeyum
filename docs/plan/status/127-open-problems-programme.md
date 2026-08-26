# Lane: open-problems-programme — five end-to-end research targets

<!-- plan-section: lane-status -->

**WIP, open-problems-programme, 2026-08-26.** Five durable research packages now own the
Rado/Schur, GF(2) bilinear-rank, S-box optimality, SIMD-shuffle minimality, and optimization
bound-certification targets.  The Axeyum-side programme contract is
`docs/research/10-cas/open-problems-programme-2026-08.md`: pin current literature status,
generate deterministically, run untrusted search, independently replay/check, bind evidence,
and reconstruct formal identities into the kernel where applicable. Current focus stays on
`abz7`: deterministic detectable-precedence closure is complete and exhausted after one round,
and an exact checker-compatible FlatZinc/DRCP route is calibrated against both an independent
Rust checker and the Rocq-verified FznDrcpCheck. Sustained `abz7@655` proof production remains
live without a short wall-clock cutoff; the upper-bound search is closed by the replayed public
656 witness described below. The
settled-cell calibration is green for `R_3(x-y=z)=14` (42 variables,
356 clauses, 25 checked DRAT steps); a mutated DIMACS header fails closed, and the aggregate
claim sweep reports 104 claims re-checked / 0 errors / 25 rows explicitly not re-checked.
Frontier claims remain open.

**Job-shop published-witness import, 2026-08-26.** ADR-0576 adds strict parsing of the common
one-job-per-machine-order-row solution format and deterministic earliest-schedule reconstruction
over the combined job/machine precedence DAG. Malformed permutations and cyclic rows fail closed;
the resulting start matrix is independently replayed and pinned into the bounded CNF. A live
current-source search found Optimizizer's retained 15-row `abz7` solution. Axeyum reconstructed
all 300 starts at makespan 656 and returned `sat-replayed` against the 175,770-variable /
1,696,774-clause exact-window formula. This closes the upper-bound half and supersedes the local
657 search as evidence. It does not prove optimality: sustained `abz7@655` DRCP producers remain
live, and only a completed proof accepted by both calibrated checkers can close the lower half.

**Job-shop FDS gap localization, 2026-08-26.** The current pinned OptalCP 2026.2.0 preview
benchmark was reproduced on the byte-equivalent `abz7` instance with four workers, seed 1,
zero gap tolerances, verified solutions, and two level-4 no-overlap / level-3 cumulative FDS
workers. It internally raised the lower bound to 656 at 59.877 seconds and reported optimum at
108.466 seconds (5,833,383 branches, 2,636,506 failures). This is strong search-direction
telemetry, not evidence: its `proof: true` field has no exported proof object, every one of 300
solution-value slots is null, and no independent checker can replay its inference. A hash-bound
package receipt records that fail-closed boundary. The generic missing capability is now sharply
identified as certifiable scheduling propagation/search composition, while all seven independent
DRCP/DRAT proof producers continue without short cutoffs.

**Checked energetic-overload boundary, 2026-08-26.** ADR-0577 adds a reusable cumulative-task
window type and exact energetic checker: task membership, domains, duration, demand, capacity,
and compulsory energy are recomputed with checked arithmetic, and only a strict overload is a
conflict. Portable job-shop conflicts replay either defining job-chain windows or ADR-0574's
precedence closure; schema, bound, machine, interval, and energy mutations fail closed. The
bounded exhaustive scan evaluates all integer intervals under explicit ceilings. On `abz7@655`,
3,222,600 intervals / 64,452,000 task contributions identify machine 5 `[0,538)` at 533/538
required/capacity energy in 0.75 seconds. Repeating after all 256 forced precedences gives exactly
the same ratio, so no root conflict exists and none is emitted. Conditional conflict composition
under branch domains is the next required layer; the target lower bound remains open.

**Checked conditional energetic clauses, 2026-08-26.** ADR-0578 adds canonical semantic
start-bound assumptions, independent conditional-overload replay, and an exact bridge from each
assumption's negation to the existing operation prefix variables. A bounded deterministic
producer searches one interval and relaxes its explanation before replay. On the strongest
`abz7@655` interval it checks 40 candidates and proves that job 2 operation 10 must start after
532: the contrary domain requires 539 units in 538 available. The 175,170-variable /
1,690,226-clause precedence-closure formula gains exactly one checked unit. Matched 30-second
CaDiCaL runs remained unknown, so no speedup or lower-bound claim is made. Fourteen focused
job-shop tests and all-feature Clippy are green; the next layer is a bounded all-interval unit
fixpoint before multi-assumption clauses or checked cover composition. All seven full-proof
producers remain live.

**Exhaustive standalone energetic units, 2026-08-26.** ADR-0579 scans every machine interval
and both one-sided bounds for every flexible task under explicit resource ceilings, uses monotone
binary search for the strongest implied unit, and independently replays every retained artifact
before bulk CNF insertion. The `ft06 = 55` control finds two units and preserves a lifted/replayed
optimal schedule. On `abz7@655`, 3,222,600 intervals / 128,904,000 candidates / 322,261,348
task checks complete in 7.49 seconds and retain exactly two deductions: `start(2,10) > 532` and
`start(7,0) < 24`. The exact formula gains two clauses; a matched 30-second SAT run remains
unknown. This exhausts standalone units, not contextual propagation under learned bounds, and
does not change the open lower-bound verdict.

**Contextual energetic fixpoint, 2026-08-26.** ADR-0580 turns replayed unit conflicts into a
bounded implication chain: semantic start bounds propagate across job chains and detectable
machine precedences, every contextual overload retains the complete assumption conjunction, and
each clause is independently replayed before insertion. A single release command reproduces four
exhaustive `abz7@655` rounds with conflict counts 2/2/1/0 and six final bounds. Forced machine
orders rise from 256 to 861; 1,289,053,403 exact task-energy checks produce five contextual plus
two premise clauses, growing the 175,170-variable formula from 1,690,226 to 1,690,233 clauses.
The closure stabilizes without a precedence or energetic contradiction, and matched 30-second
CaDiCaL runs remain unknown, so no lower bound or speedup is claimed. This exhausts the current
contextual energetic-unit layer; certified edge-finding/not-first/not-last explanations or checked
branch composition are the next materially different lower-bound routes. All seven sustained
DRCP/DRAT producers remain live.

**Rado frontier file-backed proof consumption, 2026-08-26.** The exact
`R_5(3(x-y)=2z)@351` producer is still live and its multi-gigabyte DRAT prefix carries no
credit. Before completion, the independent `akb2_frontier check` path was changed from holding
both the complete proof text and a parsed step vector to Axeyum's existing file-backed backward
checker, which retains only the reverse clause plan required by the algorithm. The settled
`R_3(x-y=z)=14` control regenerated a 25-step / 263-byte proof and the changed command accepted
it from disk with `route=file-backed-backward`; all-target/all-feature Clippy and
warning-denied Rustdoc pass. This is checker-readiness, not a result at 351.

**Strict external SAT-model replay boundary, 2026-08-26.** A reusable harness parser now
imports SAT Competition output only when it contains exactly one `SATISFIABLE` status, a
terminated complete assignment of the declared width, and no duplicate contradiction,
out-of-range literal, post-terminator payload, or missing variable. The job-shop importer no
longer owns a permissive duplicate, and `akb2_frontier check-model` evaluates the imported
assignment against the regenerated CNF, lifts its one-hot colouring, independently replays the
defining relation, re-evaluates the lifted witness, and only then writes it. Eight malformed
controls fail closed; focused tests, all-target/all-feature Clippy, and warning-denied Rustdoc
pass. The live `n=351` producer has not returned SAT, so this closes an evidence-route gap rather
than establishing a new bound.

**Rado 351 local-search experiment closed honestly, 2026-08-26.** The ordinary portfolio
completed 192 equal-budget jobs / 3.84 billion moves in 5,142.3 wall seconds without a
colouring. The experimental constraint-weighted portfolio completed 96 jobs / 1.92 billion
moves, also without a colouring; normalized user CPU was 225.66 versus 207.89 seconds per job
(+8.55%), and peak RSS was 401,924 versus 178,932 KiB (2.25 times). Different thread counts and
changing contention make wall time non-comparable. Weighting demonstrated no frontier benefit
and was removed rather than promoted. The independently justified CLI `noise`/`tie` controls,
percentage validation, and one-colour/100%-noise panic repair remain; focused tests,
all-target/all-feature Clippy, and warning-denied Rustdoc pass. Both completed `not-found` runs
carry no UNSAT or upper-bound credit; the exact proof-producing run remains live.

**Rado exact lower bound advanced, 2026-08-26.** The seed-619 CaDiCaL producer completed the
canonical 351-, 352-, and 353-point formulas SAT; the 353 run took 19:14.90. Every complete
assignment passed the strict SAT Competition importer, regenerated CNF evaluation, unique
one-hot decoding, independent enumeration of the defining relation, and lifted-witness
re-encoding. The retained strongest witness has 353 entries, uses all five colours, covers
27,495 defining triples / 142,767 clauses, and has SHA-256
`ff825f641352d5e6a59e098f9da648d1d8fa4d8481cb6ab41c694b5f33faedd2`. Therefore the checked
conclusion is now `R_5(3(x-y)=2z) > 353`; no upper bound or exact value is claimed. A persistent
exact driver is live at 354 and advances only after both replay routes. A post-result literature
refresh through 2026-08-26 found no five-colour bound at least 353 for this equation, but that
negative retrieval is not proof of priority.

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

**Bilinear first-summand normalization, 2026-08-26.** ADR-0568 applies a complete
matrix-tensor stabilizer reduction: a chosen nonzero summand occupies slot zero, its first
factor is one of the `min(m,n)` matrix rank-normal forms, and only the remaining slots are
lex-ordered. Strassen with padding and Wang's rank-20 witness both pin/lift/replay; a valid
decomposition with a non-normal first term is rejected. The open rank-19 formula is 22,641
variables / 89,206 clauses and again reached 300 seconds without model/proof. This remains
`interrupted`, not rank evidence. The de Groote normalization is classical prior mathematics;
the next safe step is a complete stabilizer-orbit cover, not a single assumed orbit.

**S-box complete operand ordering, 2026-08-26.** ADR-0569 replaces the partial
first-coefficient breaker with an opt-in complete lexicographic order on every pair of affine
AND operands across the truth-CNF, direct-ANF-CNF, and portable-ANF routes. Exhaustive
three-bit comparison, every two-input function, a reversed witness, and the published
PRIMATEs-inverse MC=8 circuit all pass lift/replay controls; the old MC=6 formula remains
byte-identical when its mode is selected. The complete MC=6 formula is 6,406 variables /
21,901 clauses and reached 300 seconds with `UNKNOWN`, no model, and no proof. Zhang--Huang
already specify this full order and report their control at 239 seconds, so the technique is
prior art and Axeyum's known lower-bound reproduction remains open. MC=7 was not attempted.

**Trusted Boolean-ANF/CNF bridge, 2026-08-26.** ADR-0570 adds a generic deterministic
definitional extension from bounded Boolean-ANF systems to CNF, with shared monomial-prefix
gates, exact parity chains, projected SAT-model replay, and independently checked DRAT. The
published PRIMATEs-inverse MC=8 witness traverses the complete portable-ANF/CNF/circuit route.
The byte-stable MC=6 source system lowers to 16,820 variables / 57,017 clauses; CaDiCaL 3.0.1
refuted it in 228.81 seconds, and Axeyum's file-backed backward checker accepted the
1,068,108,069-byte proof in 1,377.68 seconds. A 100-line truncation fails closed. This finally
reproduces the known MC>=7 endpoint and, with the replayed MC<=8 witness, independently
checks the published `[7,8]` bracket. It does not decide MC=7. ANF/CNF conversion and the
lower bound are prior work; incomplete forward-citation access precludes a first-artifact
novelty claim.

**Splitter-blind cube composition and first MC=7 frontier probe, 2026-08-26.** ADR-0543 is
accepted and `axeyum-cnf::cube` is now public. The substantial dormant implementation and its
twelve controls were preserved; the landed increment adds file-backed backward checking and
deterministic emitter/checker CLIs, bringing the focused suite to fourteen. Every leaf formula
and the cover CNF are reconstructed from the base formula and literal lists, so no splitter
formula is trusted. Szeider's July 2026 LRAT-Catcher already composes cube proofs inside Lean,
so neither the argument nor formal composition is novel. The PRIMATEs-inverse MC=7 portable
ANF/CNF frontier is 919 variables / 970 equations and 20,585 CNF variables / 69,778 clauses.
A monolithic 600-second run interrupted. A first cover exposed source variable 1 as forced;
two live leaves interrupted. An adaptive exhaustive cover on variables 2 and 3 has a checked
two-step covering proof, but all four leaves interrupted at 600 seconds. No model or complete
leaf-proof set exists, so `[7,8]` is unchanged.

**Premise-explicit exact-budget circuit reduction, 2026-08-26.** ADR-0582 adds a reusable
normal form for a query known to be at its minimum possible budget: every AND operand has a
nonconstant term, every AND result is used later, every essential primary input occurs, and
every varying output coordinate is nonconstant. The ordinary at-most-budget encodings remain
unchanged; the PRIMATEs driver requires the independently checked MC=6 premise by name before
adding these clauses to its MC=7 formula. The generic Boolean-ANF/CNF bridge now composes
validated clauses over source selectors without exposing its private extension variables,
and pure ANF export refuses the disjunctive mode. All eight exact-MC-one two-input functions
remain SAT and replay through both direct and portable routes; malformed source indices fail
closed. The complete MC=7 formula is 20,585 variables / 69,809 clauses with SHA-256
`176513848d1fa511bca2a7b5c50255f6dabe6ebff696eb9f62abcfad0f43ae76`. Two persistent
proof-producing CaDiCaL runs have no short cutoff and remain uncredited. Soeken 2020 already
publishes the corresponding nonconstant/all-used constraints, so no technique novelty is
claimed and `[7,8]` is unchanged.

**Bilinear complete first-factor orbit cover, 2026-08-26.** ADR-0571 exposes typed canonical
support/selector descriptors from normalized matrix-tensor encodings, avoiding dependence on
private CNF allocation. The `<3,2,4>` rank-19 formula reports `[0] -> 495` and `[0,3] -> 496`.
Its complete four-cube Boolean-product cover has a checked covering proof; the two leaves
inconsistent with the base one-hot constraint have independently checked DRAT proofs. The two
live leaves each returned `UNKNOWN` after 600.01 seconds, and their incomplete 5.29/5.68 GB
proof streams were deleted. The exact manifest, cover artifacts, and receipt are retained in
the sibling package. The partition is certified, not the rank bound; `[19,20]` is unchanged.
Focused CNF/search tests, all-feature Clippy, rustdoc, generated-plan/index checks, and links
are green. The full `just check` is independently red before reaching Rust tests because the
settled `Nat.fib_le_succ` fact omits two proof-derived dependencies; correcting those edges
then exposes a stale historical Autogenesis child-qualification contract. Neither belongs to
this lane, so no full-gate success is claimed.

**Bilinear polynomial-family artifact boundary, 2026-08-26.** ADR-0581 adds the missing
family-native `P_n` synthesis driver over the existing complete tensor-rank encoder. It exports
deterministic DIMACS, pins known decompositions, imports only complete strict SAT Competition
models, lifts them to portable JSON and independently replays every coefficient, or checks a
completed textual DRAT from disk. The two-sided `P_2` control replays rank 3 from an external
model and checks a 130-byte rank-2 refutation; empty output exits nonzero without writing a
witness. Wang's rank-17 `P_6` construction pins, lifts and replays all 396 coefficients. The
complete ordered `P_6@16` formula has 13,289 variables / 52,110 clauses, raw SHA-256
`d5692510...6d940`, and is under sustained no-short-cutoff CaDiCaL search. Its live proof prefix
carries no rank credit. The primary source remains arXiv v10 (2026-07-30), and refreshed exact
searches found no closure through 2026-08-26; this is negative retrieval evidence, not priority
proof.

**Job-shop exact windows and semantic order cover, 2026-08-26.** ADR-0572 adds an opt-in
complete operation-domain restriction from exact job-chain earliest/latest starts and exposes
all machine-order selector variables as typed, deterministic semantic records. `ft06` retains
its checked 55/54 boundary while shrinking by more than half. `abz7@655` falls from 381,418
variables / 4,343,486 clauses to 175,170 / 1,689,970, but 600-second lower and upper runs and
a deterministic 300-second CP-SAT upper run all remained `UNKNOWN`. A checked Boolean-product
cover over two typed order selectors proves four leaves exhaustive; every leaf remained
`UNKNOWN` at 120 seconds. ADR-0573 fixes the generic bottleneck this cover exposed: internal
proof SAT now branches only on variables occurring in clauses, taking the sparse cover from
more than two minutes without completion to a 3.55-second checked proof. Exact formulas,
semantic maps, cover proof, manifest, and resource receipt are retained in the sibling package;
incomplete 4.15 GB leaf proof streams were deleted. `abz7 = 656` remains uncertified.

**Job-shop detectable-precedence closure, 2026-08-26.** ADR-0574 adds deterministic
longest-path earliest/latest propagation over job and logically necessary machine edges.
Every machine pair is classified free, forced in either direction, or infeasible; forced
edges close to a fixpoint and remain attached to typed selectors. Baseline/closure parity and
lifted replay cover all 64 two-job/two-machine routing/duration patterns across bounds zero
through eight (576 checks). `abz7@655` forces 256 orders and `@656` forces 254, but both
stabilize after one productive round. A matched 180-second SAT run remained unknown. A
redundant time-capacity encoding was measured at 2.27 million variables / 7.97 million clauses
and 2.12 GiB RSS, then removed rather than retained as a misleading capability.

**Job-shop DRCP proof interchange, 2026-08-26.** ADR-0575 adds strict deterministic bounded
job-shop FlatZinc export on the exact predicate surface shared by Pumpkin and its checkers:
job-chain domains, `int_lin_le` precedences, and unit-demand/capacity-one cumulative machine
constraints. The `ft06@54` calibration emits a 19,396-byte gzipped full DRCP proof accepted by
Pumpkin's independent checker and FznDrcpCheck rebuilt from its Rocq development; weakening a
machine duration makes both reject inference 1887. CP 2026 already establishes the general
formally verified DRCP route, so no technique novelty is claimed. A full `abz7@655` DRCP run
is live on `/data0`; only completion plus both checks can establish the lower bound. A
deterministic makespan-678 schedule has independently replayed and now warms a sustained
six-hour CP-SAT search for the still-missing 656 witness.
