# Notes: 127-open-problems-programme

Detail moved out of [`../status/127-open-problems-programme.md`](../status/127-open-problems-programme.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Whole-tree obligation observability, 2026-08-27.** ADR-0598 adds non-authoritative start and
finish events carrying obligation index, total, tree path, and leaf/cover/structural kind. The
existing contiguous deterministic progress stream and lowest-index error remain unchanged.
The live 62.89 GB replay exposed the gap when its counter paused at 940/961 on a 921 MB leaf;
the new API makes such work visible without granting partial proof credit. The five-obligation
control pins both lifecycle events for every path and kind; focused tests and all-target/all-
feature Clippy pass.

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

**Rado exact lower bound advanced, 2026-08-26.** The seed-619 CaDiCaL producer completed every
canonical formula from 351 through 357 SAT. Exact new-relation audits then extend that checked
colouring deterministically through 368, appending `4 1 3 1 2 3 3 2 4 3` at points 359--368.
Direct enumeration accepts all 29,890 defining relations; separately, a complete 1,840-variable
assignment satisfies all 154,967 canonical CNF clauses and decodes to the byte-identical witness.
The retained witness SHA-256 is
`50b49b68ce4f5727edda7bbbcb80f69baeff69ff642c64c3557cd83956d4c517`. Therefore the checked
conclusion is now `R_5(3(x-y)=2z) > 368`; no upper bound or exact value is claimed. Every colour
is locally blocked at 369 for this fixed prefix, but that is not an UNSAT result. The obsolete
358 producer remains paused and its incomplete prefix receives no credit. Exact searches through
2026-08-26 found no indexed matching 368 bound, but that is not proof of priority.

**Rado claim ledger synchronized, 2026-08-26.** The canonical claim now carries the checked
368-point witness ahead of the historical 358-, 357-, 350-, and 319-point artifacts. Its SHA-256 is
`50b49b68ce4f5727edda7bbbcb80f69baeff69ff642c64c3557cd83956d4c517`; the independent claim
checker re-enumerates every defining relation rather than trusting the SAT encoding. The claim
remains `open`: this is a stronger lower bound, not an UNSAT certificate for 369 or an exact
Rado number.

**Rado repaired-tail climb to 404, 2026-08-26.** The local obstruction at 369 was only an
obstruction to appending one colour to a fixed prefix. A monotone relaxation audit proved that
retaining prefixes through point 180 is incompatible with 369, while retaining only points
1--140 yields a complete model. Prefix-guided exact SAT then climbed through 391; further
relaxation to 60 fixed points crossed 392 and to 50 fixed points crossed 395, reaching 404.
Axeyum imported the strongest complete assignment and evaluated it against the canonical formula
without any guiding units: 2,020 variables / 186,287 clauses. It decoded byte-identically to the
retained witness and an independent enumerator accepted all 36,046 defining triples. Witness
SHA-256 is `501f783c29a7ad069f604e394d9336118d9c35ed1695897e4440a60ccf00e973`;
canonical-CNF SHA-256 is `809d21c90860a5de661b555a856317905139f09603ca6f7df44c93748244338d`.
Thus the checked conclusion is `R_5(3(x-y)=2z) > 404`. At 405, two stronger fixed-prefix
restrictions are UNSAT and a 20-point restriction remained undecided after 120 seconds; none is
an upper bound. Fresh exact web, arXiv, and Scholar-oriented searches found no indexed matching
404 bound, which remains dated negative retrieval rather than proof of priority.

**Reusable colouring-prefix restriction, 2026-08-26.** ADR-0594 moves the successful repair
method out of shell DIMACS arithmetic. `ColouringProblem::encode_with_witness_prefix` appends
typed unit clauses only after checking problem length, witness length, and palette;
`rado_dump_cnf` exposes it with paired explicit arguments. Tests pin the untouched canonical
clause prefix, exact units, satisfying assignment, and refusals. The new API reproduces the
discovery-time 404/50-prefix formula byte-for-byte at SHA-256
`9e1f86ee99658b1448306381f9043027f5818602dfc1c1023da136ef2051f4e4`. Its contract states the
critical asymmetry: restricted SAT may be promoted only after unrestricted replay, while
restricted UNSAT is never an upper bound.

**Reusable colouring Hamming-ball restriction, 2026-08-27.** ADR-0595 composes canonical
colouring CNF with the existing generic weighted-at-most encoder instead of duplicating a
cardinality circuit. A point's change indicator is the negation of its witnessed-colour literal;
canonical one-hot clauses make this exact. The result retains source-model projection, and a SAT
result earns credit only after unrestricted CNF and independent relation replay. An exhaustive
control checks radius zero versus one with checked DRAT, projection, decoding, and replay. On the
open 405-point Rado instance, proof-free diagnostics reported UNSAT through radius 22 and timed out
at radius 23 after 120 seconds; those status lines alone received no mathematical credit before the
separate certificate run below.

**Checked Rado repair-neighbourhood boundary, 2026-08-27.** Radius 22 regenerated
byte-identically at 11,745 variables / 319,249 clauses / 6,751,821 bytes, SHA-256
`f93dc5bf...a6d`. CaDiCaL seed 722 returned UNSAT in 126.32 seconds and emitted a
609,746,173-byte textual DRAT, SHA-256 `4aed07d6...ffa5`; Axeyum's independent file-backed
backward checker returned `true` in 119.534 seconds. Thus no solution of the canonical 405-point
formula lies within 22 **labelled** changes of the checked 404 witness on points 1--404. ADR-0595
and a new checked control now make explicit that this is not distance modulo palette permutation.
The compressed CNF/proof, receipt, diary, provenance, and rebuilt paper are retained in the Rado
package. Exact searches through 2026-08-27 found no matching indexed result, which is negative
retrieval rather than priority evidence. Radius 23 and unrestricted 405 remain open, so the exact
Rado bound does not move.

**Palette-orbit repair distance, 2026-08-27.** ADR-0597 closes the labelled-coordinate gap
with one complete existential encoding, not an external loop over `k!` cases. A checked
bijection maps reference colours to model colours; per-point Tseitin matches feed the generic
weighted-at-most encoder. The wrapper validates the full model before projecting the original
colouring and separately recovers the bijection. An exhaustive two-colour control agrees with
explicit permutation enumeration for every colouring and radius; relabelling/model-replay and
resource-ceiling controls pass, as does all-target/all-feature Clippy. The real radius-22
formula is 14,194 variables / 327,843 clauses / 6,960,997 bytes, SHA-256
`33e5f3ab...b2cc`. Its no-cutoff CaDiCaL seed-723 proof producer remains live; at 27:33 it had
written 5.55 GB after 18.55 million conflicts. This prefix has no mathematical credit. A
palette-invariant conclusion requires its terminal proof and independent replay.

**Finite palette-orbit proof composition, 2026-08-27.** The tempting shortcut from labelled
UNSAT to orbit UNSAT is invalid because the canonical colouring CNF's least-first-occurrence
clauses are not invariant under arbitrary relabelling. ADR-0599 instead adds a complete bounded
lexicographic permutation enumerator, fail-closed witness relabelling, and a checker that
regenerates and checks one labelled Hamming formula for every palette permutation. A first
nonidentity five-colour control closed in 6.29 seconds, emitted a 38,821,222-byte DRAT, and
Axeyum accepted it in 1.763 seconds. Four no-cutoff workers are producing the complete 120-proof
set while the original existential producer remains live. No orbit claim is credited until all
120 proofs pass the independent proof-set checker.

**Palette-invariant Rado neighbourhood checked, 2026-08-27.** Complete production yielded
120 textual DRAT proofs / 17,595,727,192 bytes, one for every five-colour permutation. The
ADR-0599 checker independently enumerated the complete lexicographic 5! set, permuted the
hash-bound 404 witness, regenerated every 11,745-variable / 319,249-clause labelled radius-22
formula, and accepted all proofs with terminal verdict `orbit-unsat-checked`. Therefore every
valid 405-point colouring has Hamming distance at least 23 from the witness under
every palette renaming. This supersedes the earlier labelled-coordinate restriction but remains
a local repair-neighbourhood theorem: unrestricted 405 remains open and the exact lower bound
does not move. The proof manifest, receipt, diary, provenance, and rebuilt paper are retained;
the redundant single-bijection producer stopped with an uncredited 26.32 GB prefix.

**Labelled Rado radius 23 checked, 2026-08-27.** The next labelled formula has 12,150 variables,
329,778 clauses, and SHA-256 `7ab8fb91...6b2`. CaDiCaL seed 725 returned UNSAT in 155.40 seconds
with a 736,089,882-byte DRAT, SHA-256 `0f740d18...fc9b`; Axeyum's independent file-backed checker
accepted the complete proof in 127.658 seconds. Thus the canonical labelled minimum distance from
the retained witness is at least 24. This does not raise the palette-orbit distance, whose other
119 permutations have only radius-22 proofs, and does not refute unrestricted 405. The exact
lower bound remains `R_5(3(x-y)=2z)>404`.

**Bounded-parallel finite proof-set replay, 2026-08-27.** ADR-0600 removes a certificate-
consumption bottleneck exposed by the 120-member Rado radius-23 set. An explicit 1--64 worker
bound defaults to the original single-worker route; formulas and proofs check independently, but
progress, byte accounting, and failure selection remain lexicographic and deterministic. Invalid
worker counts fail before checking. The focused worker-bound control and warning-denied all-feature
Clippy pass.

**Palette-invariant Rado radius 23 checked, 2026-08-27.** All 120 permutation producers
terminated UNSAT with 23,049,937,396 textual DRAT bytes. ADR-0600's four-worker checker
independently enumerated the complete 5! set, regenerated every 12,150-variable / 329,778-clause
labelled radius-23 formula, and accepted every proof in 766.75 seconds with ordered terminal
verdict `orbit-unsat-checked`. Thus every valid 405-point colouring has minimum palette-orbit
distance at least 24 from the retained witness on points 1--404. This remains a local theorem;
unrestricted 405 is open and `R_5(3(x-y)=2z)>404` does not move.

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

**Theta external-artifact front door, 2026-08-26.** ADR-0588 separates the independently
retrieved graph from a strict `axeyum.theta-clique-dual.v1` rational artifact. The parser
rejects ambiguous graph records, unknown fields/schema, noncanonical or unreduced rationals,
and then reuses the exact graph-support and bounded BigRational PSD checker. On the actual
500-vertex / 112,332-edge `C500.9`, the universal empty-multiplier bound 500 verifies in
50.30 seconds / 70,500 KiB; changing only the bound to 499 exits 1 at a checked PSD
obstruction. This establishes the real-instance interchange path, not the published bound 73.
Current searches found numerical theta tooling but do not justify an exact-certificate priority
claim. Producing and rationalizing the missing target dual, plus binding the reduction trace,
remains the mathematical artifact gap.

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

**S-box semantic selector covers, 2026-08-26.** ADR-0586 exposes a stable typed map from
all three multiplicative encodings' selector variables to left/right AND operands, output
coordinates, and constant/input/earlier-AND basis terms. The strict external SAT-model route
now checks the exact queried CNF, projects and replays the source Boolean-ANF system, lifts a
portable circuit, and exhaustively replays the PRIMATEs-inverse truth table before writing it.
The 191-record MC=7 map leaves the 20,585-variable / 69,809-clause formula byte-identical.
A checked 32-cell cover now names variables 2--6 as gate zero's five left-operand input
coefficients. An eight-worker proof-free SAT portfolio is live without a wall-clock cutoff;
its cells carry no credit until a SAT model passes the full replay route, or every leaf has a
checked DRAT proof. The interval remains `[7,8]`.

**S-box first checked semantic leaf, 2026-08-26.** ADR-0587 adds the missing strict
partial-cover front door: given the base DIMACS, Boolean-product selectors, and a cube index,
Axeyum regenerates the cube and `base AND cube` itself before checking a retained textual DRAT.
It reports only `leaf-unsat-checked`, never global UNSAT. CaDiCaL refuted index zero, the
all-zero affine left operand of gate zero, in 0.05 seconds and emitted a 413,418-byte proof;
the file-backed checker accepts it against the regenerated 20,585-variable / 69,814-clause
leaf. Removing the final 64 bytes is rejected. Thus one of 32 leaves is now checked, while
the other eight active portfolio cells continue without a wall-clock cutoff. This is exact
partial progress, not a lower bound: `[7,8]` remains unchanged until either a replayed SAT
model appears or all leaves and the covering proof check.

**Recursive S-box leaf refinement, 2026-08-26.** ADR-0589 adds a reusable file-backed recursive
cube checker: every child formula and every covering formula is reconstructed from one trusted
root, proof files open lazily under per-file and aggregate byte caps, and a missing or invalid
leaf names its exact tree path. The first hard top-level leaf
exposed why this is needed: its raw UNSAT search took 79 minutes and the proof-producing replay
exceeded 1 GiB, while a five-selector refinement closed 30/32 children immediately. Refining
only the two hard children again, then their measured hard children, has already produced two
complete 32-leaf subtrees accepted by the existing flat checker. The full cube-8 tree remains
live and is not counted until every recursive leaf and cover checks.

**First independently replayed recursive S-box subtree, 2026-08-26.** A completed depth-five
subtree under top-level cell 8 now passes the root-reconstructing recursive checker: one split,
32 leaves, 33 nodes, and 249,251,498 proof bytes were accepted in 7:32.11 wall time at 103,936
KiB peak RSS. The root formula has 20,585 variables / 69,829 clauses and SHA-256
`9dfec7ea...1914`; the selector-27--31 manifest is hash-bound separately. Omitting one leaf
proof makes the checker exit 2 and name that path. At the contemporaneous audit, the whole
cell-8 tree had 636/683 terminal leaves complete and cell 4 had 106/373; all completed statuses
were UNSAT, but only the named subtree has received this new independent replay. Neither
top-level cell nor the MC=7 formula is therefore certified, and `[7,8]` is unchanged.

**First multi-gigabyte S-box subtree accepted, 2026-08-26.** A hard descendant under cell 8
was replaced by a complete selector-37--41 partition. Axeyum reconstructed its 20,585-variable
/ 69,839-clause root, then accepted all 32 leaf DRATs and the covering DRAT: 1,545,410,870
proof bytes, one split / 32 leaves / 33 nodes, 23:33.77 wall, and 192,700 KiB peak RSS. Formula,
manifest, cover, and checker output are separately hash-bound in the sibling package. This is
a checked subtree suitable for recursive composition, not a checked ancestor or MC=7 result;
the interval remains `[7,8]`.

**Second multi-gigabyte S-box subtree accepted, 2026-08-26.** A sibling selector-37--41
replacement also passes the recursive checker: 1,281,549,482 proof bytes, one split / 32 leaves
/ 33 nodes, 13:51.34 wall, and 197,944 KiB peak RSS against a reconstructed 69,839-clause root.
Its four authority hashes are retained in the sibling package. Both accepted replacements are
now composable into their incomplete ancestors; neither is promoted to a top-level or MC=7
verdict.

**Third multi-gigabyte S-box subtree accepted, 2026-08-26.** The next sibling replacement
passes at 1,353,759,260 proof bytes, one split / 32 leaves / 33 nodes, 6:53.92 wall, and
191,996 KiB peak RSS against another reconstructed 69,839-clause root. Formula, manifest,
cover, and checker output are hash-bound in the sibling package. This remains subtree-local;
the adjacent final replacement has completed proof production and entered independent replay.

**Fourth multi-gigabyte S-box subtree accepted, 2026-08-26.** The final targeted replacement
passes at 1,454,994,044 proof bytes, one split / 32 leaves / 33 nodes, 5:04.57 wall, and
235,748 KiB peak RSS. Its four authority hashes are retained in the sibling package. Its
parent remained six terminal leaves short at the same audit, so neither the parent nor any
higher result is yet claimed.

**Whole-tree bounded proof replay, 2026-08-27.** ADR-0596 removes the operational tail in
ADR-0590 without weakening its resource bound. The earlier four-worker checker parallelized
only the root and had fallen to two active workers after 30 root children completed. The new
route schedules every leaf and every covering proof through one bounded pool; tasks retain
only reader/cube paths and reconstruct formulas from the trusted root, so simultaneous formula
and DRAT-checker memory remains bounded by the explicit worker count. Depth-first obligation
indices preserve the sequential first-error result and deterministic contiguous progress.
Twenty-one focused tests and all-target/all-feature Clippy pass. On the retained
249,251,498-byte subtree, all 32 leaves plus its cover were freshly accepted as 33/33
obligations in 12.22 observed wall seconds. This validates the checker, not MC=7: the live
top-level tree remains uncredited until every descendant and cover accepts. The old root-only
cell-4 process is preserved under `SIGSTOP`; PID 4188179 restarted the byte-identical root as
385 whole-tree obligations and is using the intended four workers (about 350% CPU at the first
audit) rather than the prior two-worker tail.

**Bounded-parallel recursive proof replay, 2026-08-26.** ADR-0590 addresses the measured
single-core checker bottleneck without multiplying solver processes. The native API schedules
only independent root children through an explicit worker bound, reuses the unchanged recursive
formula reconstruction and backward-DRAT checker, orders failures by child index, and checks the
root cover only after all children pass. Two positive/fail-closed controls and all-target Clippy
pass. Four workers independently rechecked the retained 1,281,549,482-byte / 32-leaf sibling in
67.53 wall seconds at 351% CPU and 713,172 KiB peak RSS. Its historical sequential 13:51.34 run
had uncontrolled cache and contention differences, so no speedup ratio is claimed. The two live
full-root checks were not restarted; their silence remains uncredited and `[7,8]` is unchanged.

**Regression replay gate made load-stable, 2026-08-26.** The pre-push sweep failed twice on
different corpus rows because it ran `solve_smtlib` and its direct
`solve_smtlib_with_model` source projection sequentially under independent one-second
wall-clock deadlines; one run decided while the other correctly timed out. The test now runs
the model-carrying entry point once and replays every SAT result against that same deciding
run. This directly tests the evidence contract without turning host load into a false API
divergence. The 152-file sweep replays 44 SAT results and all-target/all-feature Clippy passes.

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

**SIMD weighted dependent-latency synthesis, 2026-08-26.** ADR-0583 adds generic,
resource-bounded weighted-at-most CNF composition and uses it without changing the ordinary
unweighted formula bytes. Under the explicitly named Haswell register-form serial dependency
profile `vpshufb=1, vpermd=3, vpermq=3, vpalignr=1, vperm2i128=3`, global byte reversal has
minimum cost four in the same exact unary language. Cost at most three is 6,024 variables /
235,303 clauses; CaDiCaL's 12,554,825-byte DRAT is accepted by Axeyum's file-backed backward
checker, while a 64-byte truncation is rejected. Cost four is SAT and lifts/replays as
`vpermd; vpshufb`. Intel explicitly scopes added latency to dependency chains, so this is not
a throughput, port-scheduling, whole-machine, ISA-wide, or priority claim. The durable sibling
package retains deterministic compressed CNF/DRAT, hashes, diary, provenance, and a cleanly
built LaTeX note. Multi-source live-register semantics and a real scheduler objective remain
the open SIMD boundary.

**SIMD multi-source live-value synthesis, 2026-08-26.** ADR-0585 replaces the unary
accumulator boundary with a reusable bounded SSA program encoding: the original input and every
earlier result remain selectable as operands. Its exact fourteen-family AVX2 language adds
two-source `vpalignr`, nonzero-control `vperm2i128`, all low/high byte/word/dword/qword unpacks,
and `vpblendd` to the prior permutation families. A GCC intrinsic differential agrees on 11
two-source modes across all 32 bytes and rejects an align-direction mutation. Global byte
reversal's one-step formula has 2,697 variables / 97,314 clauses; CaDiCaL's 1,922,088-byte DRAT
is accepted by Axeyum's file-backed checker, while a two-byte truncation fails. The 4,372-variable
/ 239,078-clause two-step formula lifts and replays `vpshufb; vperm2i128`. This proves minimum
length two only in the exact constant-control SSA language. It excludes memory, insert/extract,
logic composition, register allocation, and scheduling, and carries no novelty-priority claim.
The prior unary formula remains byte-identical, and the sibling package retains deterministic
compressed CNF/DRAT, a manifest, diary, provenance, and LaTeX write-up.

**SIMD named target closed under the brief's stated set, 2026-08-26.** A completion audit
compared ADR-0585 family-by-family with the source problem rather than substituting an undefined
whole-ISA goal. Its fourteen selectors exhaust the brief's listed `vpshufb`, `vpermd`,
`vpermq`, `vperm2i128`, `vpalignr`, eight low/high unpack forms, and `vpblendd` set. A fresh
run accepted the retained one-step DRAT, synthesized/lifted/replayed the two-step sequence,
matched all 11 hardware-oracle modes over 32 bytes, rejected the mutated oracle, and passed the
two focused tests. Thus global 32-byte reversal has exact length two in that fixed set, meeting
the brief's concrete completion criterion. This does not expand the theorem to every AVX2
instruction or establish publication priority.

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

**Complete polynomial-tensor action, 2026-08-26.** ADR-0591 adds the six homogeneous
binary-form substitutions in `GL(2,GF(2))`, acting contragrediently on both input covectors and
directly on the output, and composes them with global input interchange. Ordered summands plus
a globally minimal first term give a complete 12-element breaker rather than an assumed
stabilizer. All actions preserve all 396 coefficients of a schoolbook `P_6` decomposition;
the exact `P_2` SAT/checked-DRAT boundary and Wang's rank-17 witness also pass. The open
rank-16 formula is 26,489 variables / 105,262 clauses / 1,809,746 bytes, SHA-256
`00e5038f47c1dde3425e03cddd3625151c645ea6ddd1edbc24c3f9dc4291ddb2`; CaDiCaL seed 2606
is live without a short cutoff. Wang's current source already implements the binary-form
symmetry mathematics, so this is reusable Axeyum capability, not a novelty claim or rank result.

**Premise-explicit exact tensor rank, 2026-08-26.** ADR-0592 leaves ordinary at-most-rank
encoding unchanged and adds three nonzero-factor clauses per summand only when a caller names a
checked rank-`k-1` exclusion. The checked `P_2` rank-two DRAT plus rank-three SAT/lift/replay is
the two-sided control. Composed with the independently replayed `P_6 >= 16` certificate, the
rank-16 polynomial-action formula has 26,489 variables / 105,310 clauses / 1,811,206 bytes,
SHA-256 `bc932196...c7815`; CaDiCaL seed 2615 is live without a short cutoff. This removes
zero-product padding but does not change the `[16,17]` interval.

**Deterministic long-check progress, 2026-08-26.** ADR-0593 adds an opt-in callback to the
bounded-parallel recursive cube checker. Workers may finish out of order, but progress is
released only as the contiguous root prefix `1..n`, preserving deterministic CLI output. The
callback reports work completion, never proof credit; lowest-path failure ordering and final
cover checking remain unchanged. The two live 60/83 GB S-box checks use the older binary and
were deliberately not restarted for telemetry alone. Their active reads are not verdicts.

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
