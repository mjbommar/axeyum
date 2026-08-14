# One framework across a normally fragmented pipeline — agent-c's record

A record of which axeyum component did each stage of this lane's work, and
what a conventional pipeline would have used instead. Numbers are measured in
this session, not estimated. The seams where it did **not** hold are in the
last section; they are part of the record.

## The pipeline, stage by stage

| # | stage | axeyum component | conventionally |
|---|---|---|---|
| 1 | state the lower-bound colouring | `examples/akb2_frontier.rs::valuation_colouring` (Lemma 4.1's `c(j) = v_a(j)+1`) | a hand-written script per parameter point |
| 2 | check it, three independent ways | `ColouringProblem::first_monochromatic` (encoder view) + `ColouringFamily::first_violation` (brute force, shares no code with the encoder) + `CnfFormula::evaluate` (the CNF itself) | one hand-written checker; nobody checks the checker |
| 3 | encode the decision problem | `Rado::constraints` -> `ColouringProblem::encode` -> DIMACS, byte-identical to `scripts/gen-rado-instance.py` (`tests/encoding_parity.rs`) | a bespoke CNF generator whose faithfulness is an unexamined assumption |
| 4 | search, engine 1 | `axeyum_search::harness::run_cover` (cube-and-conquer, depth 6, 15625 cells, 12 workers) | march/cube + a solver + glue scripts |
| 5 | search, engine 2 (cross-check) | `axeyum_cnf::solve_with_rustsat_batsat_timeout` (ADR-0007) | a second solver binary, different model format, different exit conventions |
| 6 | produce a refutation proof | `solve_with_drat_proof_streaming` + `TextProofSink` (ADR-0381) | kissat/CaDiCaL writing binary DRAT |
| 7 | check the proof | `parse_drat` + `check_drat_backward` (ADR-0382) | drat-trim |
| 7b | check a proof produced *elsewhere* | `akb2_frontier check` (added this session; regenerates the formula from `(a,b,k,n)`) | **nothing** — `solve` bundled the two and `recertify_rado` always re-solved |
| 8 | verify the model against the *original* object | `ColouringProblem::decode_model` + `verify_witness` + `SearchError::ModelDoesNotSatisfy` | ad hoc, per solver, per format |
| 9 | record the result as evidence | `artifacts/claims/rado/*/claim.json` + `scripts/validate-claims.py` + `scripts/check-claim-certificates.py` | a table in a paper |

Zero external solvers and zero external checkers were used for any result in
this lane (ADR-0002).

## Four things worth naming

### 1. Eight lower bounds in 0.5 s, each checked three ways

`R_k > a^k - 1` was settled for **eight** parameter points at a total cost
under one second, because the colouring is written down from Lemma 4.1 rather
than searched for:

| (a,b,k) | n | forbidden sets | wall |
|---|---:|---:|---:|
| (3,1,5) | 242 | 16,120 | 0.02 s |
| (5,1,4) | 624 | 69,626 | 0.02 s |
| (5,2,4) | 624 | 61,876 | 0.02 s |
| (5,3,4) | 624 | 54,126 | 0.01 s |
| (6,1,4) | 1295 | 255,205 | 0.07 s |
| (4,1,5) | 1023 | 228,225 | 0.07 s |
| (7,1,4) | 2400 | 762,147 | 0.21 s |
| (4,3,4) | 255 | 10,017 | 0.01 s |

Each passed three checks *inside the framework* — the encoder's own view, an
independent brute-force enumerator that shares no code with the encoder, and
evaluation of the encoded CNF on the decoded one-hot assignment — and then a
fourth from the ledger's Python enumerator. In a fragmented pipeline stages 1
and 2 are one script written by one person, and the checker inherits the
author's misunderstanding. The whole point of `first_violation` existing
*next to* `constraints` is that the duplication is deliberate.

### 2. Two independent searchers, one verdict, one notion of "satisfies"

On `(3,1,5)` at `n = 243`:

- `harness::run_cover` found **cell 137**, cube `[1,1,2,1,3,3]`, in **35.8 s**;
- `solve_with_rustsat_batsat_timeout` found a **different** satisfying
  assignment in **457.8 s**.

Both models were checked against the *same* `CnfFormula` object by the *same*
`evaluate`, and both decoded colourings were checked by the *same*
`first_violation`. Cross-checking two search engines is routine advice;
doing it without a shared definition of the object being satisfied is where
it usually goes wrong, and that shared definition is what a single framework
supplies for free. (The min-conflicts SLS, a third engine, failed on this
instance — recorded in DIARY §7, because a disagreement between engines that
you only notice when they agree is not a cross-check.)

### 3. The integration property that made the rest believable

Before touching the frontier I replicated `R_4(3(x-y)=z) = 81`, a value
already in the ledger from a previous session on a different machine:

```
valuation 3 1 4 80 -> witness-verified (3 checks)
solve     3 1 4 81 -> verified-unsat, steps=164538, solve 1.040 s, check 0.978 s
```

The stored claim `rado-r4-a3-b1` records `proof_steps: 164538`. **The same
number, exactly.** That is not a solver property — it is the claim ledger, the
proof-producing CDCL and the backward checker agreeing bit-for-bit across
sessions, machines and rustc versions. It is why the refutation that followed
90 minutes later could be believed on its first run, rather than needing a
second opinion from a tool outside the system.

### 4. Where it did NOT help

**The shared checkout would not compile.** `cargo build -p axeyum-search`
failed on `cover.rs:299/300/314` (`cannot find type Cube`) because another
agent was mid-edit in a file this lane is forbidden to touch. Owning no shared
source file did not confer build isolation. Worked around with
`git archive HEAD | tar -x` into a scratch directory; that is now campaign
README rule 7. **This is a real seam**: one framework means one compile state,
and the ownership map does nothing about it.

**One verifier was deliberately written OUTSIDE the framework.**
`artifacts/verify-renaming.py` checks that `x + by = bz` and `b(x-y) = 1z`
induce the same hypergraph on `[n]` (49/49 cases identical). That check exists
to decide whether an external paper's claim collides with ours, so its value
depends entirely on being *independent* of our encoder. Writing it in axeyum
would have made it worthless. This one is not a gap — it is the correct
placement of a trust boundary, and it is the same reasoning that puts
`check-claim-certificates.py`'s enumerator in a separate language.

**The monolithic route was not viable on a 26 GiB host.** `parse_drat` +
`check_drat_backward` on the `(5,1,4)` certificate needed **12.3 GiB resident
for 1.87 GB of text DRAT — a 6.6x blow-up**, incurred *after* ADR-0381 made
the producer streaming. The producer streams; the checker does not. On s7
(26 GiB) the `(3,1,5)` monolithic run had to be killed at 2.6 GB of proof
rather than allowed to OOM, because an OOM kill and a refuted claim look
identical from outside. Recorded as FEEDBACK item F-C7; it is the single
capability gap that most limits what this integrated pipeline can certify.

**The cube-and-conquer harness holds each cell's proof in memory**
(`harness.rs:605` calls `solve_with_drat_proof_with_limits`, the non-streaming
variant), so cover memory is `workers x largest cell proof`. A depth-6 cover
of `(5,3,4)` at `n = 625` reached 15 GiB of 26 with **4 cells of 4096** done
in twenty minutes. Same root cause as above: half the stack adopted ADR-0381
and half did not.

**`run_cover` does not actually stop when a cell reports SAT.** It printed
"the run stops here" at 35.8 s and was still alive four minutes later at
11 GiB, having meanwhile overwritten `model.txt` with a second SAT cell's
model. The verified witness survived only because it had already been copied.
FEEDBACK item F-C8.


## Postscript — the seam that turned into a capability

Stage 7b did not exist when this lane started. It exists because the seam in
the last section bit hard enough to be worth closing: `(5,2,4)` at `n = 625`
produced **8.82 GB** of text DRAT on a 61 GiB host, and checking it there
needed ~56 GiB. The process climbed to **55.7 GiB** and was going to be
OOM-killed.

What made the recovery possible was an integration property rather than a
tool: because the sink flushes before the driver reads the proof back, the
certificate on disk was already complete when the check phase started —
confirmed from the bytes, the file ends `... -217 0\n0\n`, the empty clause.
So the process could be killed, the file moved to a 123 GiB host, and the
**same** `check_drat_backward` pointed at it, with the formula regenerated
from the same four integers by the **same** encoder. Nothing had to be
re-derived and nothing had to be trusted across the move: the four parameters
are the identity of the instance, and the ledger's `instance-pin` row exists
to say exactly that.

In a fragmented pipeline this is the awkward case — the solver's proof format,
the checker's expectations, and the generator that made the formula are three
separate programs, and "is this proof about the formula I think it is?" has no
mechanical answer. Here it is a byte-comparison against a regeneration, which
is why a certificate can be moved between machines at all.

Cost of the move: about four minutes of rsync against ~113 minutes of re-solve.

## What this lane did not finish

Recorded here rather than in a summary, because a fragmentation story that
only lists successes is not a record:

- `R_4(6(x-y)=z) = 1296?` — killed mid-solve at 1 h 49 m with 6.03 GB of proof
  written and no verdict. Lower bound `R_4 > 1295` established; refutation not.
- `R_5(4(x-y)=z) = 1024?` — both attacks killed undecided (cover: 658 of
  15,625 cells in ~1 h 35 m; batsat: 2 h 17 m). Lower bound `R_5 > 1023`
  established; the question it would have answered is untouched.
- `R_5(2(x-y)=z)` — nothing established beyond the trivial `R_5 >= 56`. The
  `a = 2` line has no construction, so its satisfiable side is a real search
  problem and stage 1 of this pipeline does not apply to it at all.
