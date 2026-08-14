# agent-c FEEDBACK — roadmap feedback for axeyum

Written as I go. Every item cites file and line. Items are ordered by value
per unit of work, in my judgement.

**Implementation-ready summary.** The two items the next phase should start
from are F-C7 (file-backed backward DRAT checking) and F-C10 (check a *stored*
proof without re-solving; a first version is committed). Their measurement
table is reproduced here so nobody has to hunt for it — all from this lane,
same driver, same family, so the numbers are comparable:

| instance | vars / clauses | solve | text DRAT | steps | resident to CHECK | hosts that can check it |
|---|---|---:|---:|---:|---:|---|
| `R_4(3(x-y)=z)`, n=81 | 324 / 8,044 | 0.94 s | 8.86 MB | 164,538 | ~0.06 GiB | all |
| `R_4(5(x-y)=z)`, n=625 | 2,500 / 287,248 | 1044.2 s | 1.87 GB | 24,184,646 | **12.3 GiB** | s0, s1, s4 |
| `R_4(5(x-y)=2z)`, n=625 | 2,500 / 255,748 | ~6,800 s | **8.82 GB** | (checking) | **~56 GiB measured live** | **s4 only** |
| `R_4(6(x-y)=z)`, n=1296 | 5,184 / 1,038,958 | killed at 6,570 s | 6.03 GB (growing) | — | ~40 GiB projected | s4 only |

Ratio of resident memory to text-DRAT bytes: **6.6x**, measured twice
independently (12.3 GiB / 1.87 GB, and 56 GiB / 8.82 GB). It is stable enough
to schedule against and it is the single number the next phase needs.

Cost per proof step for `check_drat_backward` is **not constant** — it grows
with proof length. From the ledger's own records plus this lane:
24.2M steps -> 56 us/step; 60.5M steps (`rado-r4-a4-b3`) -> 44 us/step;
222.8M steps (`rado-r4-a2-b3`) -> 62 us/step. Budget superlinearly.

---

## F-C1 (process, HIGH) — file ownership gives no *compile* isolation

**Symptom.** I own no shared source file in this campaign. I still could not
build `axeyum-search`:

```
error[E0425]: cannot find type `Cube` in this scope
  --> crates/axeyum-search/src/cover.rs:299:50
error[E0422]: cannot find struct, variant or union type `Cube`
  --> crates/axeyum-search/src/cover.rs:300:12
error[E0425]: cannot find type `Cube` in this scope
  --> crates/axeyum-search/src/cover.rs:314:62
```

agent-b was mid-edit in `crates/axeyum-search/src/cover.rs`, a file I am
explicitly forbidden to touch. `cargo build -p axeyum-search --example
akb2_frontier` compiles the whole lib, so *any* agent's half-finished edit
in *any* file of that crate blocks *every* other agent's build of it.

**Diagnosis.** The multi-agent hygiene rules in
[CLAUDE.md](../../../CLAUDE.md)
("Multi-agent hygiene", "One writer per worktree/area at a time") are about
*write* conflicts. There is no rule about *read* conflicts, and the shared
checkout has exactly one compile state.

**Fix that worked** (now campaign README rule 7): snapshot with
`git archive HEAD | tar -x -C <scratch>`, drop your own new files in, build
and run there, and touch the live worktree only to commit. Cost: one command,
one extra `target/` directory. It also gives a *pinned* toolchain-and-source
identity for every artifact, which the claim ledger wants anyway
(`provenance.toolchain.dirty` exists precisely because builds from a dirty
tree are not reproducible).

**Recommendation for `docs/contributor-guide/multi-agent-worktrees.md`:**
state that ownership is a write-conflict rule only, and that a reader of a
shared crate must build from a snapshot, not the live tree. The alternative
that people reach for -- `git worktree` -- is ruled out by the user's standing
"no side branches or worktrees" preference, so the snapshot is the answer.

---

## F-C2 (capability gap, HIGH) — no supported way to run one instance of a
`ColouringFamily` end to end

`crates/axeyum-search` ships exactly one example,
`crates/axeyum-search/examples/recertify_rado.rs`, and it does one job:
re-certify a claim whose CNF is already stored (`usage: recertify_rado <a>
<b> <k> <n> <stored-cnf> <out.drat> <hours>`, line 24). It *requires* a
stored CNF and byte-compares against it (line 126), which is right for
re-certification and useless for a new instance -- there is no stored CNF for
a frontier point.

So the crate whose whole purpose is "the housed form of the tooling that
computed and certified Rado-number bounds" (`src/lib.rs:4`) has no runnable
front door for the thing it computes. Every agent that wants a new value has
to write its own driver, and they will all write the same five modes. I wrote
mine as `crates/axeyum-search/examples/akb2_frontier.rs`
(`valuation | verify | climb | sat | solve | cover`); I suggest promoting
something like it to a first-class `examples/rado_frontier.rs`, or better a
small binary, with `parse_family` (`src/family.rs:277`) doing the argument
parsing it already knows how to do.

Note `recertify_rado.rs` also **duplicates the encoder** in
`fn rado_cnf` (lines 51-108), a third independent copy alongside
`ColouringProblem::encode` (`src/colouring.rs:167`) and
`scripts/check-claim-certificates.py:rado_cnf`. The triplication is
deliberate and good for the *checker*; it is accidental in the *example*,
which could simply call `Rado::new(a,b,k).problem(n).encode()` and byte-compare
that. As written, a divergence between `recertify_rado.rs` and
`colouring.rs` would make re-certification pass against a formula the crate
itself no longer builds.

**Specification, since someone else will build this.** The six modes this lane
needed, which I believe are the complete set for any `ColouringFamily`:

| mode | args | what it does | why it must exist separately |
|---|---|---|---|
| `valuation` | `a b k n out` | writes the family's known construction and checks it 3 ways | the lower bound is free when a construction exists; see F-C5 |
| `verify` | `a b k in` | re-checks a stored colouring, 3 ways | witnesses arrive from elsewhere (other agents, papers, ledger rows) |
| `sat` | `a b k n out hours` | untrusted searcher (batsat) for the SAT side only | cross-check against a second engine; reports `unsat-unchecked` and refuses to call it evidence |
| `solve` | `a b k n drat wit hours` | proof-producing CDCL + inline check | the common case |
| `check` | `a b k n drat` | re-checks a **stored** proof, regenerating the formula from the parameters | production and checking have different memory profiles — see F-C10 |
| `cover` | `a b k n depth dir workers hours cap` | cube-and-conquer | when monolithic is out of reach |

Two design points that are not obvious until you need them: every mode takes
`(a, b, k, n)` rather than a file, so the formula is *always* regenerated from
the claim's own parameters and can never be silently mismatched to a stored
artifact; and every mode that produces a witness runs the same
`check_colouring` (encoder view + independent enumerator + `evaluate`) before
printing success, so "the search lied" is a distinguishable outcome
(`SEARCH-LIED` / `SOLVER-LIED`) rather than a silent pass.

A working implementation is committed at
`crates/axeyum-search/examples/akb2_frontier.rs` (558 lines, clippy-clean
under the workspace's pedantic lints). It is an example rather than a
promotable binary only because `parse_family` (`src/family.rs:277`) should be
doing the argument parsing and I did not own that file.

---

## F-C3 (defect risk, MEDIUM) — `recertify_rado`'s ~28 GiB is undocumented in
the file that needs it

The campaign brief warns that `recertify_rado` was OOM-killed at exit 137 on
26-27 GiB hosts, "which reads exactly like a refuted claim and is not one".
That is a soundness-adjacent trap: exit 137 with no output is
indistinguishable from a crash on an unsound path. Nothing in
`crates/axeyum-search/examples/recertify_rado.rs` says so -- its exit-code
table (lines 25-26) lists `4 resource; 5 deadline` but the OOM path produces
neither.

The proximate cause is that `check_drat_backward` takes a fully parsed
`&[DratStep]` (`crates/axeyum-cnf/src/drat_backward.rs`), so the whole proof
must be resident even though the *producer* was made streaming by ADR-0381.
The 226 instance's proof is 18.9 GB on disk (`artifacts/claims/rado/
rado-r4-a2-b3/claim.json`, `proof_bytes: 18921576073`); parsed, that will not
fit on any of this campaign's hosts except s4/s0.

Two recommendations:
1. **Document the memory rule of thumb** next to the exit codes: expect
   roughly 1.5 GB of resident memory per GB of text DRAT, and refuse early
   with exit 4 when `metadata(drat).len()` exceeds a budget the caller
   passes. An honest exit 4 is worth a great deal more than an OOM kill.
2. **Streaming backward check** is the real fix and is already half-built:
   `check_drat_streaming` exists for the forward checker
   (`crates/axeyum-cnf/src/lib.rs:71-74`). Backward checking needs two passes
   over the file, not the file in memory.

---

## F-C4 (API friction, LOW) — `decode_model` takes `&[bool]`, everything
else hands you a `CnfAssignment`

`ColouringProblem::decode_model(&self, values: &[bool])`
(`crates/axeyum-search/src/colouring.rs:219`) but
`StreamingProofOutcome::Sat` and `SatResult::Sat` both carry a
`CnfAssignment` (`crates/axeyum-cnf/src/lib.rs:326`). Every caller writes
`.values()`. A `&CnfAssignment` overload (or making `CnfAssignment: Deref<
Target=[bool]>`) would remove a papercut that shows up in every driver.

---

## F-C5 (evidence gap, MEDIUM) — the SAT side of this whole family is free
and the crate does not know it

Chang-De Loera-Wesley's Lemma 4.1 gives an explicit colouring -- colour `j`
by its `a`-adic valuation -- that witnesses `R_k(a(x-y)=bz) > a^k - 1` for
every coprime `(a,b)` and every `k`. Writing it down and checking it takes
**0.02 s at n = 242 and 0.21 s at n = 2400**; searching for it with
`min_conflicts` takes tens of seconds and can fail. In this session it settled
the lower-bound half of **eight** parameter points in under a second total.

`crates/axeyum-search/src/family.rs` has `constraints` and `first_violation`
but no `known_witness(points) -> Option<Witness>` hook. Adding one would let
the harness try the construction before it searches, and would make
"the lower bound is by construction, not by search" a property of the
artifact rather than a sentence in a diary.

**Specification, since someone else will build this.**

```rust
/// A colouring this family knows how to write down at `points`, if any.
///
/// MUST be checked by `verify_witness` before it is returned; a construction
/// hook that is trusted is a soundness hazard, not a shortcut.
fn known_witness(&self, points: usize) -> Option<Witness> { None }
```

- Default `None`, so no existing family changes.
- `Rado::known_witness` returns the `a`-adic valuation colouring
  `c(j) = v_a(j) + 1` **only when `gcd(a,b) == 1` and `points < a.pow(k)`**.
  Both guards are load-bearing: the construction is invalid without coprimality,
  and at `points >= a^k` the valuation exceeds the palette. The previous
  session shipped a `predicted_lower_bound` with no such guard and it was wrong
  on 19/19 parameter triples with `b > a`.
- The hook must run through `ColouringFamily::verify_witness` (which calls
  `first_violation`, the independent enumerator) before returning `Some`. If
  the construction fails its own check, return `None` and let the search run —
  never return an unchecked witness.
- Callers: `min_conflicts` should take it as the default warm start **only
  when it is valid**; see the trap below.

**A trap worth encoding in the doc comment.** A warm start from the best known
construction is a *bias*, and when the extremal object is known to be unlike
the construction it is a bias toward failure. At `(a,b,k,n) = (3,1,5,243)` the
valuation colouring provably cannot be extended — joining 243 to class `v=0`
makes `{82,1,243}` monochromatic, to `v=1` makes `{84,3,243}`, to `v=2`
`{90,9,243}`, to `v=3` `{108,27,243}`, to `v=4` `{162,81,243}` — and
`min_conflicts` warm-started from it failed three times at 5,000,000 moves
each, while the cube harness, which starts from no construction at all, found
a witness in 35.8 s. So: use the construction when it is valid at `points`,
and when `known_witness` returns `None` because the construction has run out,
that is exactly the signal *not* to warm-start from a truncated version of it.

---

## F-C6 (docs, LOW) — E3 in the findings register overstates the gap

The register says "No k=5 upper bound exists for any member of this family."
Verified against the rendered PDF of arXiv:2210.03262: correct as to *upper*
bounds, but Lemma 4.1 is stated for general `k`, so a k=5 *lower* bound
`R_5 >= a^5` is published for every coprime `(a,b)`. Suggest rewording to
"no k=5 value and no k=5 upper bound; the only published k=5 content is
Lemma 4.1's general-k lower bound `a^k`."

---

## F-C7 (capability gap, HIGH — supersedes the estimate in F-C3) — the
backward DRAT checker's memory blow-up, measured

Measured on this campaign's `R_4(5(x-y)=z)`, `n = 625` run (host s1):

| stage | on disk | resident |
|---|---:|---:|
| solving (streaming sink) | 1.87 GB text DRAT | 2.0 GB |
| `parse_drat` + `check_drat_backward` | same file | **12.3 GB** |

That is a **6.6x blow-up** from text DRAT bytes to resident memory, and it
happens *after* ADR-0381's streaming producer has done its job. My earlier
rule-of-thumb guess in F-C3 (1.5x) was wrong by more than four times; the
measurement replaces it. On a 26 GiB host this caps certifiable instances at
roughly a 3 GB proof, which is well below the ledger's existing artifacts
(`rado-r4-a2-b3` stores 18.9 GB; `rado-r4-a4-b3` stores 5.0 GB) — i.e. **this
repository already ships certificates it can no longer re-check on half its
own hosts.**

The producer streams; the checker does not. `check_drat_backward` takes
`&[DratStep]`, so the whole proof is materialised as owned `Vec<CnfLit>`
clauses. Recommendations, in order:

1. **Report the ratio in the tool, and refuse rather than die.** Every driver
   that checks a proof should print `drat_bytes` and peak RSS, and **refuse
   with exit 4 when `drat_bytes * 7 > available memory`**, naming both
   numbers. An honest refusal is not a regression; an OOM kill that reads as a
   refuted claim is. This is the cheapest item on the list — a `statvfs`-style
   read of `MemAvailable` and one comparison — and it removes the single
   failure mode the brief warns about (`recertify_rado` exit 137 "reads
   exactly like a refuted claim and is not one").
2. **Two-pass backward checking off the file.** Pass one streams the proof
   recording, per step, only `(offset, length, is_deletion)` plus the literals
   needed to build the deletion/addition timeline; pass two re-reads only the
   *marked core*. The forward checker already has `check_drat_streaming`
   (`crates/axeyum-cnf/src/lib.rs:71-74`), so a file-backed DRAT reader exists
   and does not have to be written from scratch. Expected win: the resident
   set drops from "the whole proof as owned `Vec<CnfLit>`" to "the core plus
   an offset index", and on these instances the core is a small fraction of
   the proof.
3. **Or trim first.** `trim_drat_proof` is exported next to
   `check_drat_backward` (`crates/axeyum-cnf/src/lib.rs:75`); if it can run
   file-backed it would cut the resident set by whatever fraction of the proof
   is not in the core before the checker ever allocates.

### What this currently costs the repository, concretely

- `artifacts/claims/rado/rado-r4-a2-b3` ships `proof_bytes: 18921576073`
  (18.9 GB). At 6.6x that needs **~125 GiB** to re-check — **more than any
  host in this campaign has**, s4 and s0 included (123 GiB each, neither of
  them idle). The repository ships a certificate that the system that shipped
  it can no longer verify anywhere.
- `artifacts/claims/rado/rado-r4-a4-b3` ships `proof_bytes: 5001394569`
  (5.0 GB) -> ~33 GiB. That excludes s5, s6 and s7 (26-27 GiB).
- This lane's own `(5,2,4)` proof at 8.82 GB -> ~56 GiB, which excluded s1
  (61 GiB, but only 49 available) and left exactly one usable host.

So the practical rule today is: **a text-DRAT certificate above ~3 GB is
uncheckable on a 26 GiB host, and above ~9 GB is uncheckable on a 61 GiB
host.** Every ledger row whose `proof_bytes` exceeds those thresholds is a
row whose `check_status: checked` cannot be re-established on that class of
machine. That is the argument for making this the top roadmap item.

## F-C8 (defect, MEDIUM) — `run_cover` does not stop on SAT, and overwrites
`model_path`

Observed at `(a,b,k,n) = (3,1,5,243)`, depth 6, 12 workers:

```
cell    137 [1,1,2,1,3,3] sat in 35.82s
cell 137 is SATISFIABLE — the instance is satisfiable and the run stops here
cell    136 [1,1,2,1,3,2] sat in 60.12s
cell 136 is SATISFIABLE — the instance is satisfiable and the run stops here   <-- again
```

Four minutes after the first message the process was still alive at 11 GiB,
and `model.txt` had been rewritten with cell 136's model. Two problems:

1. **"the run stops here" is not true.** In-flight workers keep going, and
   `CoverOptions::total_time` is their only bound — which on a search run is
   hours. On a satisfiable instance the wall clock is set by the slowest
   in-flight cell, not by the first answer.
2. **`model_path` is a single fixed path that later SAT cells overwrite**
   (`crates/axeyum-search/src/harness.rs`, the `Satisfiable` path). Finding
   B1 was about a model *not* being flushed; this is the mirror image — it is
   flushed and then replaced. Suggest `model_path` gaining the cell index, or
   the first writer winning.

Neither is a soundness bug: `SearchError::ModelDoesNotSatisfy` still guards
every model, and both models here were genuine. It is an artifact-integrity
bug — the file a run points at is not necessarily the model the run reported.

## F-C9 (route guidance, MEDIUM) — cube-and-conquer is the wrong default for
the `a^k` instances, and the docs say the opposite

`crates/axeyum-search/src/lib.rs:52-61` presents the cover as the way to do
the UNSAT side, with a cost model measured on `R_4(3(x-y)=2z)`, n=103 — an
instance **off** the `a^k` line. On the `a^k` line the ledger's own numbers
say monolithic wins by a wide margin (`n=81`: 0.785 s; `n=256`: 24.6 s), and
a depth-6 cover of `(5,3,4)` at `n=625` managed **4 cells in twenty minutes
at 15 GiB of 26**, because colour-of-small-integers is a weak split there.

Suggest the module docs say which side of the family each route suits, and
that `branch_points` (`src/family.rs:54`) note that its default — "skip point
1, take every second point" — was tuned on the off-line instances.

**Route guidance the framework should encode, from this lane's measurements:**

| situation | route | evidence |
|---|---|---|
| refuting `n = a^k` on the `a^k` line | **monolithic** `solve_with_drat_proof_streaming` | n=81: 0.9 s; n=256: 24.6 s; n=625: 1044 s. A depth-6 cover of the same n=625 point managed **4 cells of 4096 in 20 minutes at 15 GiB**. |
| refuting `n` off the `a^k` line | **cover**, deferred checking | the ledger's 226 and 313 were done this way |
| *finding* a colouring when the construction is exhausted | **cover** — it stops at the first SAT cell | n=243: cover 35.8 s vs batsat 457.8 s vs min-conflicts failing at 3 x 5,000,000 moves |
| pushing a lower bound one integer at a time | **`min_conflicts` warm-started from the last verified witness** | climbed 243 -> 251 in minutes; stalled at 252 across four seed families |

The general shape: **cube-and-conquer is a good SAT finder and a poor UNSAT
prover on structured instances.** On the `a^k` line the same arithmetic
structure that makes the lower bound free (one valuation colouring) also makes
the monolithic refutation cheap, and splitting on the colours of small integers
throws that structure away. Splitting on *valuation strata* rather than on
`[2,4,6,8,10,12]` is the obvious experiment nobody has run.

---

## Top three, if only three get done

1. **F-C7 — file-backed backward DRAT checking.** Measured **6.6x** blow-up
   from text-DRAT bytes to resident memory, twice independently (12.3 GiB for
   1.87 GB; ~56 GiB for 8.82 GB). This is not a slowdown, it is a wall, and it
   **stopped two mathematical results in this lane**: `(5,3,4)` at n=625 was
   killed after 3 h 11 m because its 15.5 GB certificate would have needed
   ~102 GiB to check — more than any host in the campaign — and `(6,1,4)` at
   n=1296 was killed with 6.03 GB written. It also means the repository ships
   `rado-r4-a2-b3`'s 18.9 GB certificate, which at this ratio needs ~125 GiB
   and **cannot be re-checked anywhere in this fleet**. Until the checker is
   file-backed, the cheap mitigation is to read `MemAvailable`, compare against
   `drat_bytes * 7`, and **refuse with exit 4 naming both numbers** rather than
   be OOM-killed — because exit 137 with no message reads exactly like a
   refuted claim.
2. **F-C10 — check a stored proof without re-solving.** *A first version is
   committed* (`akb2_frontier check <a> <b> <k> <n> <in.drat>`, verified against
   the known n=81 instance at the ledger's recorded 164,538 steps). It earned
   its keep the same afternoon: `R_4(5(x-y)=2z) = 625`, this lane's one new
   value, was produced on a 61 GiB host that could not check it, and the proof
   was moved to a 123 GiB host and verified there. **Four minutes of rsync
   against 110 minutes of re-solve.** The same capability belongs in
   `recertify_rado`, which always re-solves first (`recertify_rado.rs:136`).
3. **F-C2 / F-C5 — the missing front door and the checked `known_witness`
   hook.** `axeyum-search` can compute and certify Rado numbers and has no
   supported way to point it at a parameter point that is not already in the
   ledger, so every agent rewrites the same driver; and the satisfiable side of
   this whole family is a two-line construction that settled **eight parameter
   points in under a second total**, four checks each, where search took tens
   of seconds and sometimes failed outright. Both items above carry a written
   specification, because someone else is going to build them.

Runners-up: F-C9 (route guidance — cube-and-conquer loses badly on the `a^k`
line, with a measured table), F-C8 (`run_cover` does not stop on SAT and
overwrites `model_path`), F-C1 (build-from-snapshot, now campaign policy).

---

## Closing note on what the gates caught

Every validator in this repository that could fire on me, did:

- `scripts/validate-claims.py` rejected my first `rado-r4-a5-b1` for
  `evidence 'upper-drat' declares artifact_format but names no artifact` — a
  format field on a row with no bytes, which is exactly the say-so that
  finding B8 exists to prevent.
- `clippy -D warnings` rejected the driver twice before it was committable.
- `TextProofSink` reported `QuotaExceeded` by name when I carelessly wrote a
  3.7 GB proof onto a RAM-backed tmpfs, instead of truncating it silently.
- `scripts/check-claim-certificates.py` reports my two large certificates as
  `NOT re-checked here` rather than pretending a hash-pinned regenerable row
  is the same thing as a re-derived one.

That last one is the pattern worth keeping: the honest label is more useful
than the flattering one, and all four of these cost me minutes and would have
cost a reader much more.
