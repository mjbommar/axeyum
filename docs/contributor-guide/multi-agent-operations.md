# Multi-Agent Operations — Safe Concurrent Work

Operational companion to
[`multi-agent-worktrees.md`](multi-agent-worktrees.md) (which defines the
worktree *model*). This file records the *operating discipline* that keeps that
model from going wrong, hardened by a real multi-agent session where several of
these were learned the hard way (2026-07-22).

**One-line rule:** one worktree per agent, one branch per worktree, one
integration owner for `main`, and **nothing merges to `main` unless it is
green**.

---

## Why: what actually breaks when agents share a checkout

These are real failure modes observed when SMT-COMP + Lean-kernel + FP work all
happened inside the shared integration checkout on one feature branch:

| Failure | Root cause | Fixed by |
|---|---|---|
| Every agent's commits landed on *one* feature branch, diverging far from `main` | one checkout = one branch = one HEAD, shared by all | worktree per agent (own branch/HEAD) |
| Could not switch the checkout to `main` | `main` was checked out in another worktree (git forbids the same branch twice) | that's the model working — leave `main` where it lives |
| A merge put a **non-compiling tree on `main`** | a broken in-flight commit rode along; no build gate before merge | the **green-before-merge gate** (below) |
| `cargo fmt` / shared-index / "who owns this dirty file" | one working tree + one index shared by N writers | separate index + working tree per worktree |
| Dozens of uncommitted files from 3 lanes tangled together | everyone's WIP in one tree | isolated WIP per worktree |
| Solver processes ran unbounded and cooked a host | `pkill -f compete.py` orphaned children with non-firing timeouts | the clean-stop procedure (below) — not a git issue |

Worktrees fix the first five. The last two are **cross-worktree** and need
separate discipline (see §4).

---

## 1. The worktree layout (separate folders under `~/projects/personal/`)

One integration checkout stays on `main` and **no topic agent works in it**.
Each agent gets a sibling folder + its own branch, all sharing one `.git`:

```sh
cd ~/projects/personal/axeyum          # integration lane — on main, owned by the integrator
git fetch origin
git worktree add ../axeyum-quant   -b agent/quant/mbqi-sat-direction origin/main
git worktree add ../axeyum-strings -b agent/strings/qf-slia-decode   origin/main
git worktree add ../axeyum-smtcomp -b agent/smtcomp/full-library-run origin/main
```

```
~/projects/personal/axeyum/            # integration lane, on main, untouched by topic agents
~/projects/personal/axeyum-quant/      # topic agent, on agent/quant/...
~/projects/personal/axeyum-strings/
~/projects/personal/axeyum-smtcomp/
```

Each agent works **only** inside its own folder, on its own branch, editing
**only its own files**, committing often. No agent runs git in another agent's
folder or in the integration checkout. Clean up with `git worktree remove`.

Branch naming: `agent/<lane>/<task>` (e.g. `agent/quant/mbqi-sat-direction`).

---

## 2. Rules that still apply *inside* each worktree

Worktrees remove working-tree collisions, not object-store or format collisions:

- **Pathspec commits only:** `git add <files>` then `git commit -m … -- <files>`.
  Verify with `git show --stat`. A bare `git commit` still sweeps everything in
  *that* tree.
- **`rustfmt --edition 2024 <file>`, never `cargo fmt`** (still workspace-wide
  within a tree — it reformats files you don't own).
- **Separate `target/` per worktree.** This is the cost: each worktree builds
  its own `target/` (disk-heavy). **Do NOT** share one `CARGO_TARGET_DIR` across
  concurrent worktrees — parallel `cargo build` on a shared target corrupts it.
  For shared *compile cache* (safe), use `sccache`, not a shared target.
- **Never** `git stash` / `checkout` / `restore` / `reset` / `branch -f` on
  anything you did not create — another lane's uncommitted WIP or live worktree
  is there.

---

## 3. The green-before-merge gate (the piece whose absence broke `main`)

The red-`main` incident was **not** a git problem — it was merging a branch that
**did not compile** (a match arm was missing for a newly added enum variant).
git merged it cleanly because there was no textual conflict; the break was
semantic.

**Integration-owner rule — a branch that is not green does not merge:**

1. Preview conflicts without touching a worktree:
   `git merge-tree --write-tree --name-only main agent/<lane>/<task>`.
2. Verify the *branch* builds green — check it out in a scratch worktree (or the
   integration lane if it's yours) and run **`just check`**
   (fmt + clippy + `cargo test --workspace` + doc + link check), or at minimum
   `cargo check --workspace --all-targets`.
3. Only then merge. **One integrator decides merge order**; topic agents push
   branches and do not merge to `main` themselves.
4. After merging, re-run `just check` on `main` before the next merge — catch
   semantic merge breaks (an enum variant on branch A, a match on branch B) that
   are invisible to `git merge-tree`.

This single gate turns a divergent merge onto a live `main` from a landmine into
routine.

---

## 3b. Iterate fast — scope the gate to what you changed

**THE RULE — read this before you ever type `just check`:**

> **In the edit → test loop, run ONLY the tests for the crate / file you changed
> (`cargo test -p <crate>`). Run the full `just check` exactly ONCE — right
> before you hand the branch to the integrator, never per commit. Running the
> full gate in the iteration loop is the single biggest time sink in this repo.
> Do not do it.**

`just check` is the **pre-merge / CI** gate: every sub-gate over the *whole*
workspace (`cargo test/clippy --workspace --all-features`, full `doc`, the Python
gates). Deliberately thorough and **slow** — tens of minutes. It is **not an
iteration tool.** A one-crate or Python-only edit should gate in **seconds**, and
nothing forces you to run more than that while developing.

**Your iteration loop — pick the narrowest command that covers your change:**

- **Rust, one crate (this is the default):** `cargo test -p <crate>` — e.g. a
  solver change → `cargo test -p axeyum-solver --features full`; one file → `cargo test -p
  axeyum-solver --test nra_differential_fuzz`. `cargo test -p axeyum-cas --lib`
  is ~21 s (moment proofs are `#[ignore]`d — see below).
- **Python, one module:** `python3 -m pytest scripts/tests/test_<x>.py`.
- **Not sure what's in scope?** `just check-scope` diffs your change vs `main` and
  runs only the relevant crate/tests, flagging anything it can't confidently
  scope so you know to fall back to the full gate.
- **The order-255 CAS moment proofs are `#[ignore]`d** (~15 min *each*). Normal
  `cargo test -p axeyum-cas` skips them; run them explicitly with
  **`just moment-proofs`**, and only when you touch moment / squared-binomial /
  falling-factorial code. The full `just check`/CI lane still runs them (via the
  `moment-proofs` gate), so coverage is unchanged.
- **When you do need a full run, go parallel + safe:** prefer **`just
  test-guarded`** (parallel, 64 GiB mem-capped so a runaway aborts instead of
  OOM-killing the host) over a single-threaded `RUST_TEST_THREADS=1` run —
  roughly 2× faster, and it removes the OOM fear that motivated single-threading.
- **Don't babysit GitHub CI.** Run `just check` (or `test-guarded`) once right
  before you push, then let CI be an async backstop — check it **once** when it
  finishes; never sit in a `while true; sleep 30` poll loop (that's a second
  ~40-min serial wait for no benefit).

Reserve the full `just check` for the moment right before you hand the branch to
the integrator — not for the edit-test loop.

---

## 4. Cross-worktree resource discipline (git can't help here)

Multiple agents share more than the object store — they share the NAS corpus,
the compute hosts, and the thermal envelope. These bit us this session:

- **Compute hosts run HOT.** `s4`/`s5`/`s6`/`s7` reach **92–99 °C** under full
  core load (`s4` also runs the project `llama-server`). Run **s4 only, N≈8,
  thread-pinned** (`RAYON_NUM_THREADS=1` so workers == active cores). Never
  full-load a host; watch temps (`sensors`) and back off at ~90 °C. See the
  SMT-COMP work stream's gotchas:
  [`../plan/smtcomp-full-library-workstream/README.md`](../plan/smtcomp-full-library-workstream/README.md).
- **Orphaned solver runaways.** `pkill -f compete.py` kills the *parent* runner
  but orphans its `axeyum-smtcomp` children, whose internal `--timeout-ms` does
  **not** fire on some hard inputs → they run unbounded and accumulate across
  launch/kill cycles, saturating and overheating the host. **Always stop
  background solver fleets with `scripts/smtcomp_repro/stop_run.sh`** (kills the
  children first, then sweeps). Never leave a run stoppable only by killing
  parents.
- **Don't hammer another lane's host/worktree.** `main` and other lanes live in
  worktrees on shared hosts (`/nas4/...`, `/home/.../.cache/codex/...`); running
  a heavy build or job there competes for CPU and heat with that lane.
- **Shared NAS paths are append-mostly.** The corpus (`/nas3/data/axeyum/corpus/`)
  is read-only in practice; run outputs go under a run-specific dir. Don't
  overwrite another run's output dir.

---

## 5. Fallback: if you must share one checkout

Lightweight collaboration in one tree (e.g. a human + one agent) is sometimes
fine. Minimum safe procedure:

1. **One writer per file-area at a time** — divide by crate/dir; never two
   agents in the same file.
2. **Pathspec add/commit only**; `git show --stat` after every commit.
3. **Never** `stash`/`checkout`/`restore`/`reset`/`branch -f` on files you did
   not create.
4. **No `cargo fmt`, no workspace `cargo test`/`check`** while another agent has
   uncommitted WIP that may not compile — you'll build their broken tree (the
   red-`main` story, locally).
5. Keep the checkout on **one agreed branch**; do not fork feature branches
   inside it (that's how a shared checkout silently drifts off `main`).

---

## Quick checklist

[ ] Working in **my own worktree folder**, on **my own `agent/*` branch**?
- [ ] Editing **only my files**; pathspec commits; `git show --stat` verified?
- [ ] `rustfmt <file>` (never `cargo fmt`); my own `target/` (no shared `CARGO_TARGET_DIR`)?
- [ ] Branch **green (`just check`)** before asking the integrator to merge?
- [ ] Background solver runs stoppable via `stop_run.sh`; host temps watched; not full-loading a shared host?
- [ ] Not touching another lane's worktree, WIP, or `main`?

---

*See also: [`multi-agent-worktrees.md`](multi-agent-worktrees.md) (the model),
[`gap-ownership.md`](gap-ownership.md) (who owns what).*

---

# Lane dispatch and isolation — what the coordinator gets wrong

The incidents below are the coordinator's failures, not the lanes'. Each cost
real time, and in most of them the lane behaved reasonably given what it was
told. The trigger index is in [CLAUDE.md](../../CLAUDE.md#gotchas).

## The stall, and how to make it cheap

Eleven subagents have finished their real work, started a long check, and
returned a holding message with the results in hand. Prohibitions have not
fixed it — briefs that named background tasks, monitors, scheduled wakeups and
second agents *explicitly and in bold* still produced stalls, because the lane is
not reasoning about mechanisms; it is reasoning that one more check would make
its report complete.

Two things actually help, neither of which is another prohibition:

- **Do not ask a lane to run `cargo test` at all.** The coordinator re-runs the
  full gate before every merge regardless, so a lane's narrow run is duplicated
  work that gates nothing and is the single largest source of stalls. Ask it to
  commit and report; verify it yourself.
- **Require an EARLY commit.** "Your first commit must land within your first ten
  tool calls, containing whatever you have, even if it does not compile — say so
  in the message." A stalled lane with commits is resumed by reading its branch;
  a stalled lane without them needs a round-trip, and its work is one
  `git worktree remove` from gone.

When the measurement *is* the task, bound it instead of forbidding the wait:
"profile a SINGLE invocation", and — the part that unlocks it — "if one full run
is too long, profile a REDUCED input and say the numbers are from a reduced run."

Diagnose before waking a quiet lane: `git log --oneline main..<branch>` plus
`git status --porcelain` in the worktree tells you whether there is work to
rescue. Do not infer a stall from a quiet transcript alone.

## A subagent that backgrounds a job and waits for it stalls

**A SUBAGENT THAT LAUNCHES A BACKGROUND JOB AND WAITS FOR IT STALLS, AND THE
HARNESS WILL NOT WAKE IT.** Measured 2026-08-22: three separate Sonnet lanes
finished their real work, launched a `cargo test` in the background as a final
check, and returned "waiting for the background test run" as their entire
report. Each had results in hand and reported none of them. Each needed an
explicit `SendMessage` to resume, costing minutes per incident and one full
round-trip of context.

This is the multi-agent form of the standing "run long gates in the FOREGROUND"
rule, and it bites harder for a subagent because a stalled subagent looks
*completed* to the coordinator — the task notification arrives with a
no-content result and nothing indicates the work is done but unreported.

**THREE MORE STALLED ON 2026-08-24, AND THE COORDINATOR HAD THE ANSWER IN
THIS PARAGRAPH THE WHOLE TIME.** Every one of those briefs said, in bold, to
run checks in the FOREGROUND and that "a check which did not complete is
reported as 'did not run'". All three backgrounded the kernel gate anyway and
returned a holding message with finished work in hand; each needed a
`SendMessage` to resume. The gate they were told to run takes 550 s under lane
contention, and no amount of instruction survives that.

The paragraph below already says what to do — *"tell it not to measure at all
and do the measuring yourself"* — and it was not followed, because asking for a
narrow per-module check feels cheap and reads as diligence. It is neither. The
coordinator re-runs the full gate in its own checkout before every merge
regardless, so a lane's narrow run is **duplicated work that gates nothing**
and is the single largest source of stalls. Do not ask a lane to run
`cargo test` at all. Ask it to commit and report; verify it yourself.

**Telling it not to is not enough — measured 2026-08-22, a fourth lane stalled
after the brief explicitly said "foreground with bounded timeouts, report
partial results rather than holding them".** The instruction does not survive
contact with a slow gate: the agent reasons that one more check would make the
report complete, and a backgrounded check looks like the way to get it.

What does work is removing the temptation. Give the subagent the specific
bounded command to run and tell it that a check which did not complete is
reported as "did not run" — and point it at the prebuilt binaries under
`target/release/examples/`, which take no cargo lock, for everything that is
only a measurement. Better still, tell it not to measure at all and do the
measuring yourself: the coordinator has to re-verify the numbers anyway. And note that prebuilt binaries under
`target/release/examples/` run directly, take no cargo lock at all, and are the
right tool for measurement when several lanes are contending — a sweep that
queues behind three other lanes is what tempts an agent to background it in the
first place.

**AND WHEN THE MEASUREMENT *IS* THE TASK, "do not background it" is not
advice a lane can follow.** Ninth stall, 2026-08-25: a lane sent to profile a
gate that takes ~500 s per run returned *"I'll stop here and wait for the
monitor's completion notification."* It could not do the work without a long
run and had been told not to background one, so it did both and reported
neither. Telling it harder would not have helped.

What works is bounding the measurement in the brief instead of forbidding the
wait: **"profile a SINGLE invocation"**, and — the part that unlocks it — *"if
one full run is too long, profile a REDUCED input and say the numbers are from
a reduced run."* A profile of a smaller input still locates the hotspot, and a
located hotspot is the deliverable. Give the lane a way to finish, not just a
way to fail.

**ELEVENTH STALL, 2026-08-27, AND THE BRIEF HAD ALREADY ENUMERATED MONITORS.**
The prohibition above was followed to the letter in the brief — *"do not defer
the answer by ANY mechanism — not a background task, not a monitor, not a
scheduled wakeup, not a second agent"* — and the lane started a monitor and
returned *"I'll pause here and wait for the monitor's notification."*
Enumerating the forbidden mechanisms does not work either, because the lane is
not reasoning about mechanisms; it is reasoning that one more check would make
its report complete.

**So stop trying to prevent the stall and make it CHEAP.** What separated this
incident from a costly one was purely whether commits existed:

    git log --oneline main..worktree-agent-<id>   -> EMPTY
    git -C .claude/worktrees/agent-<id> status --porcelain
      M crates/axeyum-lean-kernel/src/creal.rs
      M crates/axeyum-lean-kernel/src/creal/creal_tests.rs
      M crates/axeyum-lean-kernel/src/creal/crossing.rs

Three modified files, zero commits, ~30 minutes of work visible to nobody. The
brief said *"Commit BEFORE running any long check"* — the instruction exists,
and a lane that is about to stall is exactly the lane that skips it, because
it intends to commit *after* the check confirms the work.

Two things that actually help, neither of which is another prohibition:

- **Require an EARLY commit, not a pre-check commit.** "Your first commit must
  land within your first ten tool calls, containing whatever you have, even if
  it does not compile — say so in the message." A stalled lane with commits is
  resumed by reading its branch; a stalled lane without them needs a
  round-trip, and its work is one `git worktree remove` from gone.
- **Diagnose before waking it.** `git log --oneline main..<branch>` plus
  `git status --porcelain` in the worktree tells you in one command whether
  there is work to rescue and what the resume message should demand. Do not
  infer a stall from a quiet transcript alone — see
  `is-a-subagent-actually-stalled`.

The resume message that works names the recovery, not the failure: tell it to
treat any unfinished check as **"did not run"**, commit what it has *even if
broken*, and report — explicitly, that partial results reported now beat
complete results reported never.

**TENTH STALL, 2026-08-26, AND IT HAD A MECHANICAL CAUSE — EVERY LANE WORKTREE
BUILDS ITS OWN `target/` FROM SCRATCH.** Measured that day: **83 GB of lane
`target/` directories across 125 worktrees**, 400-800 MB each. Nothing is
shared, so a lane's first check pays a full cold build of the workspace
*behind the `cargo-serialized.sh` flock*, which is many minutes before a
single test runs. That wait is what a lane backgrounds. No amount of
instruction survives it, and the nine retrospectives above all read the
behaviour as discipline when half of it is arithmetic.

It also reframes the disk: the worktree tree is roughly half build artifacts,
so reaping worktrees reclaims far more than the source suggests.

**AND THE PROHIBITION MUST NAME THE OUTCOME, NOT A MECHANISM.** That lane's
brief said, in bold, *"Do NOT background a cargo run and wait for it."* It
started a **monitor** instead and stalled inside the letter of the rule —
a monitor is not literally a backgrounded cargo run. Write the constraint as
*"do not defer the answer by ANY mechanism — background task, monitor,
scheduled wakeup, or a second agent — and if a check has not finished when you
are ready to report, report it as 'did not run'."*


## Dispatching without `isolation: "worktree"`

**DISPATCHING WITHOUT `isolation: "worktree"` PUTS THE LANE IN THE SHARED
CHECKOUT WHILE ITS BRIEF SAYS OTHERWISE.** Measured 2026-08-26: three lanes
dispatched for one prelude, all briefed in bold that they were working in
their own worktree, and the `Agent` calls carried no isolation. Two of the
three needed the same `creal.rs` and `creal_tests.rs`.

Nothing surfaces it. `git status` looks ordinary, the lane's own report reads
like normal work, and the first real symptom would be two lanes overwriting
each other's whole-file edits. It was caught only by noticing that a lane 32
minutes and 104 tool calls into its task had no worktree directory.

Two rules, and the second is the one that cost time:
- Pass `isolation: "worktree"` for any lane that will WRITE, and never assert
  isolation in a brief you did not provide.
- **`git worktree list` is the check — not the presence of a directory under
  `.claude/worktrees/agent-<id>`.** A capable lane may create its own worktree
  somewhere else entirely (one did, on `/data0`, as its first action after
  noticing the shared tree was mid-merge). Inferring "no `.claude` directory"
  ⇒ "working in the shared checkout" is wrong, and it produced a false alarm
  aimed at the one lane that had handled the situation correctly.


## Unblocking a held-out family: declare the construction and nothing else

**A LANE SENT TO UNBLOCK A HELD-OUT FAMILY DECLARES THE CONSTRUCTION AND
NOTHING ELSE — declaring the ordinary supporting theorems alongside it SPENDS
the family it was opening.** Measured 2026-08-30, and it was the coordinator's
brief that caused it.

ADR-0645 measured that no held-out-safe family remained and named the exact
unblock: declare `Nat.dist` and `Nat.nth`. Its screen said Dist was clean,
**0 of 18** — measured before `Nat.dist` existed. The lane declared the
definition and, as good practice everywhere else in this repository, **seven
supporting theorems**. Five carry exact Mathlib mirror names in the Dist pool,
and `dist_comm`/`dist_self` sort into the alphabetically-first ten a draw
takes. R9 then correctly refused the family:

    GUARD REFUSED: R9 2 held-out candidate(s) ... not blind:
      [('natural-distance','Nat.dist_comm'), ('natural-distance','Nat.dist_self')]

Control, with Dist moved to development: `GUARD PASSED -- 300 entries, 120
held-out`. So that one screen is the single mechanical blocker, and the
contamination is real rather than incidental.

The sibling lane's `Nat.nth` declared **the construction only** (`Nat.nth`,
`Nat.nthAux`, both `Definition`s) and its family survived at 0 of 11. Same
brief, same session, opposite outcome, and the difference is exactly the extra
theorems.

This is ADR-0542's contamination shape arriving through the door marked
"helpful", and R9 caught it at the door rather than after a draw. Two rules:

- **Brief it explicitly.** "Declare the definition and its evaluation test.
  Do NOT declare theorems ABOUT it" — the useful proofs can land the day after
  the draw, from development, where they cost nothing.
- **Re-screen after declaring, before drawing.** A readiness figure measured
  before the unblock existed is a figure about a different tree; ADR-0645's
  `0 of 18` was honest when written and false by the time it mattered.


## A blind evaluation population is a shared resource with no owner

**A BLIND EVALUATION POPULATION IS A SHARED RESOURCE WITH NO OWNER, AND
TOUCHING ONE MEMBER SPENDS THE WHOLE FAMILY.** `artifacts/autogenesis/nursery-v1.json`
preregisters 214 Mathlib propositions into train / development / **held-out**,
and the split key is `<family>:<statement-shape>` precisely because a proof
route for one member is evidence about its siblings. On 2026-08-21 a capsule
was registered against `F:ml430-nat-gcd-greatest-0a04214a` — a held-out row —
and it cost **19 of 76** held-out propositions, 25% of the partition, for one
theorem.

Nothing caught it for a day. `check-autogenesis-nursery.py` validates the
manifest's *internal* integrity and never inspects what operations do to it;
`validate-autogenesis-operations.py` mentioned partitions zero times; the
README's "immutable held-out populations" guarantee was prose. Now gated by
`scripts/check-autogenesis-holdout-isolation.py`, and the repair is an
amendment ledger, never a deletion (ADR-0542).

The trap that nearly caught the repair too: **"dependency-ready facts" and
"train + development" are both 138 and are different sets** — the ready set is
44 train, 44 development and **50 held-out**. Check the partition, never the
count.


## Mutation testing in the shared worktree breaks other lanes' builds

**MUTATION TESTING IN THE SHARED WORKTREE BREAKS OTHER LANES' BUILDS, and the
failures it causes look like their bug.** Deleting a guard to check that
exactly one test dies means editing a tracked source file in place. Every
other lane compiles from that same file, so for the seconds or minutes your
mutant is on disk, their build sees it.

Measured 2026-08-20: verifying a `MAX_UNARY_TERMS` budget by `sed`-ing the
constant to `4096` and then `2` made a sibling lane's
`cargo test --features full --lib reconstruct::` report **8 failures**, all in
`string_length::tests`, all complaining about "the **2** budget" while the
committed constant was `128`. That lane lost time re-running from a snapshot
before working out the failures were not theirs. Nothing in the output pointed
at another lane; a mutated constant is indistinguishable from a wrong one.

`scripts/tests/mutation_controls.py` does not have this problem, and that is
most of why it exists: it `copytree`s to a scratch root and mutates the copy.
Register a suite there instead. If you must mutate by hand, do it in
`W=$(scripts/lane-snapshot.sh HEAD)`, never in the shared checkout — and see
the `__pycache__` trap under Gotchas, which makes hand loops report the
*previous* mutant's result anyway.


## An absolute path under the main checkout edits the main checkout

**AN ABSOLUTE PATH UNDER THE MAIN CHECKOUT SILENTLY EDITS THE MAIN CHECKOUT,
EVEN FROM INSIDE A WORKTREE.** A lane working in
`.claude/worktrees/agent-<id>/` opened `CLAUDE.md` by its familiar path,
`/home/mjbommar/projects/personal/axeyum/CLAUDE.md`, and was reading — and
would have been writing — the SHARED checkout, not its own isolated copy. The
worktree's whole purpose is that its writes are isolated; an absolute path
defeats that without any error.

It is asymmetric and that is what makes it easy to miss: a shell command is
fine, because the lane's cwd IS the worktree and relative paths resolve there.
Only the absolute form escapes. The lane caught it before an edit landed in
the wrong tree, but it cost exploration turns and it would have looked, to
everyone else, like a mystery edit from nowhere.

So from a worktree, prefix absolute paths with your own worktree root, or use
relative paths from cwd. When briefing a lane, say this explicitly — "read
your reference files from your own worktree" is not enough, because the lane
believes it is doing that.


## The session scratchpad is shared by every lane in the session

**THE SESSION SCRATCHPAD IS SHARED BY EVERY LANE IN THE SESSION, and a
fixed-name file in it is a shared append point.** `/tmp/claude-1000/<project>/
<session>/scratchpad` is per SESSION, not per lane, so concurrent lanes write
into one directory. On 2026-08-18 a lane kept its snapshot path in `W.txt`
there; another lane overwrote `W.txt` with its own path, and the first lane's
next `cp` loop wrote 13 files into the second lane's `/data0` snapshot tree
before it noticed. It restored every one with `git show <sha>:<path>`, but any
UNCOMMITTED edit inside that snapshot would have been gone.

The failure is not the collision, it is that the collision was silent and
compounded: a wrong path in a variable turns an ordinary `cp` into a write
into someone else's checkout. Name scratchpad files per lane
(`$AXEYUM_AGENT.W`, not `W.txt`) — the repository's own rule about per-lane
state in per-lane paths applies here too, and nothing said so until it cost
something. Prefer `scripts/lane-snapshot.sh`, which already stamps its
directories with the owning lane, and prefer passing paths in a variable
within one invocation over persisting them to a file at all.


## Push cost and the push lock

**Push with `scripts/lane-push.sh`, and never start a second push.** Measured
2026-08-19: two pushes started ten minutes apart took **5,510 s and 9,876 s**,
and the second's own steps account for only ~4,900 s of that — the rest was
spent blocked on `hooks/pre-push`'s worktree flock, printing nothing. `git
push` is silent while it waits and has no timeout, so that state is
indistinguishable from a hang, and I did it to myself twice in one day. The
wrapper refuses with exit **75** when another push is running (`--force`
overrides), and prints what the push will COST before starting: the hook exits
immediately when no `*.rs`/`*.toml` changed in the range, and otherwise runs a
battery measured at **545 s uncontended** — with single steps reaching 2,699 s
under lane contention. Batching commits makes that early exit fire less often,
not more: one Rust file in a range of twenty commits buys the whole battery.

## Heavy cargo: the serialization wrapper and its memory ceiling

**Heavy cargo goes through `scripts/cargo-serialized.sh <cargo args…>`.** Two
dev boxes (s1, s4) have been taken down by concurrent lane builds, and on
2026-08-17 a kernel OOM killed a live agent session — one test reached 125 GB,
because `recv_timeout` on a detached thread bounds *time*, not memory. Every
lane was told in prose to serialize; prose does not hold a lock. The wrapper
takes an `flock` on a host-local file (one cargo at a time on this host) and
runs the job in a `systemd-run --user --scope` carrying **both** `MemoryMax`
and `MemorySwapMax`, so the ceiling kills the JOB instead of leaving the host's
OOM killer to pick — and it has picked the agent.

**`MemoryMax` alone does not bite, and I nearly documented that it does.**
Measured here: `MemoryMax=64M` *is* applied (`memory.max` reads `67108864`
inside the scope's cgroup) and a 400 MB allocation still succeeds, because
`memory.swap.max` is `max` and the cgroup just swaps — on a box with 7 G of
swap already 6 G full, so the runaway thrashes and takes the host down anyway.
Adding `MemorySwapMax=0` turns the same allocation into status **137**, a
SIGKILL from the cgroup's own OOM killer, host untouched. A ceiling without a
swap ceiling is decoration.

So the wrapper carries its own probe: `scripts/cargo-serialized.sh --self-check`
over-allocates through the same lock and the same scope construction and fails
if it survives. It discriminates — `AXEYUM_CARGO_SWAP=1G` flips it to
`NOT-ENFORCED|status=0|out=SURVIVED`, exit 1. **Run it per host**: swap and
cgroup delegation differ, so a wrapper that caps s4 says nothing about s5.
Exit **75** means the lock timed out, deliberately distinct from a test
failure; the job's own status passes through otherwise (verified 0, 101, 75).
`AXEYUM_CARGO_MEM` / `AXEYUM_CARGO_SWAP` / `AXEYUM_CARGO_WAIT` /
`AXEYUM_CARGO_CPUS` tune it. Snapshot builds should set `AXEYUM_CARGO_LOCK` to
a per-tree path so a long cold build does not starve the shared worktree.
