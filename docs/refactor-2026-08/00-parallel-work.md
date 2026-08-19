# 00 — Parallel work: who owns what, and what that changes

Both strands were written as if one party would execute them. That is not the
situation. This document records the measured ownership picture and the
re-ordering it forces, and **both strands defer to it**:
[engineering](README.md) · [mathematics](../mathematics-2026-08/README.md).

## The other lane, measured

A second session — driven by the codex CLI, and **not reachable from this one**
— has been working continuously in this checkout. Measured 2026-08-14 over its
`feat(lean)` / `docs(plan)` commits:

| its territory | touches in 24h |
|---|---:|
| `PLAN.md` | 67 |
| `docs/research/09-decisions/README.md` (the ADR index) | 60 |
| `crates/axeyum-lean-kernel/src/nat_prelude.rs` + its tests | 49 each |
| `docs/plan/lean-kernel-requirements-2026-08-13.md` | 12 |
| `crates/axeyum-lean-kernel/tests/rado_sharp_factorization.rs` | 9 |
| `crates/axeyum-lean-kernel/src/{prelude,lib,tc,env,lean_pp,int_prelude,arith_prelude,string_prelude,lean_export}.rs` | 1–5 each |
| new ADRs `adr-0387` … `adr-0452` | ~65, roughly one per theorem |

**69 commits in 24 hours.** It effectively owns all of
`crates/axeyum-lean-kernel/`, and reaches occasionally into `axeyum-solver`'s
reconstruction files.

## The partition

### Uncontested — no touch by that lane, safe to work now

| area | strand item |
|---|---|
| `axeyum-cas/` and `axeyum-solver/src/nra_real_root.rs` | eng `02` W2 (one real-algebra engine); math `01` (widen the certifying path) |
| `axeyum-search/src/colouring.rs`, `axeyum-cnf/src/colouring.rs` | eng `02` W3 (one encoder, and the parity gate its comment promises) |
| `axeyum-scenarios/` | eng `01` K2 (UNSAT evidence route for `Int`/`Real`) |
| `axeyum-solver/src/nra.rs` and the rewrite passes | eng `01` K3 (integer bound strictness, product abstraction) |
| `axeyum-solver/src/capabilities.rs` | math `01` (generate the capability table instead of hand-maintaining it) |
| `docs/curriculum/` | eng `01` K5, math `04` (re-derive `covered` from evidence) |
| `docs/internals/architecture.md` | eng `04` T3 (11 of 23 crates documented) |
| `scripts/` | eng `04` G2 (clippy exiting 0 over a cached warning) — **DONE**, `check-clippy-complete.sh` in both gates |

### Contested — do not start

**All of `crates/axeyum-lean-kernel/`.** This includes the item both strands
named as the keystone: **constructing ℤ from proved ℕ**. `int_prelude.rs`
cannot be built without `nat_prelude.rs`, which that lane rewrites every few
minutes.

**That is the right outcome, not a compromise.** Its recent commits are
extended-Euclidean and Bézout certificates, gcd's universal property, and
divisibility bridged through executable remainder. **It is already building
toward ℤ.** Contesting the file would slow the very thing the strands identify
as the keystone.

Also contested for the same reason: the two `nat_prelude.rs` hazards recorded in
math `02` — the `:8090` `.expect(...)` panic and the O(n³) bubble sort in
`prove_left_sum_permutation`. Both are real; neither is ours to fix.

### Shared append points — FIXED 2026-08-14 (lane `append-points`)

`PLAN.md` and `docs/research/09-decisions/README.md` were clobbered by
concurrent lanes **four times on 2026-08-14**. Pathspec discipline does not
help: it stops you sweeping files you did not touch, not two lanes legitimately
touching the same one. The session protocol *instructed* every lane to edit
`PLAN.md`, so the instruction was the defect.

Both are now **generated views over per-lane sources**, so there is nothing left
to clobber:

- `PLAN.md` ← `docs/plan/status/<lane>.md` (one file per lane; lane blocks and
  landed-changes rows merged deterministically) + `docs/plan/global/*.md` (the
  project-wide sections, still hand-authored and deliberately so).
  `python3 scripts/gen-plan.py`, gated by `--check`.
- the ADR index ← each `adr-*.md`'s own front matter (`Index-summary:` /
  `Index-status:` carry the curated row text that previously existed only in
  the index) + `README-preamble.md`. `python3 scripts/gen-adr-index.py`, gated
  by `--check`.

Both gates run in `scripts/check.sh` and `just check` (`generated-trackers`).
Writing an ADR or a lane status update while another lane is live is now safe.

- **tag every commit with an `Agent:` trailer.** Every commit in this checkout
  carries the same git author, so `git log` attribution is otherwise
  unrecoverable — two lanes and this session all misattributed commits on the
  same day. Identity is `export AXEYUM_AGENT=<lane>` in your environment,
  per-process: the first version of the hook read a repo-local git config key,
  which was a third shared append point of exactly the same shape (one lane set
  it and the next lane's commits were stamped with the wrong name).

Note the slope that made this urgent: the ADR index was growing at **~65 per
day** against a 455 baseline. A generated index does not care. (Measured
2026-08-19: `rows=523`. The slope held.)

**The file stopped colliding; the NUMBERS did not.** Three ADR-number collisions
across checkouts in two days, each renumber moving the collision rather than
escaping it, because the renumbering side took the local maximum — the same
number the other checkout had taken. `--check-remote` catches this **pre-merge
only** and is structurally blind afterwards; `--check` catches the post-merge
case and, until `f63b94191`, printed the duplicates and exited 0. Before
allocating a number, read
`git ls-tree -r --name-only origin/main docs/research/09-decisions/`. Do not take
the local maximum. The structural fix (non-sequential allocation) is unbuilt —
eng [`04`](04-gates-and-truth.md) T5.

### The append-point fix did not generalise — three new incident classes (2026-08-18/19)

The section above fixed *files* two lanes both write. Three further collisions
happened after it, none of which it addresses, and **each defeated the remedy
CLAUDE.md recommends at the time**. Recorded here because prose did not prevent
them and the mechanisms are not guessable.

**1. The staged-set assertion cannot catch a WRONG pathspec.** CLAUDE.md's

```
test -z "$(git diff --cached --name-only HEAD | grep -vxF "$PATHSPEC")"
```

compares the staged set *against the pathspec*, so it catches `HEAD` moving under
you mid-commit — a real hazard, the tenth incident — and cannot catch a pathspec
that does not describe your change. Both directions then happened in one session,
to one agent:

- **too narrow.** The pathspec was derived from `git status --porcelain
  --untracked-files=no` after a `git mv`. Renamed-*to* files are untracked in a
  freshly `read-tree`'d private index, so they were omitted: the commit landed
  **four ADR deletions with none of the additions**, and four decisions were
  briefly absent from history while every reference in the tree pointed at them.
- **too wide.** The remedy — `--untracked-files=all` — enumerates *other lanes'*
  untracked files in a shared checkout. The next commit swept a sibling lane's
  new example and another's pinned output file.

Both commits passed the assertion. Use **`scripts/lane-commit.sh -m <msgfile> --
<path>...`**, which takes the paths explicitly and refuses on any of: something
staged you did not name, something named that failed to stage (the half-rename
guard), or a named path that is clean relative to `HEAD` (a sign your list is
stale). A rename must name **both** sides — naming only the destination is
incident 1 and naming only the source deletes your own file.

**2. Killing `git push` does not kill the hook.** `hooks/pre-push` gates a stable
per-lane worktree under an flock, and the hook survives the death of the `git
push` that started it: an orphaned one kept running long after, executing a step
that had since been deleted, and **held the flock so the next push sat silent**.
`git push` prints nothing while it blocks and has no timeout, so that is
indistinguishable from a hang. Two pushes started ten minutes apart took
**5,510 s and 9,876 s**, of which roughly 4,900 s of the second was spent waiting
to begin.

Use **`scripts/lane-push.sh`**. It computes the hook's own decision from the diff
and prints the cost *before* starting, and refuses with exit **75** when another
push is running (distinguishable from a rejected push; `--force` overrides). Its
concurrency probe reads `/proc/*/comm` rather than `pgrep -f`, because a `pgrep
-f` pattern matches the wrapper's own command line and killed the wrong process
here. **`git push --dry-run` also runs the hook** — one started as a test fixture
ran the full battery for 46 minutes and blocked a real push throughout;
`lane-push.sh --dry-run` never invokes `git push` at all.

**3. The session scratchpad is shared by every lane.**
`/tmp/claude-1000/<project>/<session>/scratchpad` is per **session**, not per
lane. One lane kept its snapshot path in `W.txt` there; another overwrote `W.txt`
with its own path, and the first lane's next `cp` loop wrote 13 files **into the
second lane's `/data0` snapshot tree**. Committed content was recoverable with
`git show <sha>:<path>`; an uncommitted edit inside that snapshot would not have
been.

The collision is not the interesting part — the silence is. A wrong path in a
variable turns an ordinary `cp` into a write into another lane's checkout, and
neither `git status` nor any gate can see it, because it happens outside the
repository. Name scratch files `$AXEYUM_AGENT.<something>`, prefer passing the
path in a variable inside one invocation over persisting it, and prefer
`scripts/lane-snapshot.sh`, which stamps its directories with the owner.

**The generalisation, and it is the same one three levels down:** per-lane state
belongs in a per-lane path or a per-process environment variable. That is why
`PLAN.md` was split, why lane identity is `$AXEYUM_AGENT` and not a git config
key, why the private index must be per-lane — and now why a scratchpad filename
must be too.

## What this changes in the ordering

Both strands said "the keystone first". **We cannot do the keystone.** So the
work re-orders into *what the keystone will need the moment it lands*:

1. **`axeyum-scenarios` Int/Real evidence route** (eng `01` K2). The single
   highest-value uncontested item. When ℤ lands, results about it still cannot
   carry a negative control until this exists — today the crate
   `unreachable!()`s on `Sort::Int` and `Sort::Real`. Build the receiver while
   the other lane builds the thing.
2. **Integer bound strictness + product abstraction** (eng `01` K3). Measured
   as `unknown`-at-20s → 0 ms on both bounding steps of the `k=3` critical leaf.
   Independent of the library.
3. **Gates: G2 and the architecture doc** (eng `04`). Cheap, uncontested, and a
   precondition for anything that moves files. **G2 landed** — but the gate work
   did not shrink, it grew: five further gate-scope holes were found on
   2026-08-18/19 (eng `04` G4–G8), two of them in the aggregate gates themselves.
   Three items there are still open and are listed at the end of this file.
4. **One real-algebra engine, one colouring encoder** (eng `02` W2/W3). Pure
   duplication removal in files nobody else is in.
5. **Curriculum `covered` flags re-derived from evidence** (math `04`, eng `01`
   K5). Cheap, and it stops the routing table asserting coverage of sorts that
   cannot carry evidence.

**Deferred while that lane is live**, beyond the contested crate:

- **eng `02` W1 (kernel reuse).** It touches `axeyum-lean-kernel/src/{env,lib}.rs`
  *and* six `axeyum-solver` reconstruction call sites the lane also edits. The
  measurement stands (26 ms vs 6.6 µs, ~4,000×, on a library that grew 2.6× in
  one session) and it gets *more* valuable as the library grows — but it is the
  worst possible file set to contest.
- **eng `03` (solver decomposition).** Already sequenced last; this is a second
  reason. Moving files that another lane edits occasionally is how a merge goes
  wrong quietly.

## Re-check before starting

This picture is a snapshot. Before taking any item:

```
git status --short                       # who is holding what right now
git log --since="2 hours ago" --name-only --format=""  | sort | uniq -c | sort -rn
```

And before writing anything back:

```
export AXEYUM_AGENT=<lane>
scripts/lane-commit.sh --dry-run -- <path>...   # check the set, commit nothing
scripts/lane-commit.sh -m <msgfile> -- <path>...
scripts/lane-push.sh --dry-run                  # what the hook will cost, without running it
```

If the other lane has gone quiet, the contested set collapses and the keystone
becomes available — at which point the ordering above reverts to the one in each
strand's README.

## Using the other hosts — a verified recipe, because three lanes got this wrong

`s0 s1 s4 s5 s6 s7` are reachable over ssh and all mount `/nas3/data/axeyum`
(NFS, ~15 TB). `s0` is this box. Verify before concluding otherwise:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=8 s5 'hostname; nproc; free -g | awk "NR==2{print \$7\" GB free\"}"'
```

Long work belongs in a **memory-bounded transient unit**, not `nohup`:

```sh
ssh s5 "systemd-run --user --unit=<name> \
  -p MemoryHigh=18G -p MemoryMax=22G \
  -p StandardOutput=append:/nas3/data/axeyum/<dir>/<log> \
  -p StandardError=append:/nas3/data/axeyum/<dir>/<log> \
  -p WorkingDirectory=/tmp <binary> <args>"
ssh s5 'systemctl --user is-active <name>'
```

`loginctl enable-linger` is set on s4 and s5, so such a unit survives ssh
disconnect **and** the death of whatever started it. That matters: `systemd-oomd`
killed this box's entire session cgroup on 2026-08-14 (68.36% pressure for >20 s,
27 processes, 83.6 GB peak), taking a 2¼-hour solve and two watchers with it.
It kills by **cgroup**, so `nohup` does not help and bystanders die with the
cause. A binary staged to `/nas3/data/axeyum/bin/` runs on any of them.

**Three lanes in one day concluded a resource was unavailable without checking:**
one ran `which lean`, got nothing, and reported no toolchain — Lean 4.30.0 was
installed under `~/.elan/toolchains/`, merely off `PATH`, and seven test suites
had been printing `ok` while checking nothing. One reported `/data0` as the
scratch disk without noticing it is root-owned and unwritable. One reported
`server0` as "the only machine available" while `ssh s5` worked. The shape is
always the same: a plausible probe returned empty, and empty was read as a fact
about the world. Confirm the probe covered the subject before believing its
zero.

## What is open in the gate strand (2026-08-19)

Three items, all measured, none of them blocked by the other lane. Full detail in
[`04-gates-and-truth.md`](04-gates-and-truth.md).

1. **`check-aggregate-scope` is red on 32 steps** that `main` ships and that are
   recorded as accepted in neither gate (`check.sh` 203 steps, `just check` 278,
   97 one-sided). It is now at the tail of the chain so it no longer hides
   anything, but it still fails. **The fix is to wire those 32 into both gates,
   not to re-pin `scripts/check-aggregate-scope.expected`** — re-pinning turns a
   ratchet into a rubber stamp.
2. **ADR numbers have no structural fix.** Three collisions in two days; both
   detectors are live and neither subsumes the other. Non-sequential allocation
   is the actual answer and is unbuilt. Until then, allocate from
   `git ls-tree -r --name-only origin/main docs/research/09-decisions/`, never
   from the local maximum.
3. **No `axeyum-lean-kernel` suite is registered with the mutation harness.**
   Six suites are registered as of 2026-08-19 — five Python
   (`adr-index`, `plan`, `fact-derived-numbers`, `lean-axiom-ledger`,
   `lra-hypothesis-binding`) and one Rust (`fp-width-guard`). The crate carrying
   the trusted proof surface has its guards asserted rather than
   mutation-checked, which is the crate where the rule matters most.

A fourth, found while writing this: the `local-ci` record that
`check-local-ci-freshness.sh` enforces has **five** steps, and `local-ci.sh` has
had a **sixth** (the frontier ratchet) since `69f2cffb8` the same morning. The
gate reports `PASS -- fresh, ancestor, all-pass` over a run in which that step did
not exist. Freshness of a record is not coverage by it.
