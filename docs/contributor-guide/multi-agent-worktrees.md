# Multi-Agent Worktrees

This note records the operating model for multiple agents or humans working on
Axeyum at the same time.

The short version: use separate git worktrees, use separate topic branches, and
keep one integration owner for `main`.

## Why

Axeyum has a few high-conflict files:

- `Cargo.toml`
- solver core files such as `crates/axeyum-solver/src/incremental.rs`
- broad planning docs under `docs/plan/` and `docs/research/08-planning/`

`PLAN.md` and the ADR index `docs/research/09-decisions/README.md` used to head
that list — 67 and 60 touches in 24 hours by concurrent lanes on 2026-08-13/14,
four clobbering incidents in one day. They are no longer shared files: both are
**generated views** over per-lane sources (`docs/plan/status/<lane>.md` and the
`adr-*.md` files themselves), and `scripts/gen-plan.py --check` /
`scripts/gen-adr-index.py --check` fail if either is hand-edited. That is the
pattern to reach for when a file becomes a queue: **give each writer its own
path and derive the shared view.** The same rule applies to identity — lane
identity is the per-process `AXEYUM_AGENT`, not a repo-local config key, because
a shared config key is the same defect in a smaller file.

Two agents editing the same checkout or both pushing directly to `main` can
silently overwrite context, duplicate work, or force noisy conflict resolution
in exactly the files that carry session state. Worktrees keep filesystem state
separate while still sharing one local object database.

## Recommended Layout

Keep one checkout as the integration lane and create one worktree per agent or
task:

```text
axeyum/                    # integration checkout; main owner works here
axeyum-codex-rules/         # topic worktree for a docs/rules task
axeyum-agent-solver/        # topic worktree for solver work
axeyum-agent-bench/         # topic worktree for benchmark work
```

Create worktrees from the same up-to-date base:

```sh
git fetch origin
git worktree add ../axeyum-codex-rules -b agent/codex/rules-docs origin/main
git worktree add ../axeyum-agent-solver -b agent/solver/warm-arrays origin/main
```

Use descriptive branch names:

```text
agent/codex/rules-docs
agent/solver/warm-arrays
agent/bench/qf-lia-scoreboard
agent/docs/proof-cookbook
```

## Roles

Use a simple hub-and-spoke workflow:

- **Integration owner:** owns `main`, resolves final conflicts, and decides merge
  order.
- **Topic agent:** works in its own worktree and branch, keeps changes small,
  pushes frequently, and does not edit unrelated files.
- **Reviewer / verifier:** can pull a topic branch into a separate worktree and
  run gates without disturbing either the topic agent or the integration lane.

If the team explicitly wants direct-to-`main` commits for a short stretch, make
that a named exception and coordinate file ownership before work starts.

## Daily Protocol

At the start of a task:

```sh
git fetch origin
git status --short --branch
git log --oneline --decorate -5
```

If you are on a topic branch:

```sh
git rebase origin/main
```

Before committing:

```sh
cargo fmt --all --check
git diff --check
# plus focused tests for the touched area
```

Before pushing a topic branch:

```sh
git status --short --branch
git push -u origin HEAD
```

Before merging to `main`:

```sh
git fetch origin
git rebase origin/main
# rerun focused gates after the rebase
git push --force-with-lease
```

The integration owner should merge or fast-forward in a clean integration
checkout, then run the relevant top-level gate before pushing `main`.

## File Ownership

Coordinate ownership before touching high-conflict files.

Good examples:

- "Agent A owns `crates/axeyum-solver/src/incremental.rs` for this slice."
- "Agent B owns `docs/rules-as-code/` and will leave root planning state to the
  integration owner."
- "Every lane updates its own `docs/plan/status/<lane>.md` and regenerates
  `PLAN.md`; the integration owner owns `docs/plan/global/`."

Root `STATUS.md` is a compatibility pointer, not mutable session state. Do not
add lane sections to it. `PLAN.md` is the single mutable project tracker, and it
is **generated**: edit your lane's file under
[`docs/plan/status/`](../plan/status/README.md), run
`python3 scripts/gen-plan.py`, and commit both. The project-wide sections in
[`docs/plan/global/`](../plan/global/README.md) stay hand-authored and are
changed deliberately, not once per session per lane.

In your lane's file, prefer stable links and short index updates. Detailed
session evidence and design belong under `docs/plan/` or another owned
documentation path, with one deterministic handoff when work pauses.

## Push Policy

Do not push a shared branch if it is already ahead of `origin` with commits you
did not create unless the integration owner has said that is expected.

Check first:

```sh
git log --oneline origin/main..HEAD
git rev-list --left-right --count main...origin/main
```

If the current branch contains someone else's unpushed commits, either:

- ask the integration owner to push or merge them;
- move your work to a topic branch/worktree; or
- commit locally and clearly report that pushing would also publish the existing
  unpushed commits.

Use `--force-with-lease` only for topic branches that you own. Never force-push
`main`.

## Conflict Handling

When conflicts happen, preserve the newer intent instead of mechanically taking
one side.

Recommended sequence:

```sh
git fetch origin
git rebase origin/main
# resolve conflicts
cargo fmt --all --check
git diff --check
# rerun focused tests
git push --force-with-lease
```

For planning-doc conflicts, do not duplicate entries. Merge them into one
chronological note with the final current state.

For code conflicts, rerun the smallest focused test that proves the merged
behavior and then the broader gate appropriate to the touched crate.

## When To Split Repositories

Worktrees solve same-repo coordination. They do not decide project boundaries.

Keep work inside the Axeyum repo while it is tightly coupled to solver
semantics, proof routes, benchmarks, documentation, or CI. Split into a separate
repository only when the sibling has an independent release cycle, heavy
dependencies, a large corpus, or a standalone user audience.

Examples that should incubate inside Axeyum first:

- `docs/atlas/`
- `docs/proof-cookbook/`
- `docs/rules-as-code/`
- `artifacts/ontology/`

Examples that may deserve separate repositories later:

- an Axeyum visualizer web app;
- an EVM or WASM verification frontend;
- a large law/policy corpus;
- a public course site.

## Cleanup

List worktrees:

```sh
git worktree list
```

Remove a completed worktree after its branch is merged:

```sh
git worktree remove ../axeyum-codex-rules
git branch -d agent/codex/rules-docs
```

If a worktree was deleted manually:

```sh
git worktree prune
```


## Shared-checkout index hygiene (when lanes share ONE checkout)

Learned the hard way on 2026-07-03 (a bare `git commit` swept another
agent's staged files into an unrelated commit and had to be recovered):

- **Pathspec-only commits, always**: `git add <your files>` then
  `git commit -m "..." -- <your files>`. The index is shared; a bare
  `git commit` commits *everything staged by anyone*. Verify each commit
  with `git show --stat` before moving on.
- **Never** `git stash`, `git checkout`/`git restore` on files you did not
  modify, or any history rewrite — other lanes keep uncommitted WIP in the
  tree. A dirty file you don't recognize belongs to someone else.
- **Per-file formatting only**: `rustfmt --edition 2024 <file>`. Both
  `cargo fmt` and `cargo fmt -p <crate>` reformat files other lanes have
  in flight.
- **One writer per area**: two agents editing the same crate's sources
  concurrently is a merge hazard even with pathspec discipline — partition
  by crate/module before spawning.
- **Check the index before you commit**: `scripts/check-shared-index.sh`.
  The per-process-index remedy (`GIT_INDEX_FILE` + `git read-tree HEAD`) leaves
  the SHARED index holding pre-commit blobs for the paths you just landed, which
  relative to the new `HEAD` is a staged *revert* — and a staged *deletion* for a
  file you newly added. The next bare `git commit` applies it, inside a commit
  that looks like someone else's.

  Nothing you would normally look at shows this: every affected file is
  byte-identical to `HEAD` **on disk**, so `ls`, `git show` and reading the file
  are all correct, and `git status` says `MM`, which reads as "someone is
  mid-edit". Measured 2026-08-17: six paths in that state — including 208 lines
  of a proof landed hours earlier — and zero genuinely staged edits.

  `--fix` re-adds exactly those paths, which is safe because they are already
  byte-identical to `HEAD`; it does not `read-tree`, so another lane's genuine
  staging is reported and left alone.
- If your staged set gets swept by another lane's commit: do NOT rewrite
  history; re-stage and re-commit your pathspec set on the new HEAD, then
  verify with `git show --stat`.

## Lane attribution (`hooks/commit-msg`)

Every commit in this checkout carries the **same git author**, because several
agent lanes and a human share one identity. `git log` therefore cannot answer
"who did this" — and on 2026-08-14 three separate parties misattributed commits
to the wrong lane within one day, while one lane's `PLAN.md` edit was swept into
another's commit with no way to tell afterwards.

Identify your lane once per checkout:

```sh
git config core.hooksPath hooks      # if not already set
git config axeyum.agent <lane-id>    # e.g. coordinator, lean-kernel, alice
```

`hooks/commit-msg` then stamps every commit with an `Agent:` trailer. It
**appends rather than rejects** — deliberately, because the pre-push hook's own
history records that a gate which forces `--no-verify` defeats itself. Merges,
reverts and fixups are skipped, and an existing trailer is never duplicated.

Recover attribution with:

```sh
git log --format='%h %(trailers:key=Agent,valueonly) %s'
```

## The pre-push compile gate (mechanism, not vigilance)

Every checkout should run `git config core.hooksPath hooks` once. The
committed `hooks/pre-push` refuses to push Rust/TOML changes that do not
compile (`cargo check --workspace`) or are unformatted — the exact class
that reached `main` on 2026-07-03 when a shared-index sweep published a
re-export one commit before its definition. Docs-only pushes skip the cargo
steps, so the curriculum lane's cadence is unaffected. The heavy gates
(clippy/tests/rustdoc) remain in CI and `just check`; this hook only
guarantees "main always compiles".

---

# Shared-index incident history — twelve ways a commit ate another lane's work

The rules in [CLAUDE.md](../../CLAUDE.md#multi-agent-hygiene-multiple-agents-share-this-checkout)
are the short form. This is the measured history behind each one, kept because
every rule here was written *after* an incident and several were caused by the
fix for the previous one.

The short version, if you read nothing else: **use
`scripts/lane-commit.sh -m <msgfile> -- <path>…`.** It takes the paths
explicitly and refuses unless nothing staged was unnamed, nothing named failed to
stage, and no half-rename is left behind; then it resyncs the shared index for
exactly those paths. Its controls (`scripts/tests/test-lane-commit.sh`) carry one
case per incident below, each guard mutation-verified to kill exactly one.

## Pathspec is necessary, NOT sufficient

**Pathspec is necessary, NOT sufficient — it does not protect a file two
lanes are both editing.** `git add <file>` stages that file's entire
*worktree* content, including another lane's uncommitted hunks in it. On
2026-08-14 a correctly-pathspec'd commit swept another lane's in-progress
`justfile` edit into itself: the fifth clobbering incident, and the first
where the committer followed this rule exactly. Consequences were real —
a step was attributed to the wrong lane, and `main` referenced a script
three minutes before that script existed. So: before `git add`, run
`git diff <file>` and confirm every hunk is yours. If it is not, you are
sharing a file, which is the actual problem — say so and coordinate rather
than committing around it.

## A pathspec narrower than your change drops your own hunks

**A pathspec NARROWER than your change silently drops your own hunks —
the opposite failure, and equally unguarded.** On 2026-08-14 a lane doing a
staged refactor ran `clippy -D warnings` immediately before each commit and
still shipped `ae589be97`, which **does not compile**: the gate ran against the
*worktree* while the commit used a hand-written pathspec that omitted a
one-line import fix in an already-committed file. Green gate, broken commit.
Derive the pathspec from `git status`, never by hand, and if you must hand-write
it, verify with `git stash -u && cargo check` — or simply accept that
`git show --stat` tells you what you committed, not what you needed to commit.
(That commit is still in history, repaired by the next one rather than rewritten:
**a bisect crossing `ae589be97` will report a build failure unrelated to what it
is bisecting.**)

## No form of `git commit` is safe for two lanes sharing one index

**NO FORM OF `git commit` IS SAFE FOR TWO LANES SHARING ONE INDEX — use a
per-process index.** Measured 2026-08-15, when two lanes swept each other
within twelve minutes using the two *mutually exclusive* remedies:
`git commit -- <pathspec>` reads the **worktree** and discards your staged
hunks; bare `git commit` reads the **index** and is defeated by a concurrent
`git add`. Both lose, in opposite directions. Pathspec discipline is not a fix
for this, and the rules above cannot make it one.
The remedy is the repository's own rule one level down — per-lane state in
per-process environment, the same reason lane identity is `AXEYUM_AGENT`:

    export GIT_INDEX_FILE="$PWD/.git/index-$AXEYUM_AGENT"
    git read-tree HEAD          # REFRESH FIRST, EVERY TIME
    git add <your files>
    git commit -m "…"

`git read-tree HEAD` before every stage is not optional: a stale private index
**reverts** whatever other lanes committed since you created it. Verified both
ways — without the refresh, one lane's commit shows `a.txt | 2 --` and undoes
the other's landed change; with it, both edits survive and each commit carries
only its own file. Do not use a bare `git commit` even with a private index if
you have not refreshed it.

## And then resync the shared index

**AND THEN RESYNC THE SHARED INDEX — the private-index remedy leaves a staged
revert of your own commit behind it.** This is the seventh incident and the
second one *caused by the fix*. The mechanism: you commit from a private index,
so `HEAD` advances, but the **shared** `.git/index` still holds the pre-commit
blobs for those paths. Relative to the new `HEAD` that reads as a staged
revert — and for a file you newly added, a staged **deletion**. The next lane
to run a bare `git commit` applies it, and your work disappears in a commit
that looks like someone else's.

Measured twice within one hour on 2026-08-15. One lane found a staged `−138`
revert of the golden-pin fix it had just landed, plus a staged deletion of its
new status file. The coordinator's was a staged **−430** revert across ten
files, including deleting a 130-line script that had been committed minutes
earlier. In both cases every file was byte-identical to `HEAD` **on disk** —
the content was never at risk, only the index was, which is exactly why nobody
noticed: `ls` and `git show` both look fine.

So after committing, from the shared index:

    unset GIT_INDEX_FILE
    git add -- <the paths you just committed>   # worktree == HEAD, so this is
                                                # a content no-op; it only
                                                # clears the staged revert
    git diff --cached --stat HEAD               # MUST be empty

Do **not** `git read-tree HEAD` the shared index to fix this: another lane may
have legitimately staged work there, and you would drop their staging. Resync
only your own paths, and only after confirming the worktree content matches
`HEAD` for each.

**`git diff HEAD -- <path>` is the WRONG test for a file you newly added**, and
it fails in the direction that loses work. A new file has no entry in the
shared index, so `git diff HEAD` reports it as a *deletion* — the check says
"differs", you decline to restage, and the staged deletion of your own new
file is exactly what stays behind for the next lane to commit. Two lanes hit
this on 2026-08-18, one of them nearly leaving a staged −525-line deletion of
two files it had just added. Compare the objects instead, which is defined for
a path the index has never seen:

    for f in <paths>; do
      [ "$(git hash-object "$f")" = "$(git rev-parse "HEAD:$f")" ] \
        || echo "DIFFERS: $f"
    done

## `read-tree` and `commit` must be the same shell invocation

**`read-tree` AND `commit` MUST BE THE SAME SHELL INVOCATION — a refresh in an
earlier command is already stale.** Eighth and ninth incidents, 2026-08-17,
both by agents that had read the rule above and believed they were following
it. `agent-reals-design` deleted 1,623 lines of `rat_prelude`; an hour later
`agent-characterization` deleted 1,514 lines of the same file the same way.
Each repaired it, but only after the fact.

The mechanism is that "refresh first" reads as setup rather than as part of
the commit. Between one Bash call running `git read-tree HEAD` and a later one
running `git commit`, **another lane commits and HEAD moves**; the private
index still holds the old blobs, so committing writes them back and reverts
the other lane. Nothing in the diff you were looking at hints at it.

    # WRONG -- two invocations, HEAD can move between them
    git read-tree HEAD
    … think, edit, run a test …
    git add -- a.rs && git commit -m "…"

    # RIGHT -- one invocation, nothing between
    git read-tree HEAD && git add -- a.rs && git commit -m "…"

Two checks catch it, and the obvious one does not. `git diff --cached --stat`
compares against the index's own stale base and looks clean; **`git diff
--cached --stat HEAD` is the one that fires.** And after committing, read the
FILE COUNT in `git show --stat`, not whether your own hunks look right: the
only symptom in the second incident was 15 files where 11 were staged.

**One invocation is still not enough — VERIFY THE STAGED SET.** Tenth incident,
2026-08-18, by a lane that did put `read-tree`, `add` and `commit` in a single
Bash call: another lane committed during the `git add`, and the commit reverted
six of its files (−302 lines). The window is real work, not a race you can win
by typing faster. Amended within a minute, nothing lost, but the rule above
does not prevent it.

So do not trust the sequence — assert the outcome. The staged set must equal
your pathspec, checked between `add` and `commit` in the same invocation:

    P="a.rs b.rs"
    git read-tree HEAD && git add -- $P && \
      test -z "$(git diff --cached --name-only HEAD | grep -vxF "$(printf '%s\n' $P)")" && \
      git commit -F - <<'MSG'
    …
    MSG

If that `test` fails, HEAD moved: re-run `read-tree`/`add` and check again. The
diff-against-HEAD is what sees it; the index's own base cannot.

## `git commit -m "…"` silently deletes anything in backticks

**`git commit -m "…"` SILENTLY DELETES anything in backticks.** Double quotes
mean the shell runs each backtick span as a command and substitutes its output,
which for prose is almost always empty. This repository's commit messages are
full of backticked identifiers by convention, so the trap is universal here:
one message lost `` `--` ``, an entire example command line, and `` `add_neg` ``,
leaving sentences like "cargo swallows a flag when the command has no
separator". The commit is fine; the explanation of it is gone, and `git log`
gives no hint that anything was removed. Use a quoted heredoc — which cannot
substitute anything — and the message survives verbatim:

    git commit -F - -- <paths> <<'MSG'
    subject line

    body with `backticks` and $vars intact
    MSG

`git commit -m 'single quotes'` also works, but only until the message needs an
apostrophe.

## The staged-set assertion cannot catch a wrong pathspec

**THE STAGED-SET ASSERTION CANNOT CATCH A WRONG PATHSPEC — check it BOTH
ways, or use `scripts/lane-commit.sh`.** Eleventh and twelfth incidents,
2026-08-18, by the same agent within an hour, in opposite directions, both
passing the assertion above.

*Too narrow.* A pathspec derived from `git status --porcelain
--untracked-files=no` after a `git mv`: the renamed-TO files are untracked in a
freshly `read-tree`'d private index, so they were omitted. The commit landed
four ADR **deletions with none of the additions** — 705 lines removed, 243
added — and four decisions were absent from history while every reference in
the tree pointed at them.

*Too wide.* The remedy was `--untracked-files=all`, which in a shared checkout
enumerates **other lanes' untracked files**. The next commit swept a sibling
lane's new example and another's pinned output file.

Both passed `test -z "$(git diff --cached --name-only HEAD | grep -vxF …)"`,
because that compares the staged set against the pathspec and **both times the
pathspec itself was wrong**. It catches HEAD moving under you mid-commit, which
is a real hazard and a different one. Note also that with rename detection on,
`--name-only` prints only a rename's DESTINATION, so a pathspec that correctly
names both sides is reported as half-unstaged — use `--no-renames`.

`scripts/lane-commit.sh -m <msgfile> -- <path>…` takes the paths explicitly and
refuses unless: nothing staged that you did not name, nothing named that failed
to stage, and no path in `HEAD` gone from disk with its deletion unstaged in a
directory you are committing into (the half-rename). It then resyncs the shared
index for exactly those paths, using `git hash-object` against `git rev-parse
HEAD:<path>` rather than `git diff HEAD`, and `git reset HEAD -- <path>` for
anything another lane moved under you. Controls:
`scripts/tests/test-lane-commit.sh`, one case per incident above; each guard
mutation-verified to kill exactly one.

The guard that catches the *wide* case is unreachable when every named path is
an explicit file — `git add -A -- <file>` cannot stage anything else. It fires
on a pathspec naming a **directory**, which is what actually happened. A suite
without that case would let the guard be deleted while staying green.

## A merge cannot use a private index — use a detached worktree

**A MERGE CANNOT USE A PRIVATE INDEX, SO ANOTHER LANE'S STAGED FILE BLOCKS
YOURS — USE A DETACHED WORKTREE.** The `GIT_INDEX_FILE` remedy above covers
*commits*. A merge has to write the index, and git refuses when the shared one
holds a staged path the merge would touch:

    error: Your local changes to the following files would be overwritten by merge:
      docs/plan/status/117-parity-freshness.md
    Merge with strategy ort failed.

Measured 2026-08-21. That file was another lane's, staged and uncommitted, and
**no incoming commit touched it** — git is conservative about any staged path.
Unstaging it is exactly the "you would drop their staging" mistake this section
already warns against, and `git stash` is worse (it corrupted a file the same
day: the pop conflicted and wrote `<<<<<<<` markers into a source file while
`git status` still showed the expected shape).

The way through is an index that is genuinely yours:

    W=/data0/axeyum/scratch/wt-$AXEYUM_AGENT-push
    git worktree add --detach "$W" HEAD
    cd "$W" && git merge --no-edit origin/main && scripts/lane-push.sh --to main
    cd - && git worktree remove --force "$W"

A worktree has its own index and its own `HEAD`, so the merge, the regeneration
and the push all happen without touching the shared checkout. Verify afterwards
that their entry survived — `git ls-files -s <path>` should print the same blob
hash it did before you started.


## An ADR number is a shared allocation point

**AN ADR NUMBER IS A SHARED ALLOCATION POINT, AND GENERATING THE INDEX DID NOT
FIX IT.** `docs/research/09-decisions/README.md` is generated precisely so
concurrent lanes stop conflicting on it — but the NUMBER in the filename is
still one key every lane writes, chosen by looking at the tree. Two lanes that
start within an hour of each other read the same maximum and pick the same
next number.

Measured 2026-08-30, twice in a row: `queue-refill` and `holdout-amendment`
both wrote **0617**; after the first was renumbered to 0618,
`mobility-census` had independently written **0618** as well. Each collision
costs a `git mv`, a sweep of inbound references, and an index regeneration —
and the second one was caused by the fix for the first.

Nothing surfaces it at merge time. The two files have different names, so git
merges them cleanly and `git show --stat` looks ordinary.
`scripts/gen-adr-index.py --check` DOES fail on a duplicate outside its
grandfathered `{0166, 0167}` set (verified: injecting a duplicate makes it
exit 1), and it is wired into both aggregate gates — the gate is not the
problem. The problem is that merges happen far more often than the ~10-minute
gate runs.

So: **when briefing a lane, name a specific number well above the current
maximum**, and tell it to check the tree first. When merging, run
`scripts/check-merge-hygiene.sh` (~2s) — it runs `gen-adr-index.py --check`
plus a conflict-marker scan and a generated-file freshness check, each of the
three being a defect that reached a commit through this same gap.


## Two lanes can each bump a pinned count correctly and still not compile

**TWO LANES CAN EACH BUMP A PINNED COUNT CORRECTLY AND THE MERGE STILL WILL
NOT COMPILE.** The standing rule — "recompute by COUNTING the list, never by
adding to the old number" — is written for the LANE, and it works: measured
2026-08-25, both the chain-rule lane and the series lane landed one
declaration each and both correctly took `creal_tests.rs`'s pin from 199 to
200 against their own bases.

Git then merged both array ENTRIES cleanly, because they are different lines,
and left the DECLARED size at 200 with 201 entries:

    error[E0308]: mismatched types
    let expected: [(&str, crate::NameId, &str); 200] = [ ... ]

The case the rule does not cover is the COORDINATOR merging two correct
increments. So recount after every merge that touches a pinned list, not only
after a conflicted one — this merge had **zero conflicts**. It happened eight
times in one day across `creal_tests.rs` and `nat_prelude_tests.rs`.

`hooks/pre-push` refuses the push, so it does not reach `main`; the cost is a
wasted push attempt, which on this repository is several minutes of battery.

**AND "COUNT THE LIST" IS ITSELF EASY TO GET WRONG, BECAUSE ENTRIES ARE NOT
ONE PER LINE.** rustfmt wraps any entry whose name is long across five lines,
beginning with a bare `(` on its own line, so the obvious count -- lines
matching `("` -- silently undercounts. Measured 2026-08-26 while resolving a
pin conflict in `creal_tests.rs`: **210 such lines against a true 283**, and
the wrong number was written into the file before the gap was noticed. An
entry starts at either `^        \("` or `^        \($`, and only those two.

Do not hand-roll it. `scripts/recount-pinned-inventory.py <file>` rewrites the
pin to the counted value and exits nonzero when it moved; `--check` reports
without rewriting. Controls: `scripts/tests/test-recount-pinned-inventory.sh`,
each guard mutation-verified to be killed by the case that names it.

**CURRENT STATE (2026-08-27): `creal_tests.rs` no longer has this pin at
all.** Everything above is the incident history that motivated the fix, kept
because the failure mode it describes is general (it will recur in
`nat_prelude_tests.rs` or anywhere else this array shape is used) — but the
432-entry single array is gone from `creal_tests.rs` specifically. It was
the thing making EVERY pair of concurrent `creal` lanes collide (any two
declarations anywhere in `creal/` touched the same one file), so it was
sharded into one plain `Vec` per `creal/` source module under
`crates/axeyum-lean-kernel/src/creal/inventory/` (plus `base.rs` for the
algebra declared directly in `creal.rs`), registered from
`crates/axeyum-lean-kernel/src/creal/inventory.rs`. A lane adding a
declaration to an existing `creal/` module now edits exactly one file —
that module's shard — never the array every other `creal` lane also edits.

No shard carries a pinned length, and none should be added: the length pin
answered "is this list internally consistent", never "is it complete", and
`creal_tests::every_creal_declaration_is_checked_and_axiom_free` already
answers the question that matters — coverage read from
`kernel.environment()` directly, both directions (an environment
declaration missing from every shard, and a shard entry naming a
declaration no longer in the environment) — plus a check new to the
sharded shape: no declaration may be claimed by more than one shard. A
single array could never have that failure mode; many files can, if two
lanes both add an entry for the same declaration. `scripts/
recount-pinned-inventory.py` is unchanged and still applies verbatim to any
`*_tests.rs` that keeps this pin shape (`nat_prelude_tests.rs` and
`complex_tests.rs` do not use it today — see their own `theorem_names`/
`named` helpers — so nothing else needed updating for this).


## Two lanes adding functions to one Rust file

**TWO LANES ADDING FUNCTIONS TO ONE RUST FILE PRODUCE A CONFLICT WHERE
"KEEP BOTH SIDES" SILENTLY DOES NOT PARSE.** The conflict looks purely
additive — no line is changed by both — so concatenating the sides is the
obvious resolution and it is wrong. Git's hunk boundaries cut **mid-item**:
each side ends with a dangling

    pub(super) fn declare_something(

whose parameter list is the shared context *after* the hunk, because that
boilerplate is byte-identical on both sides and the differ aligns on it.
Measured 2026-08-25 in `nat_prelude/finite_set.rs` — three `mismatched
closing delimiter` errors — and again in `nat_prelude_tests.rs` with two
`#[test] fn` bodies. **`-X patience` does not fix the alignment.** Reordering
the sides does not either: there is one shared tail and two dangling
signatures.

The tell is **delimiter balance per hunk side**, and it must count parens and
brackets, not just braces — the real failure dangled an open paren.
`scripts/lane-merge-additive.py check <file>` reports it and exits 1;
`… splice <file> --theirs <ref> --anchor <text>` reconstructs instead, lifting
whole items out of the other branch's own file by brace matching. It strips
line comments first, because this repository's doc comments are full of
`[0,n)` and [`Self::foo`] links that are deliberately unbalanced.

Two things `splice` does NOT do, and both have bitten: it moves item bodies
but **not their call sites** (wire each `declare_*` into its dispatcher
yourself), and it replaces the whole file, so **name-list and pin edits from
the other side are lost** — re-derive them, and recompute the pin by
**counting** the lists.

**THREE things, and the third SILENCES A TEST WITH EVERY COUNT STILL GREEN.**
`--anchor` inserts the spliced items immediately before the matching text, so
an anchor naming an item's **`fn` line** puts them *between* that item's
`#[test]` attribute and the function it decorates. Measured 2026-08-29:
anchoring on `fn clog_computes_and_its_boundary_equations_apply(` bound
`clog`'s `#[test]` to `land_bit`'s function, duplicated `land_bit`'s own
attribute, and **one test silently never ran**.

`cargo test` reported a healthy nonzero count throughout — the count is the
check this repository leans on hardest, and it cannot see this. Only
`clippy -D warnings` surfaced it, incidentally, in a sibling lane's tree.

So: **the anchor must sit ABOVE the item's attributes and doc comment**, not
on its `fn` line — anchor on the first line of the preceding item's doc
block, or on a `#[test]` you intend to precede. And after any splice into a
test file, run the affected tests BY NAME and confirm `1 passed`, never
`0 filtered out`. A `#[test]` separated from its function is invisible to
every count-based check there is.


