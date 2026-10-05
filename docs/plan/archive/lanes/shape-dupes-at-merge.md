# Lane: shape-dupes-at-merge — run the duplicate-declaration gate at merge time

<!-- plan-section: lane-status -->

**`DONE`, shape-dupes-at-merge, 2026-09-02.** `scripts/check-shape-duplicates.py`
— the L0 gate that catches two declarations proving one proposition — was **red
on `main` for ~25 hours** and named in **0 of that day's 240 commit messages**
(lane `retrieval-audit-0901`), with a literal duplicate landing **16 h 29 min**
after its twin inside the window. The gate worked; nobody ran it, because it
needed `cargo run --release … shape_search` and so lived only in the ~10-minute
full gate. It now has a **no-cargo route** (`--prebuilt`) and runs as **point 7
of `scripts/check-merge-hygiene.sh`**, defaulting ON. ADR-1511 amended with the
measured cost; the amendment is a third lane on that ADR's split — *give the
expensive check a cheaper route and run the real thing*, rather than a proxy.

**Measured cost, and it is over the ~30 s the brief allowed** (s4, warm binary,
2026-09-02): `--prebuilt` **60.9 s** and **70.0 s** unpinned at load 11.9 / 17.1;
**41.7 s** with `taskset -c 0-7`; the cargo route **58.8 s** warm; a cold
release build of the example **91.9 s**. So the prebuilt route does **not** save
the run — both routes pay `shape_search`'s index build over ~1,850 declarations
— it saves the *build*, and makes the cost bounded: absent or stale binary
reports `skipped(...)` in ~0.1 s instead of compiling the kernel. Being an order
of magnitude over the gate's ~2-7 s baseline, it carries
`AXEYUM_SKIP_SHAPE_DUPLICATES=1` as a documented escape, defaulting ON, and the
summary line reports the skip — a run that did not ask is distinguishable from
one that asked and found nothing.

**A stale prebuilt binary never answers.** It indexes the declarations it was
compiled against, so a duplicate that landed after the build reads as ABSENT — a
false PASS on exactly the question this gate exists to answer. The staleness
test is `fact-frontier.py`'s `kernel_projection_is_stale`, **imported rather
than copied**.

**Exit 2 is not uniformly skippable here, which is the correction to the
`gen-py-prelude-fields.py` precedent.** That generator has one unanswerable
state (no `rustfmt`), so its caller can treat every 2 as skipped.
`check-shape-duplicates.py` has two things behind one code: a **malformed
allowlist** (a defect in a committed file, pinned by its own
`test_malformed_allowlist_exits_two` — must block) and an **absent-or-stale
binary** (a fact about this host — must not). Copying the precedent verbatim
would have turned a broken allowlist into silence. Only the unanswerable case
prints a leading `SHAPE-DUPLICATES|UNAVAILABLE <token> -- <reason>` line, and
the gate keys on that marker, not on the exit code alone.

**End-to-end discrimination**, in this lane's own worktree (isolated — no other
lane compiles from it; `git status --porcelain crates/` clean after restore). A
second declaration of `Nat.add_zero`'s exact proposition added under a new name
in `nat_prelude/defs.rs`, `shape_search` rebuilt through
`scripts/cargo-serialized.sh` (1 m 25 s):

    FAIL: check-shape-duplicates.py --prebuilt (exit 1)
      NEW/UNADJUDICATED  Nat -> Eq  Nat.add_zero Nat.add_zero_e2e_probe
    MERGE_HYGIENE|FAILED                              -> gate exit 1

Probe removed, rebuilt (1 m 29 s): `OK: 15 duplicate group(s), all allowlisted
with a reason. (route: prebuilt)`, `shape_duplicates=ok`, gate exit **0**.

**Mutation table** (`scripts/tests/mutation_controls.py merge-hygiene`, isolated
scratch root; 19 tests, baseline green):

| mutant | killed |
|---|---|
| M10 a reported duplicate group fails the gate | 3 |
| M11 an absent/stale index is SKIPPED, not a failure | **1** |
| M12 exit 2 WITHOUT the marker still blocks | **1** |
| M13 the opt-out is honoured and reported | **1** |

M11/M12/M13 are split three ways deliberately: one mutant over the block would
report a kill without saying which *direction* is guarded, and the direction
that matters is the one that fails silently. M10 killing 3 is the gate's
structure (one shared `elif`), the same shape as M1 and M4.

**A finding about the mutation harness, recorded because it manufactured two
non-results.** `mutation_controls.py` names dead tests with
`^(?:FAIL|ERROR): (\S+)` and cross-checks the count against `FAILED
(failures=N)`. The gate under test prints its own findings as `FAIL: <check>` at
line start, so a raw `done.stdout` in a failing assertion's message parses as a
SECOND dead test: M11 and M13 first reported `INCONSISTENT — the summary line
says 1 died but 2 were named` for mutants that killed exactly one. **The harness
was right** — it refuses to report a number it cannot cross-check. Fixed on the
control side (`_ctx()` indents the captured output); the parser is untouched.
Any future control suite over a script that prints `FAIL:` at line start meets
this.

**What this does not close.** The gate answers only when a fresh release binary
exists in the tree being merged. On a coordinator checkout that builds regularly
that is the common case; on a fresh worktree it reports `skipped(no-binary)` and
a duplicate still lands. Strictly better than the 25-hour silence it replaces —
the summary line now says at every merge whether the question was asked — but a
route, not a guarantee. Making it a guarantee means paying the build, which this
lane measured and declined.

<!-- plan-section: landed-changes -->

| 2026-09-02 | `35ca4cf70` | Lane status stub (early commit). |
| 2026-09-02 | `63f887b89` | `--prebuilt` route on `check-shape-duplicates.py`: runs `target/release/examples/shape_search --duplicates` directly, no cargo and no flock; absent or stale binary exits 2 with a `SHAPE-DUPLICATES\|UNAVAILABLE <token>` marker instead of answering, reusing `fact-frontier.py`'s `kernel_projection_is_stale`. Wired as point 7 of `scripts/check-merge-hygiene.sh` (exit 1 blocks; marked exit 2 is `shape_duplicates=skipped(<token>)`; unmarked exit 2 still blocks, because a malformed allowlist is a committed defect). Four controls added, 19 tests green, mutants M10-M13 registered and each of M11/M12/M13 kills exactly one. |
