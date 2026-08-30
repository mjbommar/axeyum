# Notes: 151-absence-expiry

Detail moved out of [`../status/151-absence-expiry.md`](../status/151-absence-expiry.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Authority is a FRESH run, never a snapshot.** `kernel_declaration_projection`
(unfiltered, `--release`) — every declaration kind, not the theorem-only
inventories. The committed `artifacts/autogenesis/kernel-dependency-projection-v1.json`
holds **1,644** declarations against a live **1,861**, and a stale index is
wrong in the one direction that matters: it reports a newly-landed declaration
as *still absent*, so an expired claim reads as valid.
`authority_declaration_floor` (1,750 — below live, above that 217-declaration
gap) rejects a projection that short.

**Adoption, measured, not implied.** On the tree as it stands, with a freshly
built authority:

```
authority: 1861 distinct kernel declarations (floor 1750), roots covered: ...
scanned: 3993 files
markers: 5 (1 absent, 4 was-absent), naming 9 declaration(s); 10 more QUOTED
  in a code span or fence and read as documentation of the grammar
census: 705 absence-claim site(s); 145 name a declaration (4 carry a marker,
  141 do NOT); 560 name no declaration and are STRUCTURALLY UNCHECKABLE by
  any authority-derived gate
OK: 5 marker(s) checked against the kernel; every claim still holds.
  Marker coverage of checkable claim sites: 4/145.
```

**4 of 145 checkable sites are annotated. 141 are not.** Those four numbers
print on every run, pass or fail — a partial rollout reported as complete is
the same defect one level up, so the number is in the output rather than in a
claim about the output. `--list` prints the worklist. `bare_named_claim_budget`
is a **maximum** (141), so a new unexpirable claim naming a declaration fails
the gate; `--update-budget` records a deliberate increase and leaves a diff.

**The seeds, and one correction to the brief.** Four of the five known-stale
records of 2026-08-27 are annotated:
`diary-exact-root-obstruction.md` (two, for
`CReal.strict_mono_magnitude`/`CReal.diff_le_of_strict_mono_magnitude` and for
`CReal.converges_comp_eventually`), the `Rat` reindexing retraction, and
`CLAUDE.md`'s M-test paragraph.

**The fifth is NOT stale, and I checked before annotating it.**
<!-- absent: CReal.within_of_close_within -- the reverse close_within -> Within bridge trig_fn.rs:63 reports missing; verified against the live environment, and this paragraph goes red the day it lands -->
`crates/axeyum-lean-kernel/src/creal/trig_fn.rs:63` claims a `close_within` →
`Within` bridge "does not exist as a public lemma today". Read literally that
is **still true**: there is no `CReal.within_of_close_within`, and the twelve
`CReal.*within*` declarations in the live environment are `Within`,
`bound_within`, `close_within_of_within`, `close_within_of_within_indexed`,
`geom_pair_within`, `geom_tail_within`, `geom_tail_within_le`,
`sumRange_tail_cauchy_within`, `sumRange_tail_within`,
`sumRange_tail_within_cauchy`, `sumRange_tail_within_le`,
`within_of_two_sided_le` — none of them the reverse bridge. What was stale
was the *inference* a reader drew from it (that the M-test was blocked), and
**no authority-derived gate can catch a wrong inference from a true claim.**
That file is also out of this lane's scope (`crates/` has five live lanes), so
it carries no marker there; this paragraph carries the LIVE `absent:` marker
for it instead, and goes red the day the bridge lands.

**Demonstration: red before, green after.**
`scripts/tests/demo-absence-expiry-seeds.sh` copies the three seeded files
into a scratch root, rewrites `was-absent:` to `absent:` — restoring each
document to the state it was actually in the day it was written — and requires
the gate to report all **8** declarations `EXPIRED` with exit 1, then re-runs
the unrewritten copies and requires exit 0. Both halves are required: a gate
that always reds is the same as one that never does. It never touches a
tracked file. Verified against a freshly cargo-built authority: `DEMO OK: 8
seeded claim(s) red as live claims, green as historical records.`

**The gate found a defect in its own ADR on its first real run.** ADR-0611
quoted `<!-- was-absent: … -->` as an example, the generated ADR index copied
it, and both were parsed as live markers naming a declaration called `...`
(exit 2, malformed marker). The document defining the mechanism failed the
mechanism. Fixed by reading a marker inside a code span or a fence as
documentation of the grammar rather than as a claim — and by **counting**
those rather than dropping them silently (`10 more QUOTED`), because a
swallowed marker is a false green, the one outcome this gate must not produce.

**Mutation evidence: 25 of 25 guards killed, 0 SURVIVED, 0 unmeasured**
(`python3 scripts/tests/mutation_controls.py absence-claims`, registered
there so the mutant is built in a scratch copy and never in the shared
checkout). 33 controls, all of which load the REAL module from its real path
— none restates the subject. Three real findings from the first mutation run,
all fixed:

- **`the exclusion actually skips the file` SURVIVED.** The excluded fixture
  carried a claim naming no declaration, so deleting the exclusion could not
  move the budget and the test passed either way. A real gap in the test, not
  in the gate.
- **The marker-kind mutation was EQUIVALENT.** Reordering a regex alternation
  cannot make leftmost-first match `absent` at the `w` of `was-absent`, so it
  survived without meaning anything. Replaced with the mutation modelling the
  real hazard — comparing the kind by substring instead of equality, which
  reads every historical record as a live claim. It now kills two tests.
- **Three mutations scored INCONSISTENT**, and the cause is worth recording:
  assertion messages quoted the subject VERBATIM, and the subject prints lines
  beginning `FAIL: `, which the harness counts with `^(?:FAIL|ERROR): (\S+)`.
  One real failure read as two and one mutation's seven as fourteen. Messages
  are indented now (`Harness.quoted`). **A test that quotes its subject's
  output can corrupt an outer harness's classifier**, which generalizes beyond
  this suite.

**What it is structurally blind to**, stated rather than left to be found:

1. **A claim naming no declaration** — "the mesh toolkit is private", "no
   in-tree tool does this". 560 of 705 sites. No authority-derived gate can
   check these; the census reports them as `STRUCTURALLY UNCHECKABLE` rather
   than excluding them from the ratio.
2. **A wrong inference from a true claim** — seed 5 above.
3. **An obstacle that is a missing *step*, not a missing declaration.**
   CLAUDE.md's hiding place #2: a reusable step built inline inside a larger
   declaration has no name to check. The same blindness `shape_search`
   declares.
4. **The claim detector is a heuristic**, by construction. It found 320 `.md`
   files and 152 `.rs` files with a claim, against the brief's 231 and 150 —
   the `.rs` figure matches, the `.md` figure is wider. Only the marker half
   is exact; that is why only the marker half fails on a finding and the
   census half is a maximum.

**Not wired into `just check`,** for the reason `just claims` is not: the
authority is a `--release` kernel build. `just absence-claims` runs the gate
(~6.5 s once the binary exists); `just absence-claims-controls` runs the 33
controls and the seeded demonstration.

Verified: `python3 scripts/validate-facts.py` green; `./scripts/check-links.sh`
→ `all links ok`; `python3 scripts/gen-adr-index.py` regenerated (the
pre-existing `duplicate_numbers=0166,0167` is not from this lane); ADR number
taken from `git ls-tree origin/main`, not the local maximum.
