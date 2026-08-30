# Notes: 148-dup-ratchet

Detail moved out of [`../status/148-dup-ratchet.md`](../status/148-dup-ratchet.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Consumer count alone would point at keeping `sampleUpperBound` canonical and
aliasing `rat_approx_upper` to it. **Build order overrides that.**
`density::declare_density` runs *before*
`uniform_continuity::declare_uniform_continuity` in `CRealPrelude`'s build
sequence (the latter calls `declare_sample_upper_bound`/`_lower` at its own
tail), so at the point `rat_approx_upper` would need to reference
`sample_upper_bound`, the kernel has not admitted it yet — that alias
direction does not type-check, full stop. Confirmed by writing it that way
first and watching `declare_density` fail to build (reverted before
committing). So: `rat_approx_upper`/`rat_approx_lower` (`density.rs`) stay
canonical, keep their exact proofs; `sample_upper_bound`/`sample_lower_bound`
(`uniform_continuity.rs`) become thin forwards (`d.lemma(p.rat_approx_upper,
&[x, n])` / `..._lower`). Both propositions confirmed identical up to the
bound-variable name (`n` vs. `m`) by reading the type-construction code line
for line, not assumed from the design-review doc.

Verified: `cargo test -p axeyum-lean-kernel --lib
creal::creal_tests::{sample_upper_bound,sample_lower_bound,crossing_sample_upper_and_lower,ivt_,close_within_of_within,creal_prelude_builds}`
(11 tests total across those filters) — all pass, including
`creal_prelude_builds` (the build-order fix is exercised there: it would
fail loudly with a "name not yet declared" kernel error if the order were
wrong). `cargo check -p axeyum-lean-kernel --lib` — clean, no new warnings
(the two now-unused independent-derivation helper functions in `density.rs`
were never touched since that file's proofs stayed as-is; no dead code was
left behind in `uniform_continuity.rs` either — checked by compiling, not by
inspection).

**Task 2 — the gate.** `scripts/check-shape-duplicates.py` runs
`shape_search --duplicates` and compares its reported groups (by exact
name-set, not shape text) against `scripts/shape-duplicates-allowlist.json`,
which carries all 10 currently-reported groups **each with a written
reason** (6 zero-cost aliases, 1 intentional cross-check, 3 now-fixed
accidents — `succ_sub_succ_eq_sub` from the prior pass and this pass's two
`sample*Bound` entries). Two failure modes, both exit 1:

- a reported group **not** on the allowlist ("NEW/UNADJUDICATED") — a new
  accidental duplicate, or an existing pair that gained a third member;
- an allowlist entry **not** currently reported ("STALE") — the
  `#[expect]`-style bidirectional half: an allowlist entry whose group
  stopped being a duplicate (renamed, or fixed a different way) must be
  removed, or it reads as still-considered when it is not.

Malformed input (bad allowlist JSON, unparseable `--duplicates` output, a
mismatch between the tool's own `verdict: DUPLICATE-GROUPS N` line and what
this gate parsed) is a distinct exit 2 — "the gate broke," not "a duplicate
was found."

Confirmed clean on the real tree: `python3 scripts/check-shape-duplicates.py`
→ `OK: 10 duplicate group(s), all allowlisted with a reason.`, exit 0.

**Mutation-verified, 8 of 8 guards killed, 0 survived**
(`scripts/tests/test_check_shape_duplicates.py::MutationTests`, plus 23
ordinary unit/end-to-end tests, 24 total, all green): each of
malformed-line-column-count, fewer-than-two-names, allowlist-empty-reason,
allowlist-bad-names-shape, allowlist-duplicate-entry, unrecognized-detection,
stale-detection, and verdict-count-mismatch was disabled one at a time in a
scratch-copied mutant (never the real file) and its own dedicated test
failed against the mutant while passing against the baseline. `unrecognized-
detection` and `stale-detection` are the two guards that matter most (they
are properties 1 and 2 from the brief); both killed cleanly.

**Live-fire demonstration (not just the unit mutation): a genuinely new
duplicate, constructed in an isolated `/data0` snapshot, makes the real
`shape_search` + gate pipeline go red; the unmutated tree is the control and
is green.** Run: `scripts/lane-snapshot.sh HEAD` (this commit) to
`/data0/axeyum/scratch/snap-dup-ratchet-0a4655064` (never the shared checkout
or this lane's own worktree); in that copy only, added a third declaration
of `nat_prelude/order_extra.rs`'s existing `Nat -> Nat -> Nat.le -> Nat.le`
shape (`ScratchDuplicateSuccLeSucc`, forwarding to `le_succ_succ`'s proof
term — a real, kernel-checked declaration, not a fabricated log line), built
`shape_search` in release there (fresh `target/`, 36.8s), and ran it:

```
DUPLICATE  Nat -> Nat -> Nat.le -> Nat.le  Nat.le_succ_succ Nat.succ_le_succ ScratchDuplicateSuccLeSucc
verdict: DUPLICATE-GROUPS 10
```

(count stays 10 — the group grew from 2 members to 3, it did not become an
11th group, which is exactly why `--expect <N>` alone, the count-only check
`shape_search` already ships, could not have caught this.) Then:

```
$ python3 -B scripts/check-shape-duplicates.py --duplicates-file dup-output-mutant.txt
FAIL: 1 duplicate group(s) not on the allowlist:
  NEW/UNADJUDICATED  Nat -> Nat -> Nat.le -> Nat.le  Nat.le_succ_succ Nat.succ_le_succ ScratchDuplicateSuccLeSucc
  ...
FAIL: 1 allowlist entry is stale (no longer reported):
  STALE  Nat.le_succ_succ Nat.succ_le_succ  ...
MUTANT exit=1
```

Both failure modes fired from one real mutation, because a group gaining a
member changes its name-set identity: the new 3-member group is unrecognized
AND the old 2-member allowlist entry is simultaneously stale. Control, same
gate script, the real (unmutated) tree's real `shape_search` output captured
earlier in this session:

```
$ python3 -B scripts/check-shape-duplicates.py --duplicates-file <captured real output>
OK: 10 duplicate group(s), all allowlisted with a reason.
CONTROL exit=0
```

Scratch snapshot deleted after the demonstration (`rm -rf`), per the
"isolated scratch tree, never committed" instruction — nothing from the
mutation is part of this lane's diff.

**On the 6 "safe" groups, re-examined:** nothing new. Re-reading
`characterization.rs`'s four bundle entries, `weak_law_of_large_numbers`, and
`succ_le_succ` while writing the allowlist reasons did not surface anything
the prior pass's adjudication missed — each is still a one-line
`d.lemma`/`const_` forward with zero re-derived proof steps.
