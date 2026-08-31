# Lane: absence-marker-attach

<!-- plan-section: lane-status -->

Status: DONE — the marker mechanism could not attach a multi-line marker;
fixed, controlled, and the gate is green at an unchanged budget.

## The diagnosis (measured, not guessed)

`docs/plan/status/first-supplementary-law.md:50` carries a claim whose harvested
subject is exactly `Int.prodRange_split`, and a `was-absent:` marker naming that
same declaration sits in the same block. The site was still reported BARE.

Neither hypothesis in the brief holds. Driving the real module over the real
file:

    MARKERS PARSED IN FILE: 0
    SITE line 50 | annotated=False | candidates: ('Int.prodRange_split',)

The subject is right, the scope is right, and the marker is **not parsed at
all**. It is written across three lines, and `MARKER_RE`'s body is `.*?`
compiled **without `re.DOTALL`** while being applied one source line at a time
in all three readers — the file-level marker pass, the block-level name
harvest, and the body strip. A marker is an HTML comment, so it is a multi-line
construct; wrapping one that carries a note is the natural thing to do.

Surveyed over the whole scanned surface, 4,695 files: **68 per-line marker
matches against 69 real markers.** Exactly one multi-line marker existed in the
tree, and it was the one that would not attach.

The cost is not cosmetic. With the marker invisible, the only remaining way to
retire a resolved claim was `--update-budget`, which is the laundering this gate
exists to prevent — so a lane following the documented convention correctly had
no honest move at all. **A marker that cannot attach is the mirror of a checker
that cannot fail**, and it fails just as silently.

## What changed

Three parts in `scripts/check-absence-claims.py`, each with a control:

- `MARKER_RE` gains `re.DOTALL`, and the file-level pass assembles one entry per
  source line — blanked inside a fence, on a non-prose line, and where a code
  span quotes a marker — so the regex runs across the join while a match's line
  number stays exactly its newline count. Fence content is collected into runs
  and counted as `quoted`, so a multi-line marker in a fence is still reported
  as documentation rather than swallowed.
- `marker_scan_line` drops a leading Rust comment prefix, so a marker whose
  NAMES LIST wraps inside a `//!` block does not carry `//!` into a name.
- `blank_marker` keeps a stripped marker's newlines, so a claim below a
  multi-line marker is still reported at its own source line.

The block-level harvest reads the same assembly as the file-level pass; reading
raw lines there would have reintroduced the defect one level down (a marker
CHECKED against the kernel and still not attaching).

The convention is now stated in full in the checker's docstring — same block,
name the subject, a marker may wrap — with the caveat that follows: a code span
cannot quote a multi-line example, so quote one in a fence.

## Numbers

| | before | after |
| --- | --- | --- |
| markers parsed | 41 | 42 |
| bare named claims | **123** (over budget) | **122** |
| `bare_named_claim_budget` | 122 | 122 (unchanged) |
| gate exit | 1 | 0 |

The budget was NOT moved. ADR-1190 set it by measurement; the tree had drifted
one above it, and retiring the resolved claim brought the tree back to the
recorded number. `--update-budget` was not run.

Not a weakening: all 8 known-stale claims and their 11 declarations are still
attributed and still caught end to end (`StaleClaimRegression` green, fixtures
untouched). 48 tests pass; `mutation_controls.py absence-claims` reports **zero
survivors**, with `G25`/`G26`/`G27` newly registered and three pre-existing
anchors re-pointed at the rewritten code.

## Landed changes

| what | where |
| --- | --- |
| multi-line markers parse, attach and keep line numbers | `scripts/check-absence-claims.py` |
| the convention, restated in full | `scripts/check-absence-claims.py` docstring |
| G25 / G26 / G27 controls | `scripts/tests/test_check_absence_claims.py` |
| G25 / G26 / G27 mutations, three anchors re-pointed | `scripts/tests/mutation_controls.py` |
| the resolved claim retired | `docs/plan/status/first-supplementary-law.md` |
| budget re-verified at 122, reason recorded | `scripts/absence-claim-census.json` |
| the decision | ADR-1250 |
