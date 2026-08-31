# ADR-1250: A marker that cannot attach is the mirror of a checker that cannot fail

Status: accepted
Date: 2026-08-31
Index-summary: `scripts/check-absence-claims.py` (ADR-0611) makes a prose
absence claim expire, and a resolved claim is retired by writing a
`<!-- was-absent: Root.name -->` marker beside it. A correctly-placed,
correctly-named marker at
`docs/plan/status/first-supplementary-law.md:54` did not attach, and the gate
stayed red at **123 bare named claims against a budget of 122**. The cause is
neither of the two hypotheses that were proposed: the harvested subject IS
`Int.prodRange_split`, and the marker's scope IS the same block. `MARKER_RE`'s
body is `.*?` compiled **without `re.DOTALL`** and applied one source line at a
time in all three readers, so a marker written across three lines matched
NOTHING — it was invisible, not unattached: unchecked against the kernel,
silencing nothing, and absent from the marker count. Measured over the 4,695
scanned files, 68 per-line matches against 69 real markers. **The practical
consequence is that the only remaining way to retire a resolved claim was
`--update-budget`, which is precisely the laundering the gate exists to
prevent** — so a lane following the documented convention correctly had no
honest move at all. Fixed by compiling `MARKER_RE` with `re.DOTALL` and having
every reader work from one per-source-line assembly (blanked inside fences,
outside prose, and where a code span quotes a marker) so the regex runs across
the join while line numbers stay exact; plus a Rust comment-prefix strip so a
wrapped names list inside a `//!` block does not carry `//!` into a name, and a
marker-strip that preserves newlines so a claim below a multi-line marker is
still reported at its own line. Bare named claims **123 → 122** against an
unchanged budget of 122. Not a weakening: all 8 known-stale claims (11
declarations) are still caught, `StaleClaimRegression` green with fixtures
untouched, 48 tests and **zero surviving mutants**.
Index-status: accepted

## Context

ADR-0611 built the expiry mechanism: a live absence claim gets
`<!-- absent: Root.name -->` and the gate goes red the day that declaration
lands; a resolved claim gets `<!-- was-absent: Root.name -->` so it stops
counting against the bare-claim budget while staying under the gate in the
other direction.

ADR-1190 then narrowed claim/name pairing from block granularity to a
*record then sentence* unit, taking bare named sites 250 → 122 and **lowering**
the budget rather than raising it. Closing the hole that finer granularity
opened — a marker for `X` silencing a claim about `Y` in the same block —
required a marker to NAME its subject.

Against that, a lane resolving `Int.prodRange_split` in the same session it
recorded the blocker wrote:

a self-correcting sentence recording that the `prodRange` split it had been
blocked on was now landed, and immediately below it, in the same block:

```markdown
<!-- was-absent: Int.prodRange_split -- built by this same lane (ADR-1230).
     The sentence above is history, not a live claim; this marker is what
     lets check-absence-claims.py expire it rather than count it forever. -->
```

(Quoted in a **fence**, not indented — an indented block is not a fence, so a
marker written there is read as a live one. That is this ADR's own caveat
applied to itself. Note also that the block-level harvest does not track
fences, unchanged here: a marker quoted inside a fence still silences a claim
in the same block, which is why the surrounding sentence is described rather
than quoted.)

The site was still reported BARE and the gate stayed red at 123/122. Two
hypotheses were proposed: that the harvested subject was not
`Int.prodRange_split`, or that the marker's scope was still block-level while
the claim's had become sentence-level so the two no longer met.

## Decision

**Both hypotheses are wrong, and the mechanism is simpler and worse than
either.** Driving the real module over the real file:

    MARKERS PARSED IN FILE: 0
    SITE line 50 | annotated=False | candidates: ('Int.prodRange_split',)

The subject harvested from that sentence is exactly `Int.prodRange_split`, and
the marker sits in the same block. The marker is **not parsed at all**.

`MARKER_RE` is

    r"<!--\s*(?P<kind>was-absent|absent)\s*:\s*(?P<body>.*?)\s*-->"

with `re.IGNORECASE` and no `re.DOTALL`, and it was applied per line in all
three places that read a marker — the file-level marker pass, the block-level
name harvest, and the body strip. `.` does not match a newline, so a marker
written across lines matches nothing anywhere. A marker is an HTML comment,
which is a multi-line construct, and one carrying a note wraps at the same
column as the prose around it; writing one across three lines is the natural
thing to do rather than an abuse.

Surveyed over the whole scanned surface, 4,695 files: **68 per-line marker
matches against 69 real markers.** Exactly one multi-line marker existed in the
tree, and it was the one that would not attach.

**A marker that cannot attach is the mirror of a checker that cannot fail, and
it fails in the same silent way.** Nothing reported a malformed marker; nothing
reported an unattached one; the marker count simply did not include it. The
cost is not cosmetic: the sole remaining lever for retiring a resolved claim
was `--update-budget`, the laundering this gate exists to prevent, which two
lanes had already correctly declined to use.

Three changes, each with a control:

* `MARKER_RE` gains `re.DOTALL`, and the file-level pass assembles one entry
  **per source line** — blanked inside a fence, on a non-prose line, and where
  a code span quotes a marker — so `"\n".join(...)` lets the regex run across
  the whole file while a match's line number is still exactly its newline
  count. Fence content is collected into runs and counted as `quoted`
  separately, so a multi-line marker inside a fence is still reported as
  documentation rather than swallowed.
* `marker_scan_line` drops a leading Rust comment prefix. Without it, a marker
  whose NAMES LIST wraps inside a `//!` block carries `//!` into the second
  name and the whole marker is rejected as malformed. (A marker whose *note*
  wraps parses either way, because `//!` lands after the ` -- ` separator —
  which is why the obvious fixture for this guard is vacuous, and the
  registered control deliberately wraps the names instead.)
* `blank_marker` replaces a marker with a space **plus its own newlines**. The
  census locates a claim by index into the marker-stripped body, so collapsing
  a three-line marker to one space shifts every following line in that block by
  two and the gate names prose that carries no claim.

The block-level harvest now reads the same assembly as the file-level pass.
Reading raw block lines there would reintroduce the defect one level down — a
marker CHECKED against the kernel and still not attaching — and it also closes
a small pre-existing hole in the other direction: a marker quoted in a code
span used to silence a claim in its block while never being checked itself.

The convention is restated in full in the checker's docstring, which is the
only place anyone learns it: same block, name the subject, and a marker may
wrap. With the reverse caveat that follows from the last rule — a code span
cannot quote a multi-line example, so quote one in a **fence**.

## Consequences

**The claim is retired and the gate is green.** The marker now parses at
`docs/plan/status/first-supplementary-law.md:54` and the site at line 50 reads
`annotated=True`. Bare named claims **123 → 122**; markers 41 → 42.

**The budget is unchanged at 122 and was not touched.** ADR-1190 set it by
measurement; the tree had drifted one above it, and retiring the resolved claim
brought the tree back to the recorded number rather than the number being moved
to the tree. `--update-budget` was not run.

**Not a weakening.** All 8 known-stale claims and their 11 declarations are
still attributed and still caught end to end:
`scripts/tests/fixtures/absence-stale-claims/` untouched,
`StaleClaimRegression` green. 48 tests pass; `python3
scripts/tests/mutation_controls.py absence-claims` reports **zero survivors**,
with the three new guards registered as `G25` (a marker may be written across
lines, killed by three tests, all of which genuinely traverse it), `G26` (the
wrapped Rust comment prefix, killed by exactly one) and `G27` (a stripped
marker keeps its newlines, killed by exactly one). Three pre-existing anchors
had to be re-pointed at the rewritten code; `mutation_controls.py
--check-anchors` catches a stale anchor and did.

**The general rule this instance teaches.** A mechanism for retiring a claim is
part of the gate, not an accessory to it. When the retirement path is broken,
the gate does not merely mis-report — it drives every honest user toward the
one lever it was built to make unnecessary. So a gate that budgets something
must have its *escape hatch* exercised by a control, in the same way its
finding is: this suite had 45 tests and not one of them wrote a marker the way
a person writes one.
