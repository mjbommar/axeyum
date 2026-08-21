# 17 -- P1-CARDS diary (render strand, P1)

Agent P1-CARDS, 2026-08-21. Charge: render the 324 fact cards, make the atlas
navigable in both directions, fix the four gripes in `16-reader-review.md`, keep
the build fast and deterministic, look at the pages, and gate the result.

Baseline before any change: `render/check.sh` 15 passed, 0 failed.
After: **21 passed, 0 failed** (11 steps; two of them are new).

## The headline

`render/out/` is a site now, not a folder of pages:

| quantity | value |
|---|---|
| pages emitted | **328** (324 cards + atlas + 2 pilots + certificate) |
| card render time | **1.3 s** for 324 pages, in one process |
| whole `build-outputs.sh` | **3.8 s** (was 2.4 s for 10 files), pdflatex included |
| byte-reproducible | yes, `diff -r` over two builds into different trees |
| relative links | **2085**, across 328 pages |
| broken links | **0** -- and two independent checkers say so |
| emitter diagnostics over the whole corpus | 0 (336 (manifest, format) pairs) |

## The load-bearing decision: a cross-reference names a SOURCE file

`13-facts-diary.md` item 5 called this correctly a round early: "the
card-to-card link story depends entirely on the figure renderer". It did, and
the renderer was doing the wrong thing -- `href: "cards/F-x.doc.json"` was
slugged into `data-href="cards-f-x-doc-json"`, an in-page anchor no page
contains. 152 boxes on the atlas were clickable and did nothing.

The fix had one real design choice in it: what does an `href` in the IR MEAN?

Rejected: put the output path (`cards/F-x.html`) in the document. That encodes
one emitter's file-naming into the data, and a Markdown atlas would then link to
`.html` because a producer decided so rather than because an emitter resolved
it.

Taken: **an href is the relative path of the referenced document's SOURCE**
(`cards/F-x.doc.json`, `../facts-atlas.doc.json#dep-graph-c02`), relative to the
referring document's own output file, and every emitter resolves it through one
function -- `doc_link_target` in `lib.rs` -- by swapping the extension. The
source file is the thing that exists on disk and can be checked. All three
emitters resolve to the HTML page, because that is the only format the whole
324-card corpus is rendered in; a Markdown atlas linking to `.md` files nobody
generated would be a dead link that looks live, which is the thing this strand
exists to stop.

Two consequences that are not obvious until you try it:

* **Output files must be named after their source**, or the references do not
  resolve. `axeyum-render render --name-by source` (new; `doc-id` is still the
  default and P0's goldens are unaffected), and `build-outputs.sh` passes it.
  Pleasant accident: the P0 script already renamed `fact-atlas.html` to
  `facts-atlas.html` by hand afterwards, so the deliverable names did not move.
* **A card's own hrefs had to change.** They said `cards/F-x.doc.json` -- the
  ATLAS's view -- from inside `cards/`, which is one directory too deep. The
  producer now takes an explicit prefix (`card_href(id, prefix)`), and the
  wrongness is impossible to reintroduce silently because the link test renders
  the real layout.

## Rendering the cards found three things no test could have

**1. All 324 cards were unrenderable under the strand's own gate.** The first
`--fail-on-diagnostics` run reported 648 diagnostics: every certificate block on
every card has neither an exit status nor a reason, and the emitter says so
because a box that is silent about whether anything ran implies a run nothing
records.

That is the emitter being right, so the fix is not to silence it. A fact-ledger
evidence row genuinely is an assertion plus an invitation: it says
`check_status: checked` and offers a command, and nothing recorded an execution
(`13-facts-diary.md` item 2). `Certificate.no_exit_reason` landed additively --
schema, `ir.rs`, `assemble.rs`, `validate-docir.py`, and both the Markdown and
LaTeX emitters, so the three formats say the same thing -- and every card now
states it in the box. With a guard, in both implementations: a certificate that
declares `no_exit_reason` AND cites a run record is **refused**, because those
are two contradictory statements about one box. The Python validator carries the
same rule independently plus one the Rust side does not have: a certificate with
neither is a warning there, since assembly must not refuse what the emitter is
designed to report.

**2. Four cards refused to assemble, correctly.** `ArtifactRef.path` means a
path, and assembly re-hashes every one; the producer was handing it the ledger's
bare `sha256:<64 hex>` content digests, which name no file. The rule working, on
a shape P0 never exercised because P0 never rendered a card. The producer now
puts only `present` files in `artifact_refs`; the digest, the directory and the
missing-file cases are still on the page verbatim, in the evidence-record table,
with the state this producer resolved them to.

**3. The batch path is worth 14 seconds, not 0.6.** Measured: 324 cards through
the release binary one process at a time is ~1.0 s; in one process, 0.36 s. But
the build script drives the CLI through `cargo run`, which costs 47 ms per
invocation, so the loop a build script would actually write is **~15 s** against
1.3 s. Assembly itself does not re-read the ledger per card -- `facts_dir.join(file)`
is a direct path, not a scan -- so there was no ledger-reading problem to fix and
I did not invent one. `cmd_render_batch` gives each document its own `Assembler`:
batch is a loop, not a shortcut, and a card that would be refused alone is
refused there. It refuses an empty batch rather than reporting success over zero
documents.

## The four gripes

**1. Title duplication.** The first block's heading is suppressed when it equals
the document title exactly -- first block only, exact match only, and only the
heading. Every card had this too (`build_card` titles its statement block with
the fact's title, which is `meta.title`), so it was 327 pages, not 3.

**2. Badge duplication.** `badge_compact`: the shape survives, the word becomes
the accessible name (`role="img"`, `aria-label`, `title`). The shape is the part
that carries information in greyscale and to a colour-blind reader; the word was
the part being repeated three lines below itself. `normalize_evidence` copies
the claim's resolved status into the row, so the second copy never carried
information.

**3. Dead node links.** Above. A node whose href names a document is now wrapped
in a real SVG `<a>`, so the browser navigates with scripting off and the JS cone
handler leaves it alone (it returns early with no `data-href`). A node whose
href is NOT a document reference keeps the in-page scroll behaviour.

**4. Narrow-width replay command.** Verified at 420px with headless Chromium.
INTEGRATE's `min-width: 0` fix made the row scroll instead of clip, which is
correct and still leaves a phone reader looking at 30 characters of a
300-character command through a letterbox. Below 46rem the command now WRAPS:
`pre-wrap` inserts nothing, so the bytes the copy button puts on the clipboard
are unchanged, and a hanging indent marks a continuation the way a wrapped shell
line does.

## What the screenshots found that the tests could not

Four defects, all invisible to a green suite, all found by looking. DESIGN's
round-1 note keeps being right.

| defect | cause | fix |
|---|---|---|
| every fold on a card sat ~190px left of the text above it | `details.ax-fold { margin: 0 0 X }` has the same specificity as `main.ax-doc > * { margin-left: auto }` and comes later, so it silently won | `margin: 0 auto X` on `.ax-fold` and `.card` |
| the same two-line provenance paragraph under all 15 blocks of every card | every block from one producer carries the identical `Provenance` | when they are ALL equal, hoist it to the header and say it once; the moment two differ, nothing is hoisted and every block prints its own |
| `supports` and `axiom_footprint` cells ran off the right edge | `white-space: nowrap` on non-first columns, so machine values cannot break at their hyphens -- correct, but those cells are sentences | the emitter marks a cell containing a space as prose; a token with no space still cannot break |
| the atlas index's last four columns, including the link to each card, were behind a horizontal scrollbar | 12 columns at the 36rem reading measure | a table of >= 4 columns breaks out to 52rem **centred on the measure**, so its heading stays aligned with the prose (breaking out the section instead made the page ragged -- I tried that first and the screenshot said no) |

Before/after screenshots at 1280px and 420px: a proved kernel-lean fact
(`F-nat-add-comm`), a computed Rado fact with a NEW RESULT badge and a
three-entry axiom footprint (`F-rado-r4-a5-b3`), a refuted fact with three
evidence rows and a four-entry footprint (`F-fp8-add-not-associative`), the
atlas, and the certificate at 420px. Written under `$HOME` and deleted: snap
Chromium cannot write to `/tmp`.

One thing I did NOT change: a certificate box on a `refuted` fact card shows the
`OPEN` badge, because `normalize_figure`'s verdict falls back to the weakest
reading when no evidence resolves a status. It reads oddly beside a REFUTED
claim, but it is the fail-closed default working, and the "no run recorded"
marker beside it explains why. Changing it would mean an emitter inferring a
status, which contract point 3 forbids.

## The gate, and proving it can fail

Two new steps, and the first of them is the price of the second.

Making node links real meant the self-containment lint has to accept a relative
`.html` href. That is a hole unless something checks the other end -- so:

* `render/tests/link_integrity.rs` renders the whole site (328 pages) and fails
  if any relative href does not resolve to an emitted file, or if any
  `#fragment` names an id the target page does not have. It also asserts the
  graph nodes specifically link out, because rules 1-3 are satisfiable by a site
  whose graphs link nowhere -- which is exactly the state gripe 3 described.
* `render/check.sh` step 10 is a SECOND implementation of the same sweep over
  the built site, for the reason the schema and the self-containment lint each
  have two: a bug in a checker is invisible to that checker.

Both can fail, demonstrated:

| control | result |
|---|---|
| one node href pointed at a card that does not exist | reported, `target file was not emitted` |
| a card's "up" fragment changed to `#dep-graph-c99` | reported, `target page has no element with that id` |
| an external `<img>` injected into an emitted card | the widened lint still reports it |
| step 10's own controls (missing file, missing fragment), one per rule | both rejected; a sweep that only checked file existence would pass the first and be blind to the second |

**Delete-one-guard on the widened lint.** Removing `!is_sibling_page(&val)` from
`lint_self_contained` kills exactly two tests: the unit test of the rule, and
`an_emitted_card_is_still_self_contained`, which lints a REAL emitted card. Two
deaths, deliberately -- one is the rule, the other is the rule applied to bytes
a reader would be handed. A single unit test would have let the rule drift away
from the corpus.

Also fixed while building the gate, and worth recording because it is the same
class every time: **step 8's own scratch renders were producing 706 "broken"
links**, because they used `doc_id` naming while the deliverable uses source
naming, and because three negative controls wrote page copies INTO the directory
step 10 sweeps. A control that manufactures the findings the next step reports is
not a control. All three now write outside it.

Step 3 asserts the four new tests BY NAME (this repository's signature inert
gate is a feature-gated suite compiling to nothing); step 8 renders the whole
card corpus in batch and asserts the page count equals the manifest count; step
7's ASCII sweep now covers `render/examples-input/facts/cards/` and
`build-outputs.sh`; the success floor rose from 13 to 19.

## Files

Renamed `render/build-p0-outputs.sh` to `render/build-outputs.sh` -- it is not
building P0 any more. `docs/render-2026-08/14-p0-exit-report.md` still names the
old path and was left alone: it is a dated record of what P0 ran.

Regenerated by their producer, not hand-edited: all 327 documents under
`render/examples-input/facts/` and everything in `render/out/`.
`render/assets/preview/preview.html` was re-blessed four times over this session;
every hunk is a mechanical consequence of a change argued above.

## Left for P1's successor

Ordered by what I would do first.

1. **The atlas index table is still the only path to a singleton fact.** 173 of
   324 facts have no `depends_on` edge in either direction, so nothing links to
   their cards except the index row. A search box (a few hundred bytes of
   inlined JS over a `data-` index) would make the corpus navigable rather than
   merely linked.
2. **A card carries no claim, so no card has a green badge from a run.** This is
   `13-facts-diary.md` item 2 and it has not moved: the ledger's checker
   commands have to actually RUN and emit run records. Every certificate on
   every card now says so explicitly, which at least makes the gap legible
   instead of implicit. P1-RUNREC owns the first step.
3. **A COORDINATOR CALL: `render/out/cards/` is 15 MB of generated HTML.**
   `render/out/` was 1.1 MB after P0 and is 17 MB now. Every byte of it is
   reproducible from committed manifests in 3.8 s, so the alternatives are real:
   commit it (a reader with the checkout has the site), or gitignore
   `render/out/cards/` and let `build-outputs.sh` produce it (the repository
   stays small and the atlas's links are dead until someone builds). I have
   made the site, not the decision; `13-facts-diary.md` item 5 left the same
   call open for the 9.2 MB of card manifests, which ARE committed, so the
   precedent points at committing.

4. **`build-outputs.sh` never deletes a stale card.** If a fact leaves the
   ledger its page stays in `render/out/cards/`. Deliberate -- a build script
   deleting files is worse -- but nothing yet reports the orphan. The link sweep
   cannot see it, because an orphan breaks no link.
5. **The three formats diverge on cross-document links.** HTML has a nav bar and
   linked cells; Markdown has a crumb line and linked cells; LaTeX has linked
   cells and no crumbs. `cross_format.rs` only binds claims, so nothing notices.
6. The `no_exit_reason` sentence is the same 40 words on 198 certificate blocks
   across 324 cards. It is honest and it is repetitive; a per-document statement
   of it (the way provenance is now hoisted) would read better.
7. `Certificate.artifact_refs` beyond path/sha256 and `Provenance.host` /
   `duration_ms` are still dropped -- INTEGRATE's item 5, untouched.
