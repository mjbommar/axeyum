# 15 -- INTEGRATE diary (render strand, round 2)

Agent INTEGRATE, 2026-08-21. Charge: close P0 against `04-prototype-plan.md`,
work the round-2 items the four round-1 diaries queue, adjudicate three
contested points, produce the deliverables, run the gate and the mutation pass.
Measurements and criterion-by-criterion results are in `14-p0-exit-report.md`;
this file is the reasoning, the judgement calls, and what is left.

## The first thing I did was look at a page, and it was broken

Every one of the four committed manifests rendered, in every format, exit 0,
with the round-1 gate green. And every FIGURE in every one of them was a loud
red box reading `unknown figure kind unknown`.

`normalize_resolved` dispatched figures through the externally tagged shape
(`{"DepGraph": {...}}`) that DESIGN's hand-written sample IR uses. Assembly's
`ir::FigureSpec` is INTERNALLY tagged, on `figure_type`, in kebab-case. The two
never met, because the only documents the emitter had ever been run against
were the preview page's -- which is built by hand, in the emitter's own shape,
and is a golden test. So the test suite was green over an emitter that could
not draw a single figure a producer had ever emitted.

That is worth naming precisely, because it is not a bug so much as a shape:
**a golden test whose input never goes through the pipeline tests the emitter
against itself.** The round-2 cross-format test now runs against the REAL
committed manifests for exactly this reason, and `render/check.sh` step 8
renders the whole corpus in all three formats on every run.

Credit where it is due: DESIGN's loud-box-plus-diagnostic design is why this
took two minutes to find instead of never being found. The document did not
silently lose its figures; it said so, in the biggest type on the page.

## Round-2 items from the four diaries

**CORE's list.** `html` is now a DEFAULT feature (`render/Cargo.toml`), clippy
and the test suite run `--all-features`, the formatting partition covers the
whole package, and the HTML emitter joined `tests/cross_format.rs` (contract
point 5) with a `data-claim`/`data-status` parser plus the anti-vacuity control
in both directions. The kernel-inventory path is still unexercised (no snapshot
file); left for P1.

**DESIGN's list.** All three named soft spots in `normalize_resolved` are
closed:

* `RichText.html` is honoured, through `inline_or_html`, and it is closed the
  way DESIGN asked: the fragment goes through the self-containment lint AND
  must be ASCII, any finding means the markup is NOT inlined, the reader gets a
  loud box beside the escaped fallback, and the emitter records a diagnostic.
  Wired at prose and claim statements; captions still ignore an override, which
  is recorded below rather than claimed.
* `Statement.show` is honoured -- and honouring it turned out to matter more
  than a fidelity fix. All 324 fact cards ask for `proof_route`,
  `axiom_footprint`, `depends_on` and `evidence_count`, and the emitter had no
  renderer for any of them, so every card silently dropped the axiom footprint:
  this project's headline metric. `trust_base()` renders them now.
* `PlotType::Bar` has a bar renderer instead of falling through to a polyline.
  A renderer that quietly substitutes one chart type for another is the same
  class of defect as one that quietly drops a multiplication sign.

`Certificate.artifact_refs` beyond `path`/`sha256` and the `Provenance` fields
beyond `generator`/`command`/`exit_status` are still dropped; both are recorded
for P1, not fixed.

**CERT's list.** `BlockTable.from_run` is now USED by the certificate manifest
(section below), and `RunRecord.role` exists (section below).

**FACTS' list.** The atlas layout does not survive 324 nodes and now does not
try (section below).

## Adjudications

### (a) Exit criterion 5, "mutate one d(k)"

Adjudicated as ADJUSTED-PASS, argued in `14-p0-exit-report.md` section 8 and
implemented in `render/tests/pipeline_negative_control.rs`. Short version: the
criterion asks for a rendered artefact to change; the system refuses to render
it at all, because the document pins the record's digest. The test therefore
asserts BOTH halves -- tampering is refused, and a record from a genuinely
different RUN changes the table and flips the claim -- using CERT's real M1
record and no fabricated numbers. `04-prototype-plan.md` carries a dated note.

CERT called this correctly in their diary ("with today's shape the mutation is
refused before anything renders, which is arguably better but is not what the
criterion says") and left the decision to the exit-criteria audit. It is
better, and the criterion is the thing that changed.

### (b) The loud box is CORRECT, and it is now in the contract

`lib.rs` contract point 2 said an emitter is TOTAL: every block renders to
something, no escape hatch. That leaves a hole an emitter can satisfy by
DROPPING what it does not understand -- the document is then simply shorter,
nothing fails, and a reader cannot tell a document that omits a figure from one
that never had one. DESIGN closed it in code before it was in the contract.

Point 2 now states the pair as the contract: **the page says so** (a visible
`unrenderable` box, never absence) **and the caller can find out**
(`Emitter::diagnostics`, a new default-empty trait method). The distinction
that keeps this from being a second judgement about evidence, written into the
text: **assembly REFUSES, an emitter REPORTS.** Diagnostics cannot upgrade
anything and never decide a status.

`axeyum-render render` prints diagnostics to stderr ALWAYS and refuses under
`--fail-on-diagnostics`; `render/check.sh` step 8 uses the flag over the whole
corpus. It is currently zero diagnostics on all twelve (manifest, format)
pairs.

One consequence I did not expect: `latex_to_mathml` has always returned an "was
every token recognised" flag, and the call site in `inline` discarded it. So a
formula outside the LaTeX subset rendered a red `<merror>` box on the page and
told nobody. `emit_with_diagnostics` now scans the finished bytes for
`<merror>` -- catching every call site at once, the same reason the
self-containment lint works on output rather than inputs. It immediately found
one: `j'(6)`, in the statement of Theorem 4, on the flagship certificate page.
A prime is an operator, not an unknown token; it has an arm now.

### (c) Strict mode versus negative-control blocks

Adjudicated: **a production page must not embed a refuted control.**
`certificate.doc.json` carried the M1 negative control as a folded block, which
meant the strand's flagship document could never be rendered under `--strict`
-- red evidence is a build error there, and that block's evidence is red on
purpose. Correct behaviour, wrong document.

The control now ships only as `certificate-negative-control.doc.json`, which is
the strict-mode fixture. Measured:

```
$ axeyum-render validate --manifest certificate.doc.json --strict                  exit 0
$ axeyum-render validate --manifest certificate-negative-control.doc.json          exit 0  [REFUTED]
$ axeyum-render validate --manifest certificate-negative-control.doc.json --strict exit 1
```

Both are in the corpus and both are gated; only one is a publication. The
prose that pointed at the removed block ("its failing record is on this page
too, folded away below") is unchanged in the source manifest generator's
`PROSE_THIS_PAGE` and should be revised by whoever next edits that prose -- it
now describes the pair of documents rather than one page. Recorded as a P1
nit rather than silently rewritten, because it is a human's sentence.

## The negative-control role

CERT's item 4: a run record had no machine-readable way to say "I am a
recording of a deliberately broken run". It said so in `notes` and in the
record id, which is prose, and a checker cannot read prose.

Landed, additively, in four places at once because a discriminator that only
one implementation enforces is decoration:

1. `docir.schema.json`: `RunRecord.role` (`production` | `negative-control`,
   default `production`) and a fifth member of `EvidenceRef.role`.
2. `ir.rs`: `RecordRole`, `RunRecord.role`, `EvidenceRole::NegativeControl`.
3. `assemble.rs`: the pairing is enforced in BOTH directions -- a control may
   be cited only under the control role, and that role may cite only a control.
   Two guards, two tests, one death each.
4. `scripts/validate-docir.py`: the same rule again, independently, as a
   cross-file check; plus one rule the Rust side does not have -- a record that
   declares itself a negative control and yet exited 0 with
   `outcome: established` is an error, because a negative control that did not
   fail is not a control.

The producer grew `--role`, both records were regenerated by real runs, and the
seven-mutant suite from the paper repository was re-run against the patched
producer: `mutants=7 failures=0`, every one dying with its recorded catcher. A
flag that changed what the certificate CHECKS would have been unacceptable; the
measurement is what says it did not.

Deliberately NOT taken: CERT proposed `production | negative-control |
fixture`. `fixture` has no rule attached, and an enum member no checker reads
is the same prose problem one level up.

## The d(k) table stopped being a transcription

CERT's guard probe found the one hole in the certificate page: editing a `d(k)`
inside the RECORD is refused (the document pins its digest), but editing the
COPY of those rows in the manifest rendered happily with the wrong number. The
manifest transcribed 24 of the record's 397 rows.

The block is now `from_run`, so assembly copies columns, rows and provenance
out of the record and the numbers exist in exactly one place. The cost is that
the whole 397-row sweep renders instead of a reader-sized selection, which is
why the block is `detail`: folded in Markdown and HTML, in the appendix in
LaTeX. A row-selection facet on `from_run` (show these k, from that record) is
the right P1 answer; performing the selection in the producer would be a
transcription again, which is the thing being removed.

## The atlas does not survive 324 nodes, and now says so

Measured: the layered layout over all 324 facts is **32,936 x 674 px**, because
173 of them have no `depends_on` edge in either direction and land in a single
row. Scaled into a 68rem column that is a two-pixel-tall smear.

So above 40 nodes the atlas ships one graph per connected component (37 of
them, largest 31 facts), largest first, components of five or more open and the
rest folded, plus a prose block stating the measurement that forced the split
and the full index table -- which was always the complete list. The producer
carries the threshold and the reasoning.

Two more legibility defects found by looking at the rendered page:

* **Every node in the Fibonacci component read `Mathlib v4.30 source~`.** Nine
  facts, nine identical boxes, because a box holds about fifteen characters on
  two lines and their titles share a 28-character prefix. Node labels are now
  the fact's short id (`ml430-nat-fib-add-two`), which is distinguishing by
  construction and fits; the full title is the tooltip, via a new optional
  `tooltip` on `FigureDepGraph.nodes` (additive schema change) that the emitter
  puts in the SVG `<title>`.
* **A graph wider than the column was SHRUNK, text and all.** The largest
  component at 1749px in an 800px frame put its labels at about four pixels.
  Past 900px the emitter marks the SVG `ax-graph-natural`, which opts out of
  `max-width: 100%` and lets `.ax-figframe`'s existing horizontal scroll do the
  work, so a node label is the same size in every figure on the page.

## Two more defects found by screenshot, not by tests

* **The replay command was CLIPPED, not scrolled.** `.ax-cmd > code` is a flex
  item with `overflow-x: auto`, but a flex item's default `min-width: auto` is
  its content width, so the overflow never engaged and the row's
  `overflow: hidden` cut the command a reader is invited to paste. One
  declaration (`min-width: 0`). Verified by rendering the row alone WITHOUT
  `--hide-scrollbars`: there is a scrollbar now, and there was not before.
* **The provenance line printed twice under every table**, identical, because
  the table renderer prints its `source` and the block renderer then printed
  the block's own provenance -- which is the same run for every table a single
  producer emits. Deduplicated where they are equal.

DESIGN's round-1 note stands: screenshots are a gate here, not a nicety. Four
of the six defects in this diary were invisible to a green test suite.

## The gate, and the gate's own inert step

`render/check.sh` is ten steps, 15 results, and it now covers what round 1
could not: `--all-features` everywhere, the whole P0 corpus through the schema
validator (nine files, not two), the corpus rendered in all three formats with
a non-empty diagnostics list FAILING, an independent grep-based
self-containment gate over the emitted HTML, and LaTeX compiling both the
fixture and the deliverable.

Two of my own steps were defective when written, and both are in the report
because they are the interesting part:

1. The self-containment grep gate repeated, on its first try, the exact bug
   DESIGN documented in the Rust lint: `\bhref="` matches the tail of
   `data-href="`. It reported 177 violations that were not violations. A second
   implementation that repeats the first one's bug is worth nothing; it parses
   attributes by name now.
2. **The diagnostics step was inert.** Its negative control handed the renderer
   a figure with no SVG -- which ASSEMBLY refuses, so the command exited 1
   without the emitter ever running. Deleting the `--fail-on-diagnostics`
   refusal in `main.rs` left the whole step green. Found by the delete-one-guard
   pass, which is the only reason it is not still there. The control now uses a
   document that assembles cleanly and is undrawable only to the emitter, and
   it runs that document twice: without the flag it must SUCCEED, with the flag
   it must be REFUSED.

## Golden-file changes, line by line

One golden changed: `render/assets/preview/preview.html`, four hunks, all
mechanical consequences of changes argued above.

| hunk | change | why |
|---|---|---|
| `.ax-cmd > code` | `+ min-width: 0` and a five-line comment | the clipped replay command |
| `svg.ax-graph.ax-graph-natural` | new rule + two-line comment | wide graphs render at natural size |
| `svg.ax-plot .series-bar` | two new rules | `PlotType::Bar` has a renderer now |
| `<svg class="ax-graph">` on `fig-dag` | `+ ax-graph-natural` | the preview's own graph is 1541px, i.e. past the threshold |

Nothing else in the 660-line page moved. Regenerated with
`AXEYUM_RENDER_BLESS=1 cargo test --features html -- preview_page`, per DESIGN's
instructions.

Everything under `render/examples-input/` was REGENERATED by its producer
(`facts_to_docir.py`, `build-certificate-manifest.py`, the two `--emit-run`
binaries); nothing there was hand-edited. 151 of the 324 fact cards changed --
exactly the ones carrying a dependency-neighbourhood figure, whose node labels
and tooltips moved.

## Left for P1

Ordered by what I would do first.

1. **Fact cards are not rendered to HTML anywhere.** The atlas and both pilots
   carry `href`s to `cards/F-*.doc.json`, which the emitter turns into an
   in-page scroll target that does not exist on those pages, so a node that
   looks clickable does nothing. Either render the 324 cards (about 13 MB of
   HTML) or make the atlas a multi-page site. Until then the atlas's navigation
   story is the index table.
2. **A row-selection facet on `BlockTable.from_run`** (`show these k`), so a
   document can present 24 of 397 rows without transcribing them.
3. **Stat-level interpolation** (CERT items 2 and 3): claim statements and
   derivation steps embed measured numbers that are correct because a producer
   read them out of the record, not because anything checks them.
4. **A kernel-inventory snapshot**, so `FormalRef::Kernel` is exercised by the
   corpus rather than merely implemented.
5. `RichText.html` at captions and step fields; `ArtifactRef` fields beyond
   path/sha256; `Provenance.host`/`duration_ms` in the rendered provenance line.
6. **Run records for fact-ledger checkers** (FACTS item 2), which is what would
   let a fact card carry a claim at all.
7. Revise `PROSE_THIS_PAGE` in `build-certificate-manifest.py`: it still
   describes the negative control as being on the page.
8. The `--merror`-scan and the self-containment lint both work on finished
   bytes; a third such pass could assert every `data-href` resolves to an
   element that exists, which is item 1's checker.
