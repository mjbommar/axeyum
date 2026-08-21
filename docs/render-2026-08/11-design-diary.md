# 11 -- DESIGN lane diary

Lane DESIGN, round 1, 2026-08-21. Owns `render/src/emit_html.rs`,
`render/src/layout.rs`, `render/assets/`, `docs/render-2026-08/07-r-notes.md`
and this file. Research decisions live in 07; this file is the design system,
the judgement calls, and what round 2 has to pick up.

## What landed

| file | what it is |
|---|---|
| `render/src/layout.rs` | layered DAG layout, pure Rust, no deps (R-a) |
| `render/src/emit_html.rs` | the HTML emitter: blocks, badges, math, SVG, lint, `HtmlEmitter` |
| `render/assets/style.css` | the design system, inlined at emit time |
| `render/assets/app.js` | reading levels, copy buttons, graph cone, steps player |
| `render/assets/preview/build-preview-doc.py` | builds the demo document FROM the real ledger |
| `render/assets/preview/preview-doc.json` | the demo document (generated) |
| `render/assets/preview/preview.html` | the demo page (generated, golden-tested) |

85 unit tests in the two modules; `cargo clippy --features html` is clean.

## The design system

**Type.** Three families, each with a job. Prose is a serif system stack
(Iowan Old Style / Palatino / Georgia): a document that wants to be read like
an article should not look like a dashboard. Apparatus -- badges, table
headers, captions, metadata, controls -- is the system sans, which is how the
reader tells narrative from machinery at a glance. Machine text is mono, and
mono is load-bearing rather than decorative: a Lean core type or an SMT-LIB
assertion is the *exact* text the kernel checked, so it is rendered verbatim in
`<pre><code>` and deliberately NOT prettified into math. Putting a second,
unchecked rendering of a proposition on the page is the failure this strand
exists to prevent.

Scale: 17px base, 1.62 line height, steps at .75 / .8125 / .875 / 1 / 1.125 /
1.375 / 1.75 / 2.25 rem. Headings are sans and tighter (-0.01em, 1.15-1.25
leading) so a two-line title reads as one object.

**Measure and column.** `--measure: 36rem` (~68 characters at the body serif).
It is in **rem, not ch**, and that was a bug I shipped and then found in a
screenshot: `ch` resolves against the *element's own* font, so a
`max-width: 68ch` rule silently produced a much narrower box on every small-sans
block, and provenance lines drifted into the middle of the page. Units that
depend on inherited context do not belong in a shared layout token.

`<main>` is 68rem wide; each direct child is re-narrowed to the measure with
auto margins, and `.ax-wide` opts back out. This replaced a
`margin-left: 50%; transform: translateX(-50%)` full-bleed trick that worked
until the container width changed and then put a figure off the left edge of
the page. Captions stay at the measure even when their figure is three times
as wide, because a caption is prose.

**Space.** 4px grid, `--sp-1`..`--sp-9`. Cards get `sp-4`/`sp-5` padding;
sections are separated by `sp-5`; headings take `sp-6`/`sp-7` above.

**Colour.** Warm paper (`#fcfcfa`) and near-black ink in light; `#14151a` and
`#e8e6e0` in dark, both defined as tokens on `:root` with the dark set inside
`prefers-color-scheme`. One hue family per epistemic status, each as an
`fg`/`bg` pair that is legible on its own ground:

| status | hue | shape |
|---|---|---|
| proved | green | shield |
| checked | blue | double tick |
| evidence | indigo | filled 2x2 grid |
| computed | violet | triangle |
| empirical | teal | hexagon |
| advisory | amber | tilde bar |
| conjectured | ochre | open diamond |
| refuted | red | cross |
| open | slate | hollow ring |
| axiom | brown | pinned bar |
| *unrecognised* | neutral | question mark |

**Badges carry a shape as well as a colour**, as an inline SVG path inside the
badge. This is not decoration: it is what keeps status readable in greyscale
print and for a colour-blind reader, and it means a screenshot of a badge is
still informative. The badge TEXT is the uppercase status token (`PROVED`), the
same token every emitter prints, because the cross-format property test
recovers it from the bytes.

Note the last row. An unrecognised status renders verbatim in neutral styling;
the emitter never maps an unknown status onto a known one. A renderer that
quietly normalised `sat-unchecked` to `checked` would be a second place a green
badge could come from, and there is a test for exactly that.

**The two-axis presentation.** `here [BADGE] literature [BADGE]`, and when what
we established outruns what the literature has settled, a dashed `NEW RESULT`
marker. On the preview page that fires on `F:rado-r4-a5-b3` and it is the single
most persuasive thing on the page -- the ledger's most interesting property,
made visible without a word of prose.

## Judgement calls worth arguing about

**Emitters are dumb, but they are not silent.** The architecture says all
failure happens in assembly. That is right, and it leaves a gap: an emitter
handed something it does not understand could silently drop it and the document
would just be shorter. So `emit_with_diagnostics` returns a list, every
unrenderable block becomes a loud `ax-unrenderable` box that tells the reader
the document is incomplete, and the preview golden test asserts the list is
empty. The emitter also runs a *defensive* audit of the fail-closed law
(established status with no evidence; red evidence under a green claim) which
can only ever make the page louder -- it never upgrades anything. Assembly
remains the authority; this is a second, independent statement of the same rule.

**A certificate may have no exit status, but not silently.** The rado
certificate genuinely is not re-run per commit -- a four-hour re-check cannot
be a gate, and the fact says so in its `axiom_footprint`. First pass, the
emitter diagnosed it as a defect. The fix is not to relax the check but to make
the absence declarable: `no_exit_reason` renders as an amber "not re-run:
<reason>" chip, neither green nor red. With neither an exit status nor a
reason, the diagnostic still fires.

**Two rendering bugs found by looking at the page, not by testing it.** Both
are the kind this project cares about, and both are now tests:

1. `*emphasis*` ate multiplication signs. `F:nat-gcd-bezout`'s statement is
   `gcd(m, n) + m*mn + n*nn = m*mp + n*np`; naive Markdown emphasis rendered it
   as italics with the `*` **deleted**. A renderer that can silently remove an
   operator from a theorem is exactly the drift this strand exists to kill. The
   fix is CommonMark's flanking rule in miniature: an opening `*` may not follow
   an alphanumeric, and the run must close at a word boundary.
2. The dependency SVG letterboxed inside a tall empty box, because an SVG with
   `width`/`height` attributes under `max-width: 100%` is scaled in one axis
   only. `height: auto`.

Neither was visible from the test suite. Screenshots are a gate here, not a
nicety.

**`--` becomes an em dash.** The one piece of smart punctuation, and it exists
because the source files are ASCII by repository rule: `--` is the only way to
write an em dash in them, and rendering it literally puts a line-breaking double
hyphen mid-sentence. It fires only at a word boundary and only for exactly two
hyphens, so `--flag` and `---` survive.

**Relative links are rendered as text, not as links.** In a single-file
document a repo-relative `href` is a dead link by construction, and a dead link
that looks live is a small lie. They render as `label (`path`)`.

**The self-containment lint is the interesting checker.** Rules: resource
attributes must be a fragment, a `data:` URI, or empty; `href` may be absolute
only on an element carrying `data-external="1"`; any absolute URL anywhere
inside a tag must be on such an element (this catches `data-src="https://..."`,
which the per-attribute rules miss); CSS `url()` must be `data:`; a token
blacklist; and at most one `</style` / `</script` terminator, since a second
means inlined content escaped its element.

Three things learned building it:

- **Tag awareness is required, and it is the *permissive* direction.** Escaped
  prose can legitimately contain the text `src="https://..."`; only an
  attribute inside a real tag can fetch anything. Since all text is escaped
  before output, "is this between an unescaped `<` and `>`" is exact for
  documents this emitter produced.
- **Case matters.** `FORBIDDEN_TOKENS` is lowercase because the haystack is
  lowercased -- a capitalised entry would never match, which is precisely the
  silently-inert-gate failure this repository keeps finding. There is a test
  that `XMLHttpRequest` is caught, and it failed the first time for that reason.
- **The lint tripped on its own documentation.** The stylesheet's header comment
  originally spelled `@import` and `url()` literally and the lint flagged them,
  correctly. The comment now spells the forbidden constructs out in words. A
  lint its own documentation can trip is a lint that is actually looking.

Every rule has a test that injects one violation and asserts the rule name, and
one that asserts a clean document passes.

**No SVG `<marker>`, no `xmlns`.** Arrowheads are computed geometry so two
graphs in one document cannot collide on a shared element id; `xmlns` is
optional for inline SVG and MathML in HTML5, and omitting it means the lint
needs no allowlist for the W3C namespace URLs. A lint with no exceptions is a
lint nobody argues with.

**Interactivity budget.** Four features, each installed in its own `try`/`catch`
so one failure cannot take the others down, and each optional:

- reading level (summary / full / forensic) flips a `body` attribute; the CSS
  gating means that with scripting off the document opens at *full* and nothing
  is hidden;
- copy buttons fall back to selecting the command text;
- the graph cone reads precomputed `data-anc` / `data-desc` -- no traversal in
  the browser, and hover *and* keyboard focus both trigger it;
- the steps player responds to `j`/`k` and to clicks, and the steps are an
  ordinary `<ol>` without it.

Print is the forensic level: controls disappear, every fold opens, external link
targets are printed after the text, cards and steps avoid page breaks.

## Integration with CORE (round 1 status)

CORE landed `render/src/lib.rs` with the `Emitter` contract and the `html`
feature during the round. Rather than defer, I built against it:

- `emit_html::HtmlEmitter` implements `crate::Emitter`, so
  `emitter_for("html")` now returns it and
  `cargo build --features html` compiles clean.
- `normalize_resolved()` translates a serialized `ResolvedDocument` into the
  JSON shape the emitter renders. It works on `serde_json::Value` deliberately:
  the resolved types are CORE's, the translation is what will drift when they
  change, and going through `to_value` keeps it unit-testable in this module.
- Contract point 3 (never branch on `exit_status`) is honoured in the adapter,
  not downstream: a certificate's verdict comes from the resolved
  `claim_status`, and exit status is passed through for display only.
- Contract point 8 (ASCII) is enforced in `esc`/`esc_attr`, which emit numeric
  character references for every non-ASCII character. There is a whole-document
  ASCII test using the glyphs the ledger actually carries.
- Contract point 5: each claim card carries
  `data-claim="<label>" data-status="<UPPERCASE TOKEN>"`, which is the
  machine-recoverable pairing the cross-format test should read.

## For round 2 (INTEGRATE)

1. **Join the cross-format test.** `render/tests/cross_format.rs` is empty. The
   HTML recovery is `data-claim` / `data-status` on `article.card`. If CORE
   prefers a different marker, say so and I will change it -- the point is that
   the three formats must yield the identical set.
2. **`normalize_resolved` is round-1 fidelity, not final.** It maps what I could
   read from `assemble.rs` and `ir.rs` in the time available. Known soft spots,
   in priority order:
   - `RichText.html` (verbatim HTML) is **ignored**. Honouring it means letting
     a producer inject markup, which is currently impossible by construction --
     prose cannot smuggle a tag. If it is to be honoured, it must go through the
     self-containment lint first and be rejected loudly on a finding, the way
     `Figure::Svg` already is.
   - `Statement.show: Vec<StatementField>` (which fields to render) is ignored;
     the emitter renders all of them.
   - `Certificate.artifact_refs` are mapped onto the input-hash table by
     `path`/`sha256`; if `ArtifactRef` carries more, it is being dropped.
   - `PlotType::Bar` has no renderer and falls through to a line.
   - `Provenance` rendering uses `generator` / `command` / `exit_status` only.
   The right fix for all of these is a golden test per resolved block kind,
   which belongs with the manifests round 2 produces.
3. **`render/check.sh` should treat a non-empty diagnostics list as a failure.**
   `emit_with_diagnostics` exists for that; nothing wires it yet.
4. **The preview page is a golden.** After any change to the emitter or the
   stylesheet:
   `python3 render/assets/preview/build-preview-doc.py > render/assets/preview/preview-doc.json`
   then `AXEYUM_RENDER_BLESS=1 cargo test --features html -- preview_page`.
   It also runs `scripts/validate-facts.py` and records its real exit status,
   so the page's own certificate box is a real run.
5. **Look at the rendered page before believing it.** Two of the defects above
   were invisible to the test suite. A headless screenshot pass belongs in the
   round-2 checklist:
   `chrome-headless-shell --no-sandbox --window-size=1300,1700 --screenshot=out.png file://.../preview.html`
6. **Deferred by choice:** a subsetted math font as a data URI (only needed when
   the corpus grows stretchy delimiters); adopting `math-core` when the LaTeX
   subset runs out; Brandes-Koepf coordinates (do not, without reading the
   erratum first -- see 07 R-a).
