# 07 -- R-notes: the two round-1 research questions

Lane DESIGN, round 1, 2026-08-21. Both questions were timeboxed surveys via
SerpAPI and page fetches; both close with a decision that is implemented, not
merely recommended. Sources were read on 2026-08-21 -- re-check before
depending on a version number.

---

## R-a -- Layered DAG layout for the atlas, in pure Rust

**Decision: write it. `render/src/layout.rs`, ~530 lines including tests, zero
dependencies beyond `std`.** The classical four-phase pipeline, with one
deliberate substitution in the coordinate phase (below).

### What the survey found

| crate | version / date | deps | Sugiyama? | gives coordinates? | verdict |
|---|---|---|---|---|---|
| `rust-sugiyama` 0.4.0 | 2025-09-21, MIT | `petgraph`, `log` | yes, full 4-phase (network simplex, BK) | node centres only | **filters dummy vertices out of the returned layout** (`src/algorithm/mod.rs`, `.filter(|(v, _)| !graph[*v].is_dummy)`) -- so long-edge polylines are yours to re-derive, which is most of what you would be buying |
| `layout-rs` 0.1.3 | 2025-04-24, MIT, 0 required deps | -- | yes (`topo/placer/bk.rs`) | only through a `RenderBackend` trait | DOT-parser-shaped API; coordinates must be reverse-engineered out of `draw_rect`/`draw_arrow` callbacks |
| `graphviz-rust` 0.9.8 | 2026-05-03 | `pest`, `tempfile` | -- | -- | **shells out to the `dot` binary**; a C binary is not self-contained and is not on every fleet host |
| `dugong`, `dagre` (kookyleo), `mermaid-dagre`, `dagre-dgl-rs`, ... | 2026, all 0.1.x / alpha | small | claim dagre ports | ? | brand-new, low downloads, no audit history; not a dependency for a soundness-adjacent repo |
| `petgraph` 0.8.3 | 2025-09-30 | -- | **no layout at all** | -- | modules are `acyclic, adj, algo, csr, data, dot, graph, ...`; `dot` emits DOT *text*. `algo::greedy_feedback_arc_set` is the one borrowable piece |
| `fdg` / `fdg-sim`, `tabbycat` | 2022 | -- | force-directed / DOT generation | -- | stale, wrong family |

So the honest options were "take a crate and write the edge routing anyway" or
"write ~450 lines". The graphs are 10 to ~325 nodes; at that size every phase is
sub-millisecond, and the whole file is auditable in one sitting -- which matters
more here than in most places, because a layout bug that overlaps two boxes is
a *readability* defect while a dependency is a supply-chain surface on a
document format we intend to publish.

### The pipeline, as implemented

Modelled on `nulab/autog`'s phase split (Go, MIT -- the clearest small
reference, and the only one that exposes an edge-routing phase) and on
`dagrejs/dagre`'s `lib/` (TypeScript, MIT), both read 2026-08-21.

1. **Acyclic.** Iterative DFS; edges into a gray vertex are reversed and the
   reversal remembered, so an edge is always emitted in the caller's direction
   with a `reversed` flag. The ledger DAG needs none of this; it is here so a
   cyclic input degrades to a drawing instead of a panic.
2. **Layering: longest path.** `layer(v) = 1 + max layer(pred)`, by Kahn in
   index order. dagre defaults to network simplex and its own source calls
   longest-path *"a fast and simple ranker, but results are far from optimal"* --
   true, and irrelevant at this size, where the difference is a slightly taller
   drawing. Longest path also has the property the atlas wants: a fact is drawn
   strictly below everything it rests on, so "what does this depend on" is
   "what is above it", with no exceptions to explain.
3. **Dummy chains.** Every edge spanning more than one layer is subdivided,
   one zero-size dummy per intermediate layer (dagre `lib/normalize.ts`). The
   chain is kept, and its final coordinates ARE the edge's bend points -- this
   is the part the surveyed Rust crates throw away.
4. **Ordering: median sweeps + transpose.** The Gansner median heuristic (empty
   neighbour set -> keep position; odd -> middle; two -> mean; even ->
   interpolate by left/right spread), alternating down/up, followed by an
   adjacent-transpose pass that swaps neighbours when that lowers the local
   crossing count. The best ordering seen is kept.
   Two corrections to the brief I started from: dagre uses **barycentre**, not
   median, and it does **not** run a fixed 8 iterations -- its loop is
   `for (i = 0, lastBest = 0; lastBest < 4; ++i, ++lastBest)`, i.e. sweep until
   four consecutive sweeps fail to improve. We cap at 12 instead, because a
   fixed budget is trivially deterministic and determinism is a repository-wide
   promise; keeping the best-so-far makes the cap safe.
   The initial order is a DFS from the sources (dagre's `initOrder`), not index
   order: the sweeps are local and cannot undo a bad global interleaving.
5. **Coordinates: weighted isotonic regression, not Brandes-Koepf.**
   This is the one place the implementation departs from the standard advice,
   and it is a simplification rather than a shortcut.

   Brandes & Koepf (*Fast and Simple Horizontal Coordinate Assignment*,
   <https://link.springer.com/content/pdf/10.1007/3-540-45848-4_3>) is the
   textbook answer and is ~450-560 lines in every implementation checked
   (dagre's `bk.ts` 20.8 KB; `nulab/autog`'s `brandes_koepf.go` 14.8 KB).
   It also has a **published erratum**, <https://arxiv.org/abs/2008.01252>,
   describing two flaws, one of which the authors say *"requires a non-trivial
   adaptation"*; most implementations carry ad-hoc patches instead.
   Adopting 500 lines of subtle, known-buggy geometry for a 33-node figure is a
   bad trade.

   The alternative usually suggested -- a few passes of "move each node toward
   the median of its neighbours, then shove overlaps apart" -- is a heuristic
   for a problem that has an exact solution. Fix the left-to-right order (phase
   4 already did), and placing one layer is:

       minimise  sum_i w_i (x_i - d_i)^2
       s.t.      x_{i+1} - x_i >= gap_i

   with `d_i` the median of the node's neighbours in the adjacent layer and
   `gap_i` the minimum centre-to-centre distance. Substituting
   `y_i = x_i - sum_{j<i} gap_j` turns the constraints into "`y` nondecreasing",
   which is weighted isotonic regression, solved **exactly** by
   pool-adjacent-violators in linear time. That is ~40 lines
   (`isotonic_place`), it is optimal for the objective rather than approximate,
   and giving dummy nodes a higher weight (`dummy_weight`, default 6) is how
   long edges come out straight. Six alternating down/up passes.

   Tests pin the properties this is supposed to buy: a pure chain draws as a
   straight vertical line; a parent lands on the centre of its three children;
   a heavier node ends closer to its target than a lighter one when they
   conflict.

6. **Edges out.** Polyline from the source box's bottom, through the dummy
   centres, to the target box's top; `edge_path_d` emits a straight `L` when
   the segment is vertical and a smooth cubic otherwise. Arrowheads are drawn
   as computed geometry, not as an SVG `<marker>`, so several graphs in one
   document cannot collide on a shared element id.

Plus `reachability()`: ancestor and descendant sets by bitset closure over the
topological order. The HTML emitter bakes them into `data-anc` / `data-desc`,
which is why the hover interaction is ~30 lines of class toggling and needs no
graph code in the browser.

Determinism: every tie broken by index, every sort stable, no hash container
iterated. `layout_is_deterministic` compares two full layouts of a 12-node
graph for structural equality.

Measured on the preview corpus (33 nodes, 49 edges, 7 layers): 47 crossings,
sub-millisecond, drawing 1160 x 460 units.

### References worth keeping

- `nulab/autog` <https://github.com/nulab/autog> -- five named phases, one
  directory each, including the `phase5/` edge routing neither Rust crate has.
- `dagrejs/dagre` `lib/normalize.ts` (2.9 KB) and `lib/order/barycenter.ts`
  (885 B) -- each about thirty lines and directly portable.
- `paddison/rust-sugiyama` `src/algorithm/p0..p3` -- idiomatic Rust over
  petgraph; worth reading even though we did not depend on it.
- Brandes-Koepf erratum <https://arxiv.org/abs/2008.01252> -- read this first
  if anyone ever proposes adding BK here.

---

## R-b -- Mathematics in a self-contained page, no Node

**Decision: MathML Core, generated at build time, from a small LaTeX subset
implemented in `emit_html.rs` (`latex_to_mathml`). No font is embedded and no
converter crate is a dependency yet.**

### Why MathML rather than Unicode or SVG

- **Support is not the problem it was.** caniuse.com/mathml reports **94.31% of
  global usage** (data July 2026) and labels it Baseline *widely available*;
  MDN dates MathML Core Baseline to **January 2023**, when Chrome 109 shipped
  Igalia's implementation
  (<https://www.igalia.com/2023/01/10/Igalia-Brings-MathML-Back-to-Chromium.html>).
  Firefox has always had it; Safari since 10. The constructs the P0 corpus needs
  -- `msub`, `msup`, `mfrac`, `mrow`, `mo` -- are the least contested part of the
  spec; Chromium's omissions are `menclose`, elementary-math layout and
  `mmultiscripts` corners.
- **Dark mode is free.** MathML elements are CSS boxes and inherit `color`, so
  the `prefers-color-scheme` tokens already recolour every formula. Option C
  (pre-rendered SVG) does not: matplotlib mathtext hardcodes fill colours, so
  every formula would need post-processing to `currentColor`.
- **It is the only option with an accessibility story.** VoiceOver reads MathML
  natively; NVDA reads it with the MathCAT add-on. Unicode best-effort and
  inlined SVG give assistive technology glyph soup or a hand-written
  `aria-label`.
- **Size.** Measured locally with matplotlib 3.10.7 and the `svg` backend, one
  inlined formula is 2-7 KB (`$x^2$` 2,084 B; a sum with a floor function
  6,530 B). Fifty formulas is 150-350 KB of paths, against a few hundred bytes
  each of MathML. Two independently generated SVGs also share `id="figure_1"`,
  `"patch_1"` -- duplicate ids in one document, which would have to be rewritten
  per formula.

The one real gap: **Chromium ships no MATH-table font**, so `mo stretchy`
silently fails to grow -- a documented, measured symptom
(<https://www.gilesthomas.com/2025/02/mathml-fonts-on-chromium-based-browsers>,
2025-02-16: matrix parentheses render one line high). Two consequences, both
taken:

- `--font-math` is a fallback chain (`"STIX Two Math", "Cambria Math",
  "Latin Modern Math", <the prose serif>`) with no `@font-face`. Embedding a
  subsetted STIX Two Math as a base64 data URI is the known fix and stays
  available; it is not worth ~100 KB in every file for a corpus that has no
  stretchy delimiters.
- The converter emits floor, ceiling and angle brackets with
  `stretchy="false"` explicitly, so they render at text size everywhere rather
  than depending on a font that may be absent.

### Why not a converter crate (yet)

| candidate | version / date | notes |
|---|---|---|
| `math-core` (ex-`latex2mmlc`) | 0.7.0, 2026-07-03, MIT | explicitly targets MathML *Core*, KaTeX-comparable coverage, ships a `mathmlfixes.css`; ~49K SLoC, deps `phf`/`strum`/`rustc-hash`/`memchr`. Young: 4,824 total downloads. |
| `pulldown-latex` | 0.8.0, 2026-07-28, MIT | leanest -- one optional dep (`regex`); library only |
| `latex2mathml` (Rust, osanshouo) | 0.2.3, ~6 years old | unmaintained; `math-core` is its successor |
| `latex2mathml` (PyPI) | 3.81.0, MIT, zero runtime deps | the most battle-tested overall (~1.14M downloads/week) |

Any of the top three would satisfy the no-C-dependency rule. The reason none is
a dependency today is scope: the P0 corpus needs subscripts, superscripts,
fractions, floor brackets, `\gcd`, relations and Greek letters, and that is
~200 lines with total control over the failure mode. **The failure mode is the
argument.** `latex_to_mathml` returns `(markup, understood)`, and an
unrecognised command renders as a visible `<merror>` with the command name in
it, never as an approximation -- because a formula silently rendered wrong is
precisely the drift this strand exists to kill, and a general converter's
graceful degradation is the wrong behaviour for a document that is supposed to
be a checker output. When the corpus outgrows the subset, adopt `math-core` (or
`pulldown-latex` if dependency weight decides it), keep the `<merror>` contract
by checking its error channel, and record the swap in an ADR.

Other decisions inside the subset:

- Output is wrapped in `<semantics>` with
  `<annotation encoding="application/x-tex">` and an `alttext` attribute, so the
  LaTeX source survives copy-paste, stays greppable in the emitted file, and
  gives a non-MathML engine something to show.
- `-` becomes U+2212 MINUS SIGN, not the hyphen, in math context.
- Everything is emitted as ASCII numeric character references (repository rule),
  so `&#x2264;` rather than a literal glyph.
- No `xmlns` attribute: it is optional for inline MathML in HTML5, and omitting
  it means the self-containment lint does not need an allowlist for the one
  `http://www.w3.org/1998/Math/MathML` URL that would otherwise appear -- a lint
  with no exceptions is a lint nobody argues with.

### Notable: there is no zero-JS fallback pattern

Nobody has one. arXiv's own issue asking for exactly this
(arXiv/html_feedback#4631, opened 2025-08-20) is still open and the proposed
answer is "MathJax/KaTeX fallback", i.e. JavaScript, which this strand
excludes. W3C's `mathml-polyfills` are also JavaScript. Real MathML-only static
sites exist and accept the 94% floor; so do we, with the annotation and
`alttext` as the degradation.
