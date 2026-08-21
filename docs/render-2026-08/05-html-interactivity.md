# 05 -- HTML: beautiful, interactive, self-contained, no Node

## Ground rules

- One file per document: CSS and JS inlined, figures as inline SVG,
  fonts system-stack (or none embedded; NO webfont fetches). Zero
  external requests, enforced by lint (04).
- Plain modern JS (no frameworks, no build step). Interactivity budget:
  everything must degrade to readable with JS disabled (`<details>` is
  the base mechanism; JS enhances).
- Dark/light via `prefers-color-scheme` with tokens defined on `:root`.

## Interaction inventory (in order of value)

1. **Verbosity toggles**: `Detail` blocks are `<details>`; a page-level
   control ("reading level: summary / full / forensic") flips classes --
   pure CSS + ~20 lines JS.
2. **Certificate boxes**: collapsed summary (verdict badge, generator,
   exit status) expanding to: input hash table, replay command with a
   copy button, and the raw run-record JSON in a fold.
3. **Dependency graph (atlas)**: SVG GENERATED IN RUST (layered/
   Sugiyama-lite layout over petgraph; our DAGs are small -- tens to low
   hundreds of nodes). Nodes colored by epistemic status; plain-JS hover
   highlights the ancestor/descendant cone; click scrolls to the fact
   card. No d3, no vendored libs.
4. **Steps player (traces)**: Alectryon-style -- each step a row,
   keyboard j/k walks steps, current step's output pane pinned. Pure
   DOM, no state library.
5. **Polygon figures** (Newton/Hodge): Rust-generated SVG with vertices
   as elements carrying data-attrs; hover shows (x, y, slope) tooltip;
   NP-vs-HP contact points emphasized. (The NoH paper's missing figures
   become the first real instances.)
6. **WASM re-verify (the showcase, P2)**: compile a checker to
   wasm32-unknown-unknown (repo already builds this target, ADR-0017;
   candidates in order: the noh_wt certificate core, check_drat on a
   small committed proof, a fact-card replayer). A "Re-verify in your
   browser" button runs the ACTUAL checker on the embedded artifact and
   flips the badge live. Rules: wasm module embedded as base64 data URI
   (self-containment); the page's static badge remains the build-time
   truth -- the button is a demonstration, and a wasm failure renders
   loudly (this button must also be able to fail: ship one deliberately
   broken demo page in tests).

## Aesthetic direction

Distill-like restraint: generous measure (~70ch), real typographic scale,
one accent hue per epistemic status family, tables as the first-class
citizens they are here. Status badges use shape + color (not color
alone). Print stylesheet so the HTML also papers well.

## Anti-goals

No SPA routing, no client-side search index in P0 (grep the repo), no
analytics, no iframes, nothing that phones home -- the self-containment
lint is a trust property, not a style preference.
