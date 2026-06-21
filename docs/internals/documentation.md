# How This Documentation Is Built (and Why)

This page is the answer to *"what's the right way to do rich, diagram-driven,
interactive docs for a project like this?"* — and the rationale for the stack we
chose over the obvious alternatives (Docusaurus, Verso, Jupyter).

## The stack

| Layer | Tool | Why |
|---|---|---|
| Source | **Markdown** | renders on GitHub *and* compiles to a site — one source, zero lock-in |
| Site | **[mdBook](https://rust-lang.github.io/mdBook/)** | Rust-native (`cargo install mdbook`), built-in search + themes, matches the project's toolchain |
| Flow/architecture diagrams | **[Mermaid](https://mermaid.js.org/)** (```` ```mermaid ````) | text-based, diffable, version-controlled; renders natively on GitHub and via `mdbook-mermaid` |
| Precise structural diagrams | **Graphviz `dot` → committed SVG** ([`assets/`](../assets/)) | exact control for the term-IR DAG and bit-blast circuits where Mermaid is too coarse |
| Interactivity | **WASM solver playground** ([`playground/`](../playground/README.md)) | a *live* solver in the browser — the project already targets `wasm32` |

## Why these, not the alternatives

- **mdBook over Docusaurus / Astro Starlight.** Those are excellent but
  Node-centric and heavier; for a Rust project, mdBook keeps the toolchain
  coherent (`cargo install`, no `node_modules`), and the source stays plain
  Markdown that also reads fine directly on GitHub. We lose some polish; we gain
  simplicity and zero ecosystem drift.
- **Mermaid as the default diagram language.** Diagrams that live as *text* get
  reviewed, diffed, and kept in sync with the code. Binary/exported diagrams rot.
  We only drop to hand-authored SVG when a diagram needs precision Mermaid can't
  express (e.g. a ripple-carry adder, the IR DAG).
- **WASM playground over Jupyter / Verso.**
  - *Jupyter* is the gold standard for executable notebooks, but it needs a
    **kernel server** and a Python/IRust runtime — wrong shape for "open a page
    and try the solver." Our solver is Rust; the natural fit is WebAssembly.
  - *Verso* (Lean's literate-doc tool that compiles docs against verified code)
    is the right *spirit* — executable, trustworthy docs — and a real
    inspiration. But it's Lean-specific. The Axeyum analogue of "executable
    docs" is **compile the actual solver to WASM and run it client-side**: the
    reader runs the *real* engine, no server, no install, and the example can't
    silently drift from the code because it *is* the code.

The result: the same Markdown is readable on GitHub, builds into a searchable
mdBook site, carries maintainable text diagrams, and links to a page where the
real solver runs in your browser.

## Building the site

```sh
# one-time
cargo install mdbook mdbook-mermaid
mdbook-mermaid install .        # writes mermaid.min.js + css, wires book.toml

# build / preview
mdbook build                    # -> book/ (static site)
mdbook serve --open            # live-reload preview
```

`book.toml` sets `src = "docs"` and the curated table of contents is
[`docs/SUMMARY.md`](../SUMMARY.md). The deep `research/`, `plan/`, and `reviews/`
trees are linked from the guide, not inlined, so the book stays a *front door*,
not a dump of the whole repo.

## Building the playground

The WASM bundle is built from the `axeyum-wasm` binding crate; see
[`playground/README.md`](../playground/README.md) for the `wasm-pack` build and
the current status (the binding is scaffolded; the bundle build is gated on the
`wasm32` toolchain + a green workspace).

## Quality bar (enforced for every page)

- Every support claim links to the [capability](../research/08-planning/capability-matrix.md),
  [support](../research/08-planning/support-matrix.md), or
  [trust](../research/08-planning/trust-ledger.md) matrix, or a benchmark artifact.
- Every example is runnable.
- `unknown` is always described as honest incompleteness/resource control, never
  failure.
- Beginner pages define terms (QF_BV, CNF, DRAT, Alethe, MBQI…) before using the
  abbreviation.
- Roadmap claims use concrete fragment milestones, not broad parity language.
