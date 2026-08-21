# Render strand (2026-08): reader-facing export of Axeyum artifacts

Goal: Axeyum artifacts -- CAS reports, SMT/SAT evidence, kernel theorems,
fact-ledger entries, and whole integrated projects -- render into
beautiful, reader-friendly documents in three formats (Markdown, LaTeX,
self-contained static HTML), without ever becoming able to lie.

Identity, one sentence: **a rendered document is a checker output, not
prose about one.** The renderer is fail-closed: a claim whose evidence did
not run green cannot render as established.

Motivating incident (2026-08-20/21): the NoH-p2 paper
(mjbommar/newton-over-hodge-char2) was produced from machine-checked
results by agents *hand-transcribing* every number into LaTeX -- the exact
drift class this stack exists to kill, reintroduced at the last step. Three
normalization errors were corrected across documents during that project;
single-sourcing renders that class structurally impossible.

## Constraints (from the project owner, 2026-08-21)

- Rust and Python only as implementation languages.
- Output assets: Markdown, LaTeX, self-contained static HTML/CSS/JS,
  optional WASM (the repo already ships wasm32 targets, ADR-0017).
- NO live Node frontend or backend; no Node build chain. Vendored
  single-file JS is acceptable only if truly self-contained; prefer
  generating SVG/JS from Rust.
- Markdown and LaTeX must support verbosity control (hide detail, link to
  file); HTML must be beautifully interactive.

## Files

- `01-goals-and-requirements.md` -- the two rendering products (system,
  result), format requirements, the fail-closed law, non-goals.
- `02-prior-art.md` -- survey (Alectryon, Isabelle document preparation,
  leanblueprint, Verso, sTeX/OMDoc, MyST/Quarto, Distill; SMT/SAT gap),
  with what to steal from each.
- `03-architecture.md` -- the Doc-IR, provenance and evidence binding,
  verbosity tags, emitters, checked references, determinism, crate plan.
- `04-prototype-plan.md` -- P0 pilot scope, exit criteria, test strategy
  (golden files, negative tests, mutation discipline).
- `05-html-interactivity.md` -- static-HTML design: no frameworks,
  Rust-generated SVG, plain-JS toggles, the WASM in-browser re-verify
  showcase.
- `06-roadmap.md` -- phases P0-P4 with tasks, sizing, exit criteria,
  risks, and the NoH-paper retrofit as the integration pilot.

## Standing rules for this strand

Same as everywhere: decisions via ADR (a new crate and any public evidence
format need one -- see 03, section "Crate and ADR plan"); generated views
are never hand-edited; every checker introduced here must be demonstrably
able to fail (delete-one-guard test discipline).
