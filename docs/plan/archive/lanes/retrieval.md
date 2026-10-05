# Status: Shape-indexed retrieval (`shape_search`)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, retrieval, 2026-08-27).** See the detail below.

**Track:** Refactor 2026-08-27 — the retrieval gate on marginal cost per theorem
**Phase:** ADR-0608 landed; tool in the tree, controls mutation-verified
**Date:** 2026-08-27

## Summary

Lanes repeatedly declared themselves blocked on a lemma that already existed,
proved, in the tree. Every existing instrument answers *"is this name taken?"*,
which cannot find a thing whose name you do not know.
`crates/axeyum-lean-kernel/examples/shape_search.rs` answers *"does a
declaration of this SHAPE exist, anywhere, under any name?"* over
`Kernel::environment()`, covering **every** declaration kind, and it
distinguishes a genuine zero from a query it was never pointed at.

## Delivered

- `crates/axeyum-lean-kernel/src/shape_index.rs` — the index and query engine.
  Indexes conclusion head, per-hypothesis head **taken under that hypothesis's
  own telescope**, type constants, opt-in value constants, and a canonical type
  shape for duplicate detection.
- `crates/axeyum-lean-kernel/src/shape_index/shape_index_tests.rs` — 19
  controls, each written so that deleting the guard it names turns it red.
- `crates/axeyum-lean-kernel/examples/shape_search.rs` — the CLI.
- `docs/research/09-decisions/adr-0608-…md` — the decision.
- Appendix to `docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md`
  — the audit, the measurements, and the stated blind spots.

## Measured

| | |
|---|---|
| declarations indexed (`--include-constructed`) | 1,797 across 10 prelude groups |
| index build | ~13 s release; `--index-values` adds no measurable cost |
| unit tests | 19, 0.20 s |
| audited "already existed" instances, 2026-08-25 → 08-27 | **17** (reported: 13); 3 landed as real duplicates |
| theorem pairs stating the same proposition under two names | **6**, none previously reported |
| `CReal` names with `_` / internal capital / **both** | 315 / 200 / **114** |

## Next

- Wire `--expect 1` / `--expect-absent` `checker_command`s into facts whose
  evidence is a `Definition`; today those use
  `kernel_declaration_projection --require-declaration`, which is correct but
  requires knowing the exact name.
- Size the inline-step route described in the appendix (index `Kernel::infer`ed
  `Prop`-typed subterms of checked proof values) against the cheaper
  alternative: a lint for `Prop`-typed subterms reused three or more times.
- Decide whether the six duplicate theorem pairs are deduplicated or
  deliberately aliased, and record which.


<!-- plan-section: landed-changes -->

| 2026-08-27 | retrieval | see this lane's detail above |
