# 01 -- Goals and requirements

## Two products, one machinery

**R1 -- rendering the SYSTEM.** A derivation as a document: what Axeyum
did. Applies to: rewrite/canonicalizer traces, CAS report computations
(the gf2/acb/noh report style), solver routes (lowering chain, backend,
proof/model production), kernel admissions (statement, proof-term size,
axiom footprint), Lean-export cross-checks. The reader experience is
Alectryon-like: prose interleaved with captured, foldable machine steps.

**R2 -- rendering the RESULT.** The established mathematics as a document:
fact cards, theorem pages, an atlas over the fact ledger with its
dependency DAG, and the "paper genre" -- an integrated project (like
NoH-p2) whose claim-bearing content is generated, not transcribed.

Both consume the same Document IR; they differ as genres (emitter
configurations), not as systems.

## Format requirements

| | Markdown | LaTeX | HTML |
|---|---|---|---|
| Audience | repos, GitHub | papers, arXiv | atlas, showcase |
| Verbosity | `<details>` folds + link-to-file | keep / fold-to-appendix / drop-with-\href, Isabelle-style tags | live toggles |
| Claims | badge text + link to evidence | badge macro + footnoted provenance | interactive certificate box |
| Figures | pre-rendered SVG/PNG links | TikZ or included PDF/SVG | inline SVG, hover states |
| Self-contained | yes | yes (arXiv-safe) | single file, zero external requests |

## Verbosity model (applies to MD and LaTeX; HTML makes it live)

Every block carries a tag: `essential` (always shown), `detail` (folded:
MD `<details>`, LaTeX appendix/fold, HTML collapsed), `archive` (dropped
from the document; rendered as a link to the file/artifact that holds it).
Tags are data on the IR block, set by the producer and overridable by the
document assembly -- one source can emit a terse README and a full report.

## The fail-closed law (non-negotiable)

1. A `Claim` block MUST carry >= 1 evidence reference. Rendering a claim
   with no evidence is a build error, not a warning.
2. An evidence reference resolves to a recorded run (generator, command,
   input hashes, exit status). Exit status != 0 renders the claim in its
   failure styling (REFUTED/OPEN); a strict build mode makes it a build
   error. There is no styling path from red evidence to green claim.
3. Statements of record (theorems, facts) are pulled by checked reference
   from the fact ledger / kernel inventory -- never inlined by hand. A
   dangling reference is a build error (Isabelle antiquotation semantics).
4. Determinism: identical inputs -> byte-identical outputs. No wall-clock
   timestamps (SOURCE_DATE_EPOCH / commit time only), stable iteration
   order everywhere (repo-wide promise).

## Epistemic status vocabulary (renderable badges)

From the fact ledger and this summer's practice:
`PROVED` (kernel-admitted / complete written proof), `CHECKED`
(independently replayed evidence), `EVIDENCE` (finite computation, no
universal credit), `ADVISORY` (non-comparable run), `REFUTED` (witness),
`OPEN`. Two axes where applicable (epistemic vs external), as in
`artifacts/ontology/fact.schema.json`. The renderer takes these from data;
it never infers or upgrades them.

## Non-goals (for this strand)

- Not a notebook/REPL environment (no live kernels, per constraints).
- Not a WYSIWYG editor.
- Not a replacement for prose: humans still write the narrative blocks;
  the system owns every number, statement, table, figure, and badge.
- No Node toolchain anywhere in the build.
