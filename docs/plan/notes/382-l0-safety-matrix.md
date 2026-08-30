# Notes: 382-l0-safety-matrix

Detail moved out of [`../status/382-l0-safety-matrix.md`](../status/382-l0-safety-matrix.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

3. **`generated-unreviewed` is the best-protected population, not the worst.**
   All 1,038 carry a discriminating own-subject checker against 392 of 1,067
   hand-authored rows. What none of them has is any check on
   `formal.statement` — the field their own prose calls authoritative. The
   unreviewed part is the prose; the unprotected part is the formal statement.

## Handoff — what I did NOT do, and what is a hypothesis

Per the standing rule that a handoff's "blocked on X" is a claim about one
route: everything below is what my route did not reach, not a claim that it is
hard.

- **`just check-theorem` was out of scope by instruction** and remains so until
  the receipt schema exists. When it is built, its table must distinguish
  "cites a discriminating command" from "cites a command naming THIS fact's
  subject" — the ledger's own regex fallback would claim 82.4% coverage where
  the explicit bindings support 68.1%, guessing for 302 rows.
- **I did not run `scripts/check-fact-evidence-replay.sh`,** so I have not
  measured whether the cited commands actually pass today. The census reads
  what facts CLAIM; it does not execute their checkers. That is a real gap in
  S0 and the honest place for S6 to start.
- **`per_theorem_footprint` at 59 may be an undercount** for routes I classified
  by command shape rather than by running anything. I did not verify that a
  prelude-wide `--require-axiom-free` fails to bound an individual theorem; I
  only recorded that it is not a per-theorem check.
- `scripts/check-fact-depends-derived.py` was run and exits 0, reporting
  `kernel_facts=2037|named=1868|graph=2021|missing_edges=0` with **169**
  kernel-route facts whose checker command names no theorem, explicitly "not
  enforced". That corroborates the subject-binding gap from a second tool.

## Paths owned by this lane

`scripts/gen-safety-matrix.py`, `artifacts/safety-matrix/`,
`docs/research/09-decisions/adr-0746-*.md`, this file. Registration lines only
in `scripts/check.sh` and `justfile`.
