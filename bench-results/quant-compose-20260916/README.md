# QUANT-COMPOSE: sizing the four OFF quantifier levers before composing them

**This round was closed early by the coordinator after the sizing and the
reading half of the design deliverable.** The 53-core stacked sweep, the
800-file pinned A/B, the held-out draw and any Rust **did not run**. Nothing
here is a verdict measurement. The full write-up is
[`docs/plan/status/quant-compose.md`](../../docs/plan/status/quant-compose.md).

## What the lane was asked

Compose ADR-2120 (`AXEYUM_QINST_POSITIVE_PATH`), ADR-2127
(`AXEYUM_MACRO_INLINE`), ADR-2130 (`AXEYUM_QINST_GROUND_SESSION`) and ADR-2133
(`AXEYUM_QINST_GEN_LADDER`) on ADR-2113's 53 reference-minimal `UFLIA` cores.
Each ships OFF, each was measured alone, and each ADR reports "necessary, not
sufficient". The hypothesis: the composition moves verdicts no single lever
moves, because each removes a different link of one chain.

## What this directory holds

| file | what it is |
|---|---|
| `build.sh` | builds ONE `smtcomp_cli` into a private target dir and **refuses it** unless no `crates/**/*.rs` is newer than the binary, then prints its sha256. Every arm of the cancelled sweep was to be the same bytes under a different environment. Ran: sha256 `1ca58672c11008f8a679df7868cbf77a62a3e0f86606b0f39a63a07536ba1de2` at `4f81de9c1`. |
| `sizing.py` | re-derives the `UFLIA` / `AUFDTLIRA` baselines from row data — our decided counts from the Tier-1 ledger, z3/cvc5/union from the head-to-head TSVs — and checks that all three sources carry the *same* 200-file population per division. |
| `check-our-citations.py` | 37 `file:line` claims about `crates/axeyum-solver/src/`. **Exits 1 on any miss**, prints the line it actually found, and points at the true line. |
| `check-reference-citations.py` | 34 `file:line` claims about the gitignored `references/z3` and `references/cvc5` clones (absolute path into the main checkout — a worktree has no `references/`). Same contract. |

Both citation checkers exist because a `file:line` claim renders identically
whether or not it points anywhere, and this lane's entire output is such
claims. On their first honest run they failed **13 of 71** — 10 of my own
(including the two lines the nested-activation argument rests on) and 3 that
arrived from a delegated reading which had itself asserted "all line numbers
verified by printing". Both now report `BAD=0`.

## How to run them

```sh
python3 bench-results/quant-compose-20260916/sizing.py
python3 bench-results/quant-compose-20260916/check-our-citations.py
python3 bench-results/quant-compose-20260916/check-reference-citations.py
bash   bench-results/quant-compose-20260916/build.sh compose
```

The first three are pure reads and take under a second. `check-reference-citations.py`
needs `references/z3` and `references/cvc5` populated
(`scripts/fetch-references.sh`) and hardcodes the main checkout's path, so it
fails loudly rather than silently passing on a host without them — an absent
clone reports `FAIL … No such file`, never `BAD=0`.

## The headline numbers, re-derived

| division | ours | z3 | cvc5 | best-ref (union) |
|---|---:|---:|---:|---:|
| `UFLIA` | 86 / 200 | 139 | 142 | **144** |
| `AUFDTLIRA` | 119 / 200 | 176 | 176 | 176 |

Ours from `bench-results/ledger/t1-<div>-db31113fa.tsv` (200 rows, one arm, one
`binary_sha`) — **a snapshot 313 commits behind this branch**, 84 of them in
`crates/axeyum-solver/src`, not a measurement of this tree. References from
`bench-results/six-divisions-headtohead-20260912/UFLIA.tsv` and
`bench-results/dt-divisions-headtohead-20260912/AUFDTLIRA.tsv`.

**`UFLIA`'s standing "vs cvc5 144" is a mis-attribution**: cvc5 alone decides
**142**, z3 **139**, and **144 is their union** — the `best ref` column, which
no single reference solver reaches.

## The nested-activation gap, in one paragraph

z3 and cvc5 both get nested activation for free by asserting the instance back
into the SAT/theory layer: z3 re-internalizes the clause `¬q ∨ body`
(`qi_queue.cpp:288`, `:336`), so a `forall` exposed by instantiation acquires
its own `bool_var` (`smt_internalizer.cpp:656`) and activates on assignment
(`smt_context.cpp:1482` → `:1485` → `smt_quantifier.cpp:818`, `:849`); cvc5
routes it through `preNotifyFact` into a context-dependent asserted list
(`theory_quantifiers.cpp:173`, `:182` → `first_order_model.cpp:95`). We have no
assertion-back step. A nested universal is matched, its tuples computed, and
then kept or dropped on whether its registration carries a `PositiveContext`
(`qinst_egraph.rs:7279` vs `:7294`) — and that context is forced to `None` for
an entire subtree the moment the walk enters a `forall` body
(`qinst_egraph.rs:1948`). **So ADR-2120's lever covers a universal nested under
`and`/`or`/`not`/`=>`/`ite`, and does not cover one nested inside another
universal's binder — and no level setting can reach it**, because `:1948`
passes `None` before any level is consulted, and the checker refuses a crossed
binder on soundness grounds anyway.

**This is a reading, not the decision the brief asked for.** The fixture that
was to decide it was not built. How much of QUANT-REACH-DIFF's 476-instance
NESTED class actually has this shape is unmeasured.
