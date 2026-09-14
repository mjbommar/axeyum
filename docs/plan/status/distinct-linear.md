# Lane: distinct-linear

Status: **active** — ADR-2000, the linear `distinct` encoding.

Branched from `main` at `2611e14b0` (`git merge-base main <branch>` =
`2611e14b0`, which was main's HEAD at branch time).

## What this lane is

`crates/axeyum-smtlib/src/parse.rs` expands `(distinct t1 … tN)` into
`N(N-1)/2` pairwise disequalities and refuses above
`MAX_DISTINCT_EXPANSION_PAIRS = 65_536`. Lane `QBUDGET` handed over five `UFNIA`
rows that die at the front door in ~0.1 s with no solver run, and proposed the
standard linear encoding through a fresh uninterpreted `f : S → Int`.

This lane sized it corpus-wide, built it behind a lever that ships OFF, and
measured it.

## Landed changes

| commit | what |
|---|---|
| `1e8aa69ae` | the encoding and the `AXEYUM_DISTINCT_LINEAR` lever, shipping OFF |
| `b7f761f70` | 20 tests across two suites; both mutants flip |
| `b439597e9` | the polarity walk — the handoff's scoping fires on ZERO of the 356 files |
| `1688f46b6` | the pre-registered sizing and the A/B / mutation harness |

## The sizing, and the two handoff claims it refuted

The handoff sized the target at **5 files** in one division's pinned 200. The
corpus-wide number is **356** (438,631 files scanned; 28,415 contain `distinct`;
356 carry an application of arity ≥ 363). `UFNIA` 309, `QF_NIA` 35, `QF_LIA` 12;
265 declare `unsat`; the largest application has 65,677 arguments.

Two of the handoff's claims are false, and each would have shipped a rewrite
that never fires:

* "the `distinct` is the whole body of an `(assert …)`" — that shape occurs
  **zero** times in 356 files. 257 are `assert > and`, 52 are
  `assert > let > not > or > not`, 47 sit inside a `let` BINDING. All are
  positive polarity. The shipped site test is a polarity walk, covering 309.
* "nullary uninterpreted constants of an uninterpreted sort" — true of the 257
  `lahiri` files, false of the other 99, which are `Int` (Boogie's UFNIA
  encoding uses `Int` as a universal carrier).

Full measurement and method: `bench-results/distinct-linear-20260913/README.md`.

## Next

The A/B, the mutation control and the decision on the lever's default are in
`bench-results/distinct-linear-20260913/AB.md` and ADR-2000.
