# Lane: nested-array-row — outer read-over-write, sized and declined

<!-- plan-section: lane-status -->

**Lane nested-array-row (`DONE`, nested-array-row, 2026-09-13).** ADR-1965 named
**outer read-over-write on a nested array** as the gate holding ALIA's 511 files
and ABV's 423, and said re-sizing it needed a different instrument. That
instrument is built and run. **The gate is worth 0, and no solver code was
written.**

ADR: [ADR-1971](../../research/09-decisions/adr-1971-outer-read-over-write-is-worth-zero-alia-and-abv-are-held-by-satisfiability.md)
· artifact: [`bench-results/nested-array-outer-row-20260913/`](../../../bench-results/nested-array-outer-row-20260913/README.md)
· instrument: [`scripts/nested_array_outer_row_surrogate.py`](../../../scripts/nested_array_outer_row_surrogate.py)

## The sizing came first, and it said do not build

Committed at `675282be2` **before any change under `crates/`**.

The instrument is the **mirror** of ADR-1965's. ADR-1965 turned the outer array
into an uninterpreted sort, which DELETES outer read-over-write — which is why
it refused 33 of 36 ALIA and 12 of 17 ABV winnable files and could say nothing
about them. This one **curries** the outer level (`M : (Array I (Array J E))`
becomes `M_row : I -> (Array J E)`) and performs read-over-write syntactically,
leaving the inner array theory and the quantified inner-array variables the
SV-COMP memory model actually uses. Model-preserving on the accepted fragment;
the reach counts only `unsat`, the direction that holds regardless.

**Two findings, and the first settles it before reach is measured.**

1. **39 of the 53 winnable ALIA + ABV files are SATISFIABLE.** Outer
   read-over-write is a refutation mechanism. The ceiling on the whole gate is
   **220 files, not 934** — and that is if every refutable file fell to it.

       AUFLIRA 186 unsat / 1 sat     AUFNIRA 139 / 0
       ALIA     12 unsat / 24 sat    ABV       2 / 15

2. **Of the refutable remainder it reaches none.** Handed outer read-over-write
   for free, axeyum answers `unknown` on **18 of 18** accepted ALIA files and
   **8 of 9** accepted ABV files. The one ABV refutation is the same file
   ADR-1965's surrogate already reached, and it has **zero outer stores** — so
   the marginal contribution of this gate is **0 on every division**.

   Sharpest form: **5 ALIA files are refutable AND inside the fragment AND had
   read-over-write performed for them. axeyum decided 0 of 5.**

## Why the zero is readable

AUFLIRA and AUFNIRA refuse **187/187** and **139/139** under this surrogate
(their files pass outer arrays to functions), so unlike ADR-1965's instrument
this one has no natural population where it is known to reach anything. Six
fixtures in `controls/` supply the missing opportunity — `c1` and `c6` are
outer-read-over-write refutations it returns `unsat` on, and `c3`/`c4` are
adversarial over **satisfiable** queries so a relaxed `ite` guard or a captured
quantified row would be caught rather than counted. Every fixture's own verdict
is confirmed on the ORIGINAL by z3 **and** cvc5.

Soundness control, z3-on-original against z3-on-surrogate, an opportunity on
every accepted file: **agrees 14 / 14, no opinion 13, CONTRADICTS 0.**

Ten mutations of the instrument, all `killed N`, exit 0; eight kill exactly one
test. The informative row is the index guard of the expansion — deleting it
kills six, because without it every outer write is visible at every outer index
and satisfiable files become surrogate `unsat`.

## What the refusals name instead

The refusal reason is the gate *behind* this one, and it differs by family:

| refusal | ALIA | ABV | AUFLIRA | AUFNIRA |
|---|---:|---:|---:|---:|
| outer array **equality** (extensionality) | 15 | 8 | 0 | 0 |
| outer array passed to a **function** | 0 | 0 | 185 | 129 |
| no nested array at all | 3 | 0 | 2 | 10 |

**Where ALIA's and ABV's files actually are: quantified model construction.**
24 ALIA and 15 ABV winnable files are reference-`sat` — the majority of both
lists. They are `forall`-quantified SV-COMP verification conditions whose answer
is `sat`, and no array capability produces a `sat`. That is a different kind of
work from every nested-array lane so far: ADR-1965 moved 273 verdicts and all
273 were `unsat`.

## One real gap found on the way, sized at zero

`select` through an array-sorted `ite` whose branch is a UF-returned row is
`unknown`; the same query with the `select` pushed through by hand is `unsat`.
`crates/axeyum-rewrite/src/arrays.rs` already has that rewrite and these queries
do not reach it. The sweep's `--distribute` arm sizes closing it at **+0 on
ALIA and +0 on ABV**. Pinned as
`select_through_an_array_ite_on_a_uf_returned_row_is_undecided`.

<!-- plan-section: landed-changes -->

| date | change | evidence |
|---|---|---|
| 2026-09-13 | `675282be2` — the sizing instrument and its sweep, committed before any solver code | `bench-results/nested-array-outer-row-20260913/`, 17 files |
| 2026-09-13 | ADR-1971 — outer read-over-write is worth 0; ALIA and ABV are held by satisfiability | reach 0/18 ALIA, 0 marginal ABV; ceiling 220 not 934 |
| 2026-09-13 | two gate-map rows pinning what the sizing measured | `nested_array_gate_map` 12 tests (was 10) |
| 2026-09-13 | `outer-row-surrogate` mutation suite, 10 guards | all `killed N`, exit 0, 8 kill exactly one |
