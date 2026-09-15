# Lane: lra-trace — what the same simplex does differently on `QF_LRA` (ADR-2111)

<!-- plan-section: lane-status -->

**Lane LRA-TRACE (`WIP`, lra-trace, 2026-09-15).** `QF_LRA` reads ours 107 of
200 against z3 166 — 59 behind — and every reference decides those files with
the same Dutertre–de Moura simplex we ship, so the lane's question was what ours
does differently with a trace on both sides, not which algorithm is missing.

**Census of all 93 undecided rows, four cause channels, 0 without a capture**
(the give-up string alone loses the largest bucket, [ADR-2045]): **40 `rc=134`
allocation aborts, 36 `budget/other`, 7 `incomplete`, 5 `bound-no-decline`, 5
`not-applicable`**. Two structural readings fall out: **34 of 93 are bound
inside `lra.rs` before the simplex gets a system** (21 building the
Fourier–Motzkin unit-multiplier matrix, 11 with the deadline already gone when
the conjunctive decider was entered), and **only 23 of 93 ever reach the online
CDCL(T) engine** — the other 70 contribute nothing to its counters, not a zero.
The **typed decline name types nothing here**: all 36 budget rows carry
`Budget::Other`, which is [ADR-2102]'s empty `decline_names` seen from the
producer side, and typing the six `lra.rs` give-up sites is named as remaining
work rather than done.

**Shape census, with the 107 decided rows as a control in the same table.**
Atoms separate the halves **1,351×** (median 9,462 against 7). **Coefficient
size does not**: max numeral digits median 5 and max 10 in *both* halves, and 0
of 200 rows over 18 digits on either measure, against `i128`'s 38 — so every
arithmetic decline on this population is pivot growth, never the file's own
numbers, and the "big coefficients" reading is dead before a trace is read.

**Three design-difference claims, `file:line` on both sides.** (1) Our tableau
was dense and **none of z3, cvc5, `OpenSMT` or `SMTInterpol` stores a dense
one**, and all four thread the columns too. (2) Theory propagation is not weak
but absent: a median **19** propagations against **836,531** decisions and
**12.2 M atom visits**, because `propagate_bounds` rescans every atom on every
call, while z3 analyses only touched rows and pre-axiomatises the bound ordering
as SAT clauses — we generate no bound axioms at all. (3) The equality hypothesis
(66 of 93 rows ≥50 % equalities, no Gaussian elimination here) is **refuted on
the reference side**: z3 has no `solve_eqs` either and cvc5's is capped at 2.

**Shipped:** `Tableau` is sparse (`row_val` aligned with the `row_nz` index that
already existed, plus a `col_rows` transpose), as the only path, with a
soundness-negative fill-in fixture. The **lever** is the consequence, not the
storage: the online budget reserved 128 MiB — 20 % of 640 MiB — for a structure
now costing ~1.4 MB, and that reserve decides which queries the engine admits;
`TableauReserve` ships **`Dense`**, because ADR-2045's budget raise bought 0
verdicts and five new aborts and ADR-2055's cap turned 18 clean exits into
aborts.

**Next:** the A/B over the six linear-arithmetic divisions and the mover
recheck. The largest unpulled lever is the touched-driven bound scan (claim 2),
which is provably output-equivalent at fixpoint and has an exact control
already written for its sibling filter.

<!-- plan-section: landed-changes -->

| 2026-09-15 | `28280dbfb` | lra-trace: `QF_LRA` shape census — undecided are 1,351x the decided in ATOMS and identical in COEFFICIENT SIZE, with the 107 decided as a control |
| 2026-09-15 | `2b66f2d50` | lra-trace: all 93 undecided rows bucketed over four channels — 40 aborts, 34 die in `lra.rs` before the simplex, 23 reach the online engine |
| 2026-09-15 | `81ed00d56` | lra-trace: the simplex tableau is sparse (nobody else stores a dense one); `TableauReserve` lever ships `Dense` |
