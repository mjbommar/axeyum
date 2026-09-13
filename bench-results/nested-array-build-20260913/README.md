# Re-sizing the nested-array prize BEFORE building it

**2026-09-13, lane `nested-array-build`.** Everything here was measured and
committed *before* a line of `crates/` changed, because that is the only order
in which the number can be checked against the build afterwards.

## The question

[ADR-1957](../tier1-divisions-headtohead-20260913/README.md)'s census puts the
nested-array parse refusal in front of a **projected ceiling of 20,399 files**,
of which 18,510 (91%) is AUFLIRA alone. A ceiling is a count of files we
**refuse at the front door**. It says nothing about whether the solver behind
that door would decide them, and this repository has watched that distinction
collapse an estimate five times (143→6, 51→2, 173→10, 27,150→1,135, 19,620→0).

[ADR-1955](../../docs/research/09-decisions/adr-1955-the-nested-array-sort-is-the-first-of-three-gates-and-the-only-one-the-ir-owns.md)
sized the reach by transferring a **family-matched control rate** onto each
division's blocked count, and got ~1,135 — essentially all of it one family of
ABV. For AUFLIRA and AUFNIRA, 95% of the prize, ADR-1955 records in the same
table that *no family-matched control exists*: every blocked file is
`nasa`/`peter`, not one `nasa` file parses, and
[ADR-1960](../../docs/research/09-decisions/README.md) adds that of the AUFLIRA
and AUFNIRA files that *do* parse, `grep -c Array` returns **0**. So the method
that produced ~1,135 has, by its own account, nothing to say about the part
that matters.

This measures it directly instead.

## The instrument: an array-free surrogate, sound for `unsat`

[`nested_array_surrogate.py`](nested_array_surrogate.py) rewrites a benchmark
so it parses **today**, without any IR change:

* each distinct `(Array I (Array J E))` becomes a fresh **uninterpreted** sort
  `NA_k`;
* every `select` whose base has that sort becomes a fresh uninterpreted
  function `na_sel_k : NA_k × I → (Array J E)`.

The outer level loses the array theory and keeps congruence. The inner level is
untouched.

The rewrite **deletes axioms and adds none** — outer extensionality goes,
outer read-over-write goes (and a file that uses a `store` at the outer level is
*refused* by the script rather than rewritten, since that is the axiom being
deleted). Deleting axioms admits more models, so

> **surrogate `unsat` ⟹ original `unsat`.**

The converse fails, so a surrogate `sat` transfers nothing and is reported in
its own column so the reach cannot be misread as a decide rate. 186 of
AUFLIRA's 187 winnable files and 138 of AUFNIRA's 139 carry `:status unsat`, so
the sound direction is the one that covers the population.

`python3 nested_array_surrogate.py --self-test` checks the rewrite on a fixture
with a let-bound carrier, a quantified carrier, a UF returning the carrier, and
a flat row sort that must survive untouched — plus a negative control (an
outer-level `store` must be refused).

## What it found

Over the **pinned full-span winnable lists** of
`bench-results/tier1-divisions-headtohead-20260913/`, at the board's own budget
(24 s, `taskset`-pinned, `AXEYUM_TIMEOUT` 24,000 ms), produced by
[`surrogate-launch.sh`](surrogate-launch.sh) and summarized by
[`surrogate-summarize.py`](surrogate-summarize.py):

| division | winnable | rewritten | refused | ax `unsat` | ax `sat`* | z3 `unsat` | reach | ADR-1957 ceiling | projected |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| AUFLIRA | 187 | 175 | 12 | **141** | 0 | 175 | **80.6%** | 18,510 | 14,914 |
| AUFNIRA | 139 | 121 | 18 | **115** | 0 | 121 | **95.0%** | 955 | 908 |
| ALIA | 36 | **0** | 36 | 0 | 0 | 0 | — | 511 | 0 |
| ABV | 17 | **1** | 16 | 1 | 0 | 1 | 100.0% | 423 | 423 |
| **total** | **379** | **297** | **82** | **257** | 0 | 297 | **86.5%** | **20,399** | **16,245** |

\* a surrogate `sat` transfers nothing; the column exists so the reach is not
read as a decide rate. It is 0 everywhere, which is itself the expected shape
for a population that is 96% `:status unsat`.

**The soundness check on the rewrite passed**: no surrogate `unsat`, from either
solver, lands on a file whose original is `sat` (by declared `:status` or by
z3's own board verdict). 257 axeyum + 297 z3 refutations were checked.

### Why 82 files are refused, and what that costs

| reason | AUFLIRA | AUFNIRA | ALIA | ABV |
|---|---:|---:|---:|---:|
| outer-level `store` (the axiom the rewrite deletes) | 10 | 8 | **33** | 12 |
| no nested array sort in the file at all | 2 | 10 | 3 | 0 |
| more than one distinct nested array sort | 0 | 0 | 0 | 4 |

**ALIA and ABV are essentially outside this instrument**: 33 of 36 ALIA and 12
of 17 ABV winnable files write to the outer array, so the outer read-over-write
axiom is load-bearing and a congruence-only abstraction cannot refute them. The
table above therefore says **nothing** about ALIA's 511 or ABV's 423 — those two
rows are the ones ADR-1955's ABV control was about, and they stay where ADR-1955
left them. The 16,245 is 98% AUFLIRA + AUFNIRA.

## The bracket, and what it is a bracket on

    lifting the parse refusal alone   →  measured after the build, this lane
    congruence-only refutation reach  →  16,245  (95% of it AUFLIRA+AUFNIRA)
    ADR-1957 census ceiling           →  20,399

The middle line is **not a forecast of the build**. It is the answer to a
question about the *files*: does a refutation exist that needs only congruence
through the nested read? For AUFLIRA and AUFNIRA the answer is yes for 86.5% of
the winnable set — which is the fact ADR-1955's family-matched transfer could
not see, because it had no family to transfer from.

Turning that into decided files is a **routing** decision, not a parsing one:
the query has to reach a route that abstracts the outer array as a congruent
uninterpreted function and reports only `unsat` from the abstraction. That is
the same one-directional argument the existing lazy ROW/extensionality CEGAR
already runs on flat arrays — *"the bare abstraction is a RELAXATION so its
`unsat` transfers to the original"* — so the capability is a reach extension of
a route that exists, not a new trust assumption.

Two directions in which 16,245 is still wrong, stated before the build so
neither is a retrofit:

* **Down.** It credits each division the rate measured on its *winnable* set —
  files where a reference decides and we do not. The blocked population is
  larger than the winnable one and no harder-file discount is applied.
* **Up.** It assumes the routing above exists. With only the parse refusal
  lifted and every array route still refusing a nested sort by construction, the
  reach is whatever the measurement after the build says — which is the number
  this lane is obliged to publish next to this one.

## Files

| file | what it is |
|---|---|
| [`nested_array_surrogate.py`](nested_array_surrogate.py) | the rewrite, its soundness argument, and its self-test |
| [`surrogate-sweep.sh`](surrogate-sweep.sh) | one division through axeyum + z3 |
| [`surrogate-launch.sh`](surrogate-launch.sh) | all four, pinned, board budget |
| [`surrogate-summarize.py`](surrogate-summarize.py) | the table above, plus the soundness check |
| `sweep/` | the per-division TSVs (below) |
