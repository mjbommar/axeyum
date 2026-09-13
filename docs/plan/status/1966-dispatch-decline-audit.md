# Lane: dispatch-decline-audit — the exhaustive list of dispatch rungs that return a refusal as a verdict

<!-- plan-section: lane-status -->

**Lane block (`DONE`, dispatch-decline-audit, 2026-09-13).** ADR-1927 fixed
three quantified-ladder rungs that returned a sub-solve's
`SolverError::Unsupported` as the query's verdict, and said its audit "was not
exhaustive"; ADR-1960 then found two more by accident. All four known instances
were found while chasing something else, so this lane enumerated the population
**mechanically** — `scripts/enumerate-dispatch-refusal-propagation.py`, whose
three inputs are all derived from the source. **Baseline: 72 rung-to-sub-solve
propagation sites, 40 with another sub-solve below in the same body.** **Five
are closed (ADR-1966); the sixth — the only one worth files — was built,
measured and REVERTED.** The list is pinned with a `--fail-on-new` ratchet whose
negative control fires on exactly one re-introduced site and passes clean
otherwise.

Measured, per-file A/B of the same binary with and without the guards, arms
interleaved on one pinned core, over 1,606 well-formed rows in eight divisions,
every moved row re-run 3× per arm at 24 s: **`AUFDTLIRA` 90 → 110 decided of
200 (+22 / −2 after re-check), 0 `sat`↔`unsat` flips anywhere**, and all 23 new
verdicts confirmed `unsat` by z3 4.13.3 and cvc5 1.3.4 (23/23 comparable each;
the declared `:status` is comparable on **0 of 23** — these files carry none).

**Every one of those files comes from the site that was reverted**, and this is
the handoff: converting `check_auto_dispatch` → `check_with_datatype_native`
turns **7 assertions red in 4 registered pre-push suites** (`dt_uf_gate`,
`dt_capability_1935`, `dt_constructor_arg_1942`, `dt_valued_result_1946`) owned
by ADR-1920/1935/1942/1946. Three read the refusal MESSAGE out of the `Err`
because it is what the blocker census reads; one pins the `Err` itself; four
then get `Ok(Sat(model))` from a rung below. **Prerequisite that removes 3 of
the 7: carry the datatype rung's own sentence into the final `unknown` instead
of letting the bit-blast tail's `unsupported pure-Rust BV operator DtTest(…)`
become the message.** The A/B, the verification and the per-file rows are
committed so the next lane re-measures nothing.

**Three results a later lane should not have to rediscover.**

1. **A structural hit rate is not reachability.** `AUFLIRA` declares the refused
   shape in 184 of 200 files — the highest of any division — and **186 of 200
   never get past the PARSER** (nested array element sort, ADR-1955). Aiming an
   A/B by what files "contain" produces a confident zero for the wrong reason.
   Aim by the route trail of the fixed binary instead (`guard-firing.sh`).
2. **Site count is not file count.** The one fixed site whose firing population
   was identified BY NAME — `abv-online-cdclt`, 6 of 200 `QF_ABV` files, refusing
   an array shape while the array fast path sits immediately below it — yields
   **0 verdicts** on that complete population at 24 s.
3. **The cost is not confined to the queries whose refusal is converted.** The
   `UFLIA` control cannot trigger any guard (200/200 reach the rung, 0/200 can
   refuse it) and still loses one file of 200 reproducibly: the ladder reaches
   `q:egraph`, which eats 19.3 s, so `q:mbqi-quick` — which decided it in 2.0 s
   — never runs.

**Open, sized, named.** (a) The datatype site above: +22 files, verified, behind
7 named assertions and one prerequisite. (b) The
enumerator is exhaustive for `SolverError::Unsupported` only; the
`Unknown`-that-means-refusal class is a separate population it cannot see, and
ADR-1960's second site is in it. (c) The `uf-nra` guard fires 0 times on all 58
`QF_UFNRA` files (route entered 3 times) and no test kills it — kept as correct
by the rule, claimed as evidence of nothing. (d) ADR-1960 and
`real_element_array_row.rs` are NOT on `main` as of `f9075838e`; this lane did
not touch the two sites that ADR names, to avoid colliding with that unmerged
branch.

<!-- plan-section: landed-changes -->

| 2026-09-13 | `b47972ab9` | ADR-1966: the mechanical enumeration of dispatch refusal-propagation sites (72 baseline, 40 with a rung below), five converted to declines, `dispatch_rung_refusal_declines` suite gated in `hooks/pre-push`, and the largest site measured at +22/−2 and left in place with its measurement. |
