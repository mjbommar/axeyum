# Lane s11a — UF / QF_UF Ackermann + declared-sort CEGAR cap

<!-- plan-section: lane-status -->

Status: **landed, partially measured.** The census's cause attribution for 67 of
the 70 files does not survive a front-door re-measurement; the cap genuinely
blocks 3, and those 3 now decide. The full 200-file QF_UF / UF regression sweeps
were **not run** (see "Gates and what did not run").

Plan anchor: `docs/plan/smt-parity-plan-2026-09-05.md` §2.5, §4 row S11.
Census: `docs/research/11-design-review/2026-09-05-parity-loss-census.md`
(QF_UF 38 files, UF 32 files).
Measured note: `docs/research/11-design-review/2026-09-06-s11a-uf-ackermann-measured.md`.

## 1. Why the 70 files reach the Ackermann routes instead of `euf-online`

Short answer: **35 of them do not.** `euf-online` is already tried first, and on
most of these files it is the route that spends the budget. The census's
per-file `class` is the message of the *last* route in the trace, and on this
family the last route is a millisecond-scale tail after the budget is gone.

`crates/axeyum-solver/src/auto.rs::dispatch_uf_fast_paths` orders the UF ladder
as: `uf-arith-lazy-overbound` (arithmetic-sorted functions only) →
**`euf-online`** (`euf_egraph::check_qf_uf_online_cdclt`, the backtrackable
congruence-closure theory on the CDCL(T) driver) → `dispatch_ufbv_online` →
`euf-offline` → eager Ackermann elimination (`qf-bv`). So the lever the census
names — "try the online e-graph before the eager Ackermann expansion" — is
already the shipped order, and `MAX_ACKERMANN_CONGRUENCE_PAIRS` already gates
only the eager fallback.

`check_qf_uf_online_cdclt` carries **no admission constant of its own**. Its
four decline sites are: no equality atoms; `boolean skeleton outside the online
CDCL(T) encoder`; `timeout in the online CDCL(T) QF_UF driver`; and `model did
not replay (base-sort semantics outside congruence)`. There is nothing to raise.

Per file class, confirmed by `explain_corpus --json --timed-trace` on five
QF_UF and five UF census files and then by the **front door**
(`uf_unknown_probe`, which is `solve_smtlib`):

| Class | Files | What actually happens |
|---|---:|---|
| QF_UF "eager Ackermann would emit N" | 35 | `euf-online` is entered first and **times out** (23.5 s of a 24 s budget, measured). The `qf-bv` Ackermann decline is a 0.3–15 ms tail. The cap is not the binding constraint. |
| QF_UF "declared-sort lazy CEGAR refuses N (bound 64)" | 3 | `euf-online` declines fast (`model did not replay`, 20 ms / 1.1 s), `euf-offline` says `boolean skeleton undecided`, then the 64-pair bound fires **with 21–24 s of budget unspent**. This is the only class the cap actually blocks. |
| UF (all 32) | 32 | The census class is an artifact of the diagnostic tool. `explain_corpus` runs `check_auto_explained` on the **flat assertion view** and its own banner warns it disagrees with `solve_smtlib` on 134 of 397 files; this is one of those classes. At the front door these files never reach the CEGAR bound: they run the e-matching / MBQI / finite-model ladder (`egraph-seg`, `match-seg`, `nested-quant`, `uf-fmf-probe`) and end at `unknown kind=Incomplete detail: query has quantifiers instantiation does not reach (nested, existential, or non-top-level)`. |

Measured trace excerpt (QF_UF, 24 s budget), the shape behind row 1:

```
probe                    probe       9.6ms  fragment {uf}
dl-online                declined  516.4ms
euf-online               declined  23513.6ms  timeout in the online CDCL(T) QF_UF driver
qf-bv                    declined   14.6ms   eager Ackermann ... 14629 congruence constraints ... bound 64
```

Consequence: raising or removing `MAX_ACKERMANN_CONGRUENCE_PAIRS` /
`MAX_ENCODED_DECLARED_SORT_CEGAR_PAIRS` can move **at most 3 files**, not 70.

## 2. What changed, and why it is not a raised cap

Two changes, needed together — either alone moves nothing.

**(a) `check_qf_ufbv_lazy` no longer discards a replay-confirmed `sat`.** The
route reaches `Sat` only out of `project_replay_build`, which evaluates every
ORIGINAL assertion under the projected (lifted, original-symbol-keyed) model
through the ground evaluator and declines on any non-`true` outcome. It then
threw that `Sat` away unconditionally, on the stated ground that "satisfiability
does not transfer back because the model interprets the encoding". Measured, the
premise is false for the queries that reach it: all three QF_UF files replay
clean and their declared verdict is `sat`. Keeping them is sound for the
ordinary reason — an uninterpreted sort carries no semantics beyond equality and
non-emptiness, so any assignment of distinct tokens is a legitimate
interpretation, and replay certifies that symbols the query needs distinct did
not collide.

**(b) The congruence-pair bound is a parameter, not a constant.** Every measured
failure recorded at its check site is budget theft from an *enclosing* search.
`dispatch_declared_sort_ufbv_lazy` is the terminal rung of the quantifier-free
ladder — `euf-online`, `dispatch_ufbv_online` and `euf-offline` all declined
above it, nothing runs after it — so there is no enclosing search to protect,
and the budget it refuses to spend is discarded, not handed on (214 ms of 24 s
measured). It now passes `DECLARED_SORT_CEGAR_PAIRS_TERMINAL_RUNG` = 16 384; the
public `check_qf_ufbv_lazy` keeps 64 unchanged. Time is bounded by the loop's
own shared deadline; the pair count survives as the memory bound on the
`O(pairs)` preseed scan and lemma pool. This is not a cap raised to buy breadth
with time — the time is time the ladder currently throws away.

## 3. Scoped to S11b, not attempted here

- **UF (32 files) is a quantifier-reach gap, not finite-model finding.** 23 of
  32 end at "quantifiers instantiation does not reach (nested, existential, or
  non-top-level)"; 7 are e-matching budget exhaustion (S1/S2); only 2 are the
  "instantiation is satisfiable" shape a model finder would take. §2.5's named
  UF lever (bounded finite-model finding) does not address a query the
  instantiation engine never reaches.
- **QF_UF's 9 remaining timeouts are `euf-online` search power** (S1/S2).
- **`uf-fmf-probe` costs 1.5 / 8.1 / 17.1 s of a 24 s budget on three of five
  traced UF files, all declining** — worth its own measurement.

## 4. Measured before / after

Interleaved (both binaries on each file back to back, so both arms see the same
machine load), `taskset -c 0-7`, 24 s, front door (`uf_unknown_probe` =
`solve_smtlib`). Artifacts:
`bench-results/s11a-uf-ackermann-20260906/{before,after}/QF_UF.census38.il.tsv`.

**The 38 QF_UF census files**

| | before | after |
|---|---:|---:|
| decided | 27 | **29** |
| PAR-2 (s) | 798.2 | **690.8** |

- gained (3): `QF_UF_Heap_ab_cti_max`, `QF_UF_cambridge.7.prop2_ab_fp_max`,
  `QF_UF_hanoi.3.prop1_ab_br_max` — all `sat`, all matching `declared`, and
  exactly the three files the cap blocks.
- verdict flips: **0**. Verdicts contradicting `declared`: **0** (checked in
  both arms by `summarize.py`).
- one apparent loss, `iso_brn_repgen004.smt2`, is 24 s-boundary noise, not a
  route change: it is `sat` at 23 529 ms in this run's before arm and `Timeout`
  at 24 031 ms in an earlier before arm of the *same* binary. It decides on the
  cliff.

**The 32 UF census files** (before arm only,
`before/UF.census32.tsv`): 0 decided, and none of them reaches the changed
route, so the change cannot move them. Terminal reasons: 23 "quantifiers
instantiation does not reach (nested, existential, or non-top-level)", 7
"quantified solve time budget exhausted after e-matching", 2 "instantiation is
satisfiable".

## Gates and what did not run

Run, foreground, serialized, all with nonzero counts:

| Gate | Result |
|---|---|
| `test -p axeyum-solver --lib --features full` | 1454 passed, 0 failed |
| `--features full --test corpus_regression` | 1 passed |
| `--features full` × 10 euf/uf/aufbv/cdclt suites | 4+8+7+3+7+2+16+2+3 = 52 passed, 0 failed |
| `--features z3 --test qf_uf_differential_fuzz` | 2 passed (0 without the feature — confirmed) |
| `--test progress_frontier --features full -- --test-threads=1`, `taskset -c 0-7` | 12 passed |
| `check --workspace --all-targets` | clean |
| `clippy -p axeyum-solver --all-targets --all-features -- -D warnings` | clean |
| `build --target wasm32-unknown-unknown -p axeyum-solver` | clean |
| `cargo fmt --all --check` | clean |
| `./scripts/check-links.sh` | all links ok |

**Did not run** (session ended before them):

- The full 200-file `bench-results/parity-lists/{QF_UF,UF}.txt` sweeps through
  both arms. The 38-file interleaved sweep covers 37 of the 38 census files and
  shows 0 verdict flips and 0 contradictions of `declared`, but it does **not**
  demonstrate that the 162 QF_UF and 85 UF files already decided keep their
  route and their evidence. That is the outstanding regression gate for this
  change; run it before treating the change as validated.
- The corpus-level mutation demonstration (restore the dispatcher to the
  default bound, rebuild, show the three files decline again with the same
  message). The unit test `lazy_declared_sort_terminal_rung_bound_admits_above_
  the_default` pins the parameter but explicitly does **not** pin the
  dispatcher's choice of it, and says so in its own comment.

## Landed changes

| Commit | What |
|---|---|
| `c37238ce7` | Routing explanation, front-door re-measurement, probe artifacts |
| `0453b664a` | The pair bound becomes a parameter; a replay-confirmed `sat` is no longer discarded |
