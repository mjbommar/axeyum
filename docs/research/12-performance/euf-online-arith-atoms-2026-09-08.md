# `euf-online` was reached, and refused the query it can decide in 2 ms

Lane `euf-online-admission`, 2026-09-08.

The handoff said five `QF_UFLIA` files are `unsat` in 2–13 ms when `euf-online`
runs alone and are lost at a 120 s budget through the normal front door, and that
"the route that solves them instantly is not being admitted at all, inside
`check_auto`". **The route is admitted. It runs. It reaches the query and throws
it away in 1.3 ms**, and the reason is a normalization the dispatcher performs on
its own first line.

## 1. The admission condition, in code

There is no admission bound. The operative branch is the encoder's fall-through:

`crates/axeyum-solver/src/euf_egraph.rs`, `Encoder::encode_app`:

```rust
match (op, lits.as_slice()) {
    (Op::BoolNot, [a]) => { … }
    (Op::BoolAnd, [a, b]) => { … }
    …
    _ => return None,      // <- this
}
```

and `check_qf_uf_online_cdclt`:

```rust
let Some(top) = enc.encode(arena, assertion, &mut clauses) else {
    return CheckResult::Unknown(unknown(
        "boolean skeleton outside the online CDCL(T) encoder",
    ));
};
```

`Op::Lt` has no arm. One arithmetic comparison at Boolean position ends the route
for the whole query — including the part of it the congruence closure already
refutes.

### What puts the comparison at Boolean position

`check_auto_dispatch`'s **first statement** (`crates/axeyum-solver/src/auto.rs`):

```rust
let lifted = lift_arith_ite(arena, assertions)?;
let assertions = &lifted;
```

`lift_arith_ite` hoists each Int/Real `ite(c, a, b)` to a fresh `t` plus
`¬c ∨ t=a` and `c ∨ t=b`. It exists for the arithmetic linearizers, which do not
accept an `ite` inside a term. It is exact and equisatisfiable and it is *the*
right thing for the simplex routes.

For the e-graph deciders it is the opposite. In `medium9.smt2` the condition
`(< (+ x y) 9)` occurs **only** as an `ite` condition nested inside
`(Pred (ite (< …) … …))` — an opaque congruence term, which this encoder never
looks inside. The lift moves it out to the top level, and the route that could
decide the file now cannot encode it.

The dispatcher already knows this distinction and applies it in the other
direction three lines later: `lift_uninterpreted_sort_ite` is run *only* for the
e-graph deciders. Nothing ran the symmetric argument for `lift_arith_ite`.

### The measurement

Binary: `smtcomp_cli`, release, this tree. File:
`QF_UFLIA/mathsat/EufLaArithmetic/medium/medium9.smt2` (declared `unsat`).

| run | result |
|---|---|
| `route_solo --route euf-online` (24 s) | `unsat`, **2 ms** |
| `smtcomp_cli --timeout-ms 24000 --trace` | `unknown` at 25.0 s |

and the route trail's own entry for the route in question:

```json
{"route":"euf-online","outcome":"declined","reason":"incomplete","kind":"other",
 "detail":"boolean skeleton outside the online CDCL(T) encoder",
 "elapsed_ns":1275250}
```

It was reached (after `uf-arith-lazy-overbound` spent 18,007 ms) and it declined
in 1.3 ms.

**The control that pins the cause.** Delete the file's two `ite`-carrying
conjuncts — the query stays `unsat`, since the refutation lives in the tabulated
`Succ`/`Pred`/`Sum` congruences and the first `z = Sum(…)` conjunct — and the
front door decides it:

```
"route":"euf-online","outcome":"decided"
unsat
```

### What it is not

- **Not `check_auto_inner`'s `to_real`/`to_int` normalization**, the candidate
  the handoff nominated. `medium9` is pure `Int`: `relax_coercions` returns
  `had_coercion == false` and `check_auto_inner` goes straight to
  `check_auto_dispatch` without entering that block at all.
- Not preprocessing, route order or budget — the three controls the portfolio
  lane already ran, and this finding is consistent with all three.
- **Not a registry bound.** `note_crossed` has nothing to be wired to here: this
  is a hard "unsupported operator" refusal with no threshold, which is worse than
  a silent bound, not better. The instrument added below is the repair.

## 2. The fix

`Encoder` gains an opt-in `opaque_bool_atoms` arm: a Boolean-sorted application
with no connective arm becomes a **fresh opaque skeleton variable** instead of
failing the encode.

**Soundness.** Replacing an atom with a fresh propositional variable only ADDS
models — every model of the original induces one of the skeleton by giving the
variable the atom's truth value — so `unsat` of the skeleton transfers to the
original. `sat` says nothing and is already replay-gated: `check_qf_uf_online_cdclt`
runs `replays(arena, assertions, &model)` through the ground evaluator on the
ORIGINAL assertions before returning `Sat`. This is the same argument the
pre-existing `bool_apply_atoms` mode already rests on, applied one level further
out. Structural sharing keeps one variable per distinct term (`term_var` is keyed
on the hash-consed `TermId`), so a repeated or negated occurrence stays
consistent.

**The abstraction fires at the DEEPEST failing Boolean node**, because
`encode_app` encodes its arguments through the recursive `encode`, which hits the
same fall-through at their own level: `(and p (< a b))` keeps `p` and abstracts
only the comparison.

**Off for every other route sharing this encoder.** `euf_egraph::Encoder` is used
by `lra_theory`, `lia_theory`, `lia_online`, `dl_online`, `string_theory`,
`ufbv_online` and `qinst_egraph`. Those routes REGISTER their comparisons as
theory atoms, so `encode` finds them by map lookup; silently abstracting one they
failed to register would drop the theory reasoning that is their entire job. The
flag is opt-in and only `check_qf_uf_online_cdclt` sets it.

### The policy, and why the route needed a budget

Abstracting turns a 1.3 ms decline into a route that SPENDS time on every
UF+arithmetic query, and the routes below it — `euf-offline`, `ufbv-online`,
`uf-arith-online` (the online model-based EUF+LIA combination, the architecture
Z3 uses for this division) — run on what it leaves.

`EufOnlineAtomPolicy` is therefore a swappable object with three arms selected by
`AXEYUM_EUF_ONLINE_ATOMS`, plus a thread-local guard for tests:

| arm | env | behaviour |
|---|---|---|
| `Refuse` | `refuse` | the historical behaviour, byte-identical |
| `AbstractSliced` | *(default)* | abstract; on a query where that fired, run under `min(remaining/4, 2 s)` |
| `AbstractWholeBudget` | `whole` | abstract; take the whole remaining budget |

A query that abstracted **nothing** keeps the caller's whole timeout under every
arm, so pure `QF_UF` is unaffected in verdict and in budget. The slice is decided
after the encoding for exactly that reason.

## 3. What it does to the division

Population: `bench-results/parity-lists/QF_UFLIA.txt`, the committed 200-file
parity list — the whole division, not the five files. Protocol identical to
`scripts/parity-run.sh`: 24 s wall, 8 GiB `ulimit -v`, `AXEYUM_TRACE=1`. One
binary, three arms, arm chosen by environment variable
(`scripts/euf-online-atoms-sweep.sh`).

| arm | decided / 200 | vs `refuse` |
|---|---:|---|
| `refuse` (pre-2026-09-08) | **151** | baseline |
| `sliced` (shipped default) | **156** | **+5 / −0** |
| `whole` | **156** | +5 / −0 |

The `refuse` arm reproducing 151 is the check that the baseline is this tree and
not a remembered number: 151 is exactly what `QF_UFLIA` was reported at after the
`MAX_BOOLEAN_ATOMS` 512→8192 and `care-truncate` changes landed earlier the same
day.

The five gained are `medium9`, `medium10`, `medium13`, `medium16`, `medium19`
from `mathsat/EufLaArithmetic/medium/` — the five the handoff named. Each is
`unsat`, each `decided_by=euf-online`, the route itself costing 2–9 ms.

**Nothing was lost and no two arms disagree on any verdict.**
`scripts/euf-online-atoms-compare.py` exits 2 on a cross-arm verdict
disagreement and 1 on a file that stops being decided; it exited 0.

`sliced` and `whole` decide the same set, so the budget slice costs nothing here.
That is what lets the sliced arm ship as the default rather than as the arm that
needs defending.

### What the abstraction costs

The route abstracted on **68 of 200** files. Of those it decided 6 (1–9 ms) and
declined 62 after a median of 8 ms and a maximum of **1,159 ms**; under `refuse`
the same 68 declined after at most 6 ms. Five files bought for up to ~1.2 s spent
on the worst single one, out of budget the routes below it did not need on any
file in this population.

**Neither new bound fired.** `min(remaining/4, 2 s)` is 1.5 s at the 24 s budget
(the route is entered with ~6 s left after the over-bound CEGAR) and 1,159 ms is
under it. The bounds are insurance against a query outside this population, and
this note says so rather than implying a fit.

### The neighbour division, and the reading I nearly published

`QF_UF` is the division this route owns, so a change to its encoder has to be
measured there too. First run, 200-file committed parity list:

| arm | decided / 200 |
|---|---:|
| `refuse` (s7, cores 0–7) | 195 |
| `sliced` (s5, cores 8–15, **beside another sweep on cores 0–7**) | 192 |

**−3 — and it is entirely the host placement.** The three files
(`gensys_brn838`, `gensys_icl591`, `iso_brn_nogen005`) are ones `euf-online`
decides at **21.2 s of a 24 s budget**; on the busier host it ran out of clock.
The counter is what settles it rather than an argument: on all 198 `QF_UF`
queries the route was entered on, `abstracted_queries=0`. Nothing was abstracted,
so `route_timeout` returned the caller's timeout unchanged and **the two arms ran
identical code**.

Re-run of the `sliced` arm on the SAME host and the SAME cores as the baseline:

| arm | decided / 200 | vs `refuse` |
|---|---:|---|
| `refuse` (s7, cores 0–7) | 195 | baseline |
| `sliced` (s7, cores 0–7) | **195** | **+0 / −0** |

Both runs are committed (`QF_UF.sliced.tsv` is the confounded one and is labelled
as such), because a measurement that moved for a reason other than the change is
worth more in the record than out of it.

### Reference frame

Hosts were **not** idle and this is not a timing claim. `s4` (this worktree)
carried 14 other `smtcomp_cli` processes from sibling lanes at load 13–17 of 16
cores throughout; the arms ran on `s5` (`whole`), `s6` (`refuse`) and `s7`
(`sliced`), load 3–4 of 16 at launch, `taskset -c 0-7`, 6 slots each. **The
decide / not-decide bit is what the conclusions rest on**; every millisecond
figure here is advisory.

Data: [`bench-results/euf-online-atoms-20260908/`](../../../bench-results/euf-online-atoms-20260908/README.md).

## 4. The instrument, and the blind spot it had on its first run

The only evidence this decision point existed was the string *"boolean skeleton
outside the online CDCL(T) encoder"* in a decline. It names the encoder. It does
not name the atom, the count, or the policy, and it cannot distinguish "never
entered" from "entered and gave up". `EufOnlineAtomStats` now records
`entered` / `abstracted_queries` / `abstracted_atoms` / `refused` / `policy`,
publishes onto the live board so it survives a watchdog kill, and prints as
`; euf-online-atoms …` under `smtcomp_cli --trace`.

**Its first version was blind to the state it exists to report.** The recording
sat after the encoding finished, so the `Refuse` arm returned early and published
`policy="unset"`, `entered=0`. `the_counters_separate_abstracted_from_refused_from_merely_entered`
failed on its first run and is what found it. That is the shape this repository
keeps meeting: an instrument whose happy path is the only path it measures.

## 5. Gates

| gate | result |
|---|---|
| `--features full --test euf_online_arith_atoms` | 4 tests, 4 passed (NONZERO) |
| `--features full --lib config_registry` | 17 passed |
| `check-config-registry-staleness.py` | 0 — 471 entries, 84 dated, none stale |
| `check-admission-limit-basis.py` | 0 — 143 declarations, all resolve |
| `check-fmt-complete.sh` | 0 — 2,161 files checked |
| `check-merge-hygiene.sh` | PASS |
| `check-links.sh` | all links ok |
| `--features full --test corpus_regression` | 1 test, `corpus_regression_is_sound` ok |
| `--lib --features full -- --test-threads=4` | 1,620 / 1,622 then 1,621 / 1,622 — see below |

The instrument was also verified end to end on the shipped binary, on both arms
and through a watchdog kill:

```
$ AXEYUM_EUF_ONLINE_ATOMS=refuse smtcomp_cli medium9.smt2 --timeout-ms 3000 --trace
; partial euf-online-atoms policy=refuse entered=1 abstracted_queries=0 abstracted_atoms=0 refused=1
unknown
$ AXEYUM_EUF_ONLINE_ATOMS=sliced smtcomp_cli medium9.smt2 --timeout-ms 3000 --trace
euf-online-atoms policy=sliced entered=1 abstracted_queries=1 abstracted_atoms=3 refused=0
unsat
```

Three atoms abstracted, and at a **3 s** budget — not just 24 s — the shipped arm
decides it.

### Two `--lib` failures that are not this change

The full `-p axeyum-solver --lib --features full -- --test-threads=4` sweep
(1,622 tests) reported two failures on a box at load 20 of 16 cores with 16
sibling `smtcomp_cli` processes. Both are load artefacts with documented
mechanisms, and neither can reach this diff:

- `lra::memory_limit_tests::a_multiplier_matrix_over_the_budget_is_refused_before_it_is_allocated`
  — got a WATCHDOG trip ("resident set reached 239 MiB over the 1 MiB
  `memory_limit_mb`") where it wanted the PROJECTION refusal.
  `memory_budget::set_limit_for_test` writes a **process-global** atomic while
  `WATCHDOG_LOCK` only serialises tests inside that one module, so any
  concurrent test in another module can start the sampler against the 1 MiB
  limit. Verified: passes with `--test-threads=1` (7 passed).
- `euf_egraph::tests::check_qf_uf_with_config_is_bounded_by_timeout` — got
  `Unknown("boolean skeleton undecided")` on the 600 s half, in **both** sweeps.
  This exact failure has a commit of its own: `0d10aebac` (2026-07-01, "repair
  the six red CI jobs") raised this budget from 60 s to 600 s because *"the
  solve takes ~50 s on a fast dev box, so 60 s flaked on slower CI runners
  (deadline hit mid-solve → 'boolean skeleton undecided')"*. At load 20 of 16
  cores with 16 sibling solver processes, 600 s is again not enough. It
  exercises `check_qf_uf_with_config`, the **offline** route, which does not
  touch `Encoder` at all: the only two `Encoder::new` sites in `euf_egraph.rs`
  are `check_qf_uf_online_cdclt` (line 1189) and the test-only `run_online_diag`
  (line 2606, flag off, byte-identical). This diff cannot reach it.

The second sweep (1,621 passed, 1 failed) is what separates the two: the LRA one
passed there, which is what a race looks like; the timeout one failed in both,
which is what a too-slow budget looks like.

## 6. What this does not fix

The five files land at **~18.3 s of a 24 s budget**, because
`uf-arith-lazy-overbound` still spends `24000 × 3/4 = 18,006 ms` on them before
the ladder below it runs, and only then does the 2 ms route get its turn. They are
decided, not decided *well*. Two things follow, neither of them this lane's:

- The CEGAR's probe share is a budget question with its own policy
  (`UF_ARITH_LADDER_RESERVE_SHARE`) and its own arm. A file whose answer costs
  2 ms should not need 18 s of someone else's failure first.
- This is the **exact shape** the parallel-portfolio note put in its middle band
  and could not find members for. Five files where one route needs 18 s and
  another needs 2 ms, on one 24 s clock, are five files a two-arm portfolio
  decides in 2 ms — the same argument
  `docs/research/12-performance/the-portfolio-answer-is-not-yet.md` makes from
  `hash_sat_08_05`, with four more members than it had.
