# ADR-2035 preregistration — the boundary's missing rescue, and why the round cap is not measured

Committed **before** any A/B arm runs. Rules first, values second, as
[ADR-2030] did for its lemma cap.

Branch base: `git merge-base main HEAD` is
`ffaf920cd585300b5c3c854f88db9d8ee8517759`, which **is** local `main`'s HEAD.

## 0. What the split already decided

[`split-populations.txt`](split-populations.txt), committed in `42b5427db`
before any lever existed:

| population | test | n |
|---|---|---:|
| **GROWN** | `sat_candidates >= 1` — a round was admitted past the boundary and returned a model, so the refusal is on a LATER round over a skeleton the lemma batch grew | **10** |
| **BORN-OVER** | `sat_candidates == 0`, `solve_rounds == 1`, `lemmas_added == 0` — the FIRST solve was refused, before a single lemma existed | **12** |

and the census label splits across **two code sites**: 22 of 22 at
`IncrementalArithDpll::solve` (stage `declining before the first SAT round`),
**0** at `arith_dpll_admission_preflight`. Only the second has the
`oversized_admission_probe` rescue.

## 1. The round cap is refuted structurally, and that is a pre-registered outcome

**A round cap cannot convert an `unknown` into a verdict anywhere in this
population**, and the argument is in the code rather than in a rate.
`check_with_function_consistency` has exactly three exits:

| exit | condition |
|---|---|
| `Unsat` | the inner solve refuted the abstraction |
| `Unknown` | **the inner solve returned `Unknown`** — returned immediately, wrapped in the stats |
| replay | the candidate model was functionally consistent, so no lemma was emitted |

Truncating the loop at a cap can only produce the **second**. So:

* on **BORN-OVER** (12 of 22) the refusal is at round 1's solve, before any cap
  of `N >= 1` could fire; and
* on **GROWN** (10 of 22) round 1 returned a model that is functionally
  *inconsistent* (`violated_pairs >= 8` on every one), so stopping there yields
  `Unknown`, which is what already happens.

The only thing a round cap can buy is **wall-clock handed back to a downstream
route**, which is not a verdict and which PAR-2 does not score.

**Pre-registered:** the round-cap A/B is **not run**, and the distribution that
would have chosen its value is published anyway
([`round-distribution.txt`](round-distribution.txt), measured with the probe
below over the whole 129-file population, decided rows included). If that
distribution shows any file **deciding** at `solve_rounds >= 2`, a cap at 1
costs that file, and the number is reported. Recording the non-run here, in
advance, so that "we did not measure it" is a stated outcome rather than a quiet
omission.

## 2. What IS measured: the rescue that is wired to the other site

[ADR-2020] §8.3 recorded a **second** missing wiring beside the one [ADR-2030]
refuted:

> The `oversized_admission_probe` rescue is wired only into
> `check_with_arith_dpll`. The UF+arith route reaches the boundary through
> ... `euf.rs:948`, ... so a `UFLIA`/`UFNIA` instantiated conjunction that
> crosses this rectangle gets **no bounded online-CDCL(T) shot at all**.

Nobody has measured it. It is a **different hypothesis** from [ADR-2020]'s own
envelope lever: raising the envelope admits the oversized skeleton to
`IncrementalArithDpll`'s own enumerate-and-block loop (measured: 0 of 129, the
refusal becoming a timeout); this hands the same query to
`check_qf_lia_online_cdclt`, a different engine, under its own bounded budget.

**And it is still a last-site-to-refuse census claim.** [ADR-2030]'s whole
lesson is that such a claim is manufactured unless an ordered probe separates
"never reached the rescue" from "reached it and came out the other side". So:

### Gate 0 — the ordered probe, before the A/B is believed

`AXEYUM_PRESATPROBE=1` (off by default, printed, never acted on) emits one line
per boundary crossing naming which site crossed and what followed.
Pre-registered reading:

* If any of the 22 files shows a `site=preflight` line, the "missing wiring"
  framing is **wrong for that file** and it is excluded from the target set with
  its count reported — the same correction [ADR-2030] made.
* The target set is the files that cross **only** at `site=solve`.

## 3. Levers, polarity, and fail-closed

| lever | OFF (shipped) | ON |
|---|---|---|
| `AXEYUM_PRESATPROBE` | unset | `1` — print the ordered probe |
| `AXEYUM_PRESAT_RESCUE` | unset | `1` — offer `oversized_admission_probe` at the `solve` site |

Both parse through one function, `parse_pre_sat_flag`, which accepts an exact
`1` (whitespace tolerated) and **nothing else**, so a typo measures the shipped
arm rather than a half-enabled one. The parse is split from the `OnceLock`
lookup so the polarity is a pure unit test: a `OnceLock`-backed reader resolves
once per process, and a test that sets the variable after another test has read
it measures the wrong arm and still passes.

**Both arms visible BY MECHANISM, asserted before measuring:** with
`AXEYUM_PRESATPROBE=1`, the OFF arm prints `rescue=lever-off outcome=refused`
and the ON arm prints `rescue=ran outcome=<...>`. An ignored or mistyped
`AXEYUM_PRESAT_RESCUE` prints `lever-off`, which is the shipped value.

**The nonlinear guard is reproduced, not inherited.** `check_with_arith_dpll`
rejects a nonlinear-integer query *before* its preflight, because
`lia_online::is_lia_atom` accepts `(<= (* x y) c)`, classifies it `Unsupported`,
contributes no row, and the driver then enumerates to its deadline (measured
1.7–8.0 s per file). The `solve` site has no such guard upstream and **three of
the 22 files are `UFNIA`**, so `pre_sat_boundary_rescue` re-applies
`has_nonlinear_int_product` itself.

**Soundness.** The rescue returns a `CheckResult` in exactly the position
`IncrementalArithDpll::solve` would have returned one, over the **same**
assertion set. `check_qf_lia_online_cdclt` returning `Unsat` refutes that set;
returning `Sat` yields a model of it, which the CEGAR loop then replays and
projects exactly as it does for any other inner solver — `check_auto` is already
one of the loop's own fallbacks. Nothing is admitted that was not admitted
before; what changes is which engine is asked.

## 4. Decision rule, fixed before any value

`AXEYUM_PRESAT_RESCUE` **ships ON** iff, on the 129-file main population, ALL of:

1. net verdict change **>= +3**;
2. every gain is **STABLE-GAIN** — 3/3 in the ON arm and 0/3 in the OFF arm on
   re-run;
3. **zero STABLE-LOSS** rows;
4. every new verdict agrees with an independent authority (declared `:status`,
   `z3 -T:`, `cvc5 --tlimit`) with **no disagreement**, and the **comparable
   denominator is printed beside any zero** ([ADR-1957]);
5. both controls move **0**.

Otherwise it **ships OFF**.

**Why 3 and not 1.** [ADR-2030]'s same-arm noise floor moved **1 of 129**, and
the row it moved is the same volatile row that produced every loss in both of
its arms and then inverted under 3× re-runs. A band measured at 1 cannot
distinguish a 1-row or 2-row effect from itself. Three independently
STABLE-GAIN rows is the smallest count that is not explicable by that band.
This is a RULE about stability, not a conversion rate carried over from a mixed
population — [ADR-1980]'s bracket missed 3× that way and [ADR-2030]'s own
21.8 % turned out to be 10.2 % at row level.

## 5. Controls, built to detect a LOSS

The lever fires **only** at the `solve` site and **only** when the boundary is
already crossed, and at that site a crossing currently returns `Unknown`
unconditionally. (At the *other* site a crossing can already decide, through the
shipped rescue — which is the whole point — so this scoping matters and is
stated rather than assumed.) A loss therefore cannot come directly from a
changed verdict on a currently-decided row; it can only come from **budget**:
`oversized_admission_probe` may spend up to 10 s, and a file that today gives up
fast at the boundary and is then decided by a LATER route in the dispatch ladder
can be starved. Inside the CEGAR the cost is per ROUND, so a multi-round file
can pay it more than once.

That is the loss mechanism, and the controls are built for it.

| control | population | why non-vacuous |
|---|---|---|
| **A — same population** | the decided rows inside the 129 | same dispatch ladder, same budget; a starved downstream route flips them to `unknown`. Its decided-row count is reported so its POWER is visible, not assumed |
| **B — same function, other logic** | `QF_LIA` decided rows | exercises `IncrementalArithDpll::solve` directly, without the CEGAR above it |

A `QF_BV` control of [ADR-2030]'s kind would be **structurally blind here** — BV
never reaches `dpll_lia.rs` — so it is deliberately not used. A control that
cannot fail is worse than no control.

## 6. Noise floor, re-runs, and shards

* **Noise floor:** same binary, same 129-file list, `VAR=AXEYUM_NOT_A_LEVER`
  `VALUE=1`. The flag fails closed, so both arms are the shipped build and any
  movement is the band. Published for the whole division.
* **Re-runs:** every moved row 3× per arm, classified
  STABLE-GAIN / STABLE-LOSS / UNSTABLE / FLIP.
* **Interleaving:** one binary, two env values, arms back to back on the same
  file on the same pinned core, order rotating per file, both arms inside one
  shard. Polarity is stated in the runner header (`ab-run.sh`, reused verbatim
  from [ADR-2030]): the OFF arm **removes** the variable with `env -u`.
* **Shard configuration, fixed across arms:** main = **s5 cores 1, 3, 5, 7**
  (4 shards); control B = **s6 cores 1, 3**; noise floor = **s7 cores 1, 3**.
  Eight pinned cores, each running BOTH arms. Budget 24 s, `ulimit -v 8 GiB`,
  `timeout 40 s`.
* **The A/B arm measures THIS BRANCH**, not post-merge main, and the
  post-merge value is predicted with its reason in the ADR.
* Wilson 95 % intervals on every proportion.
