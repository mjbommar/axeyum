# Does MBQI reach the candidateless universals? No — it never runs, and fixing that reaches 7 of 1,498

**Date:** 2026-09-10
**Lane:** Q5-mbqi
**Question:** lane Q1 measured 290 triggerless universals (267 actable) with no
`Op::Apply` subterm mentioning any bound variable, and concluded *"reaching them
means model-based instantiation."* Does our MBQI reach them?

**Answer: no, at three independent depths, and only the third is about
capability.** The rung is entered on all 32 files; its refutation loop runs on
**0** of them; and if the guard that stops it were relaxed, the loop would
instantiate over 1,498 candidate universals of which **1,491 (99.5%) bind an
uninterpreted sort it cannot write a term for.** The residual — universals that
would actually reach instantiation — is **7, on 3 files**.

**And the prize is one file.** An engine ablation on z3 (§5) finds that
`smt.mbqi=false` costs it *nothing* on this slice — it decides the same 19 of
32 either way. Exactly one file, `f30`, is decided by z3's MBQI and by neither
of the other two arms. That is the measured ceiling for this whole line of
work.

**Verdict: DO NOT BUILD the guard relaxation.** It is a measured dead end at 7
universals. Section 7 states the one build this does *not* rule out, its single
named target, and the cheap pre-check that would kill it before it is
written.

**Population:** the 32 files of `bench-results/parity-losses-20260908/UF.txt`.
**Method:** `AXEYUM_QPROBE=1 target/release/examples/axeyum_cli <file> --timeout-ms 24000`,
four at a time, with three new `AXEYUM_QPROBE` probes (`mbqi-rung`,
`mbqi-shape`, `mbqi-census`/`mbqi-inst`) added in `b6e225bb8` and `a9dea1d48`.
The probes are diagnostic only: no routing, budget or verdict changes, and the
slice decides the same 1 of 32 before and after.

## 1. Why a new probe was needed at all

`mbqi_first_refusal` (`auto.rs`) logs exactly one of `sat` / `unsat` /
`declined` through `qtrace`. `declined` collapses two findings that need
completely different work:

- the MBQI refutation loop ran, instantiated, and failed to refute; or
- a shape guard in `prove_unsat_by_mbqi_inner` fired on the **first pass over
  the assertion list** and the call was `prove_unsat_by_ematching` from its
  first statement.

At the call site those are the same `Ok(None)`. The brief's own framing —
*"a rung that declines on an unsupported shape and one that runs and fails are
completely different findings"* — is exactly the distinction the existing trace
cannot make. It is the second one, on every file.

## 2. The rung runs. The loop does not.

| | value |
|---|---:|
| files where the rung was **entered** | **32 of 32** |
| budget the rung was handed | 526 – 2,972 ms (of a 24,000 ms clock) |
| files where the loop reached instantiation (`[mbqi-inst]` printed) | **0 of 32** |
| files decided | 1 (`f27`, by e-matching, fixed in `318930806`) |

So the brief's question 3 — *is the admission gate on the rung the same
`residual_quantifier` defect shape?* — is **no**. The gate lets it in every
time. The refusal is inside.

And the brief's caution about `MBQI_FIRST_REFUSAL_SHARE` — *"a rung given an
eighth of the budget that then declines has told you nothing"* — does not
apply either, for a reason that is worth stating rather than assuming. The
budget is not binding here: the decline happens during the initial classifying
walk over the assertions, **before any solving**, so an unbounded clock would
produce the identical decline. That is falsifiable — see §8.

The rung is not free, though. On `f31` with `AXEYUM_QTRACE=1`:

```
[qtrace] uf-fmf-probe +12.434s declined
[mbqi-rung]  state=entered budget_ms=1445
[mbqi-shape] exit=nested-binder-in-matrix single_binder_universals=0 ground=0
[qtrace] mbqi-quick +0.746s declined
[qtrace] egraph +14.053s declined
```

746 ms of the rung's 1,445 ms was spent — in `prove_unsat_by_ematching`, on a
throwaway arena clone, immediately before `run_egraph_quantified_fallback` runs
the e-graph route for real. The rung is currently a duplicate of the route
below it. (The larger budget sink on this file is `uf-fmf-probe` at 12.4 s of
24 s, which is a separate finding and not this lane's.)

## 3. Which guard, and on what

`prove_unsat_by_mbqi_inner` classifies each assertion in one pass and bails out
of the **whole call** at the first one it does not handle. Four of its five
exits `return prove_unsat_by_ematching(...)`. Measured first exit per file:

| first exit | files | the guard |
|---|---:|---|
| `nested-binder-in-matrix` | **25** | `if has_quantifier(arena, &[matrix])` after the `Forall` prefix is peeled |
| `quantifier-below-top-level` | **6** | `else if has_quantifier(arena, &[a])` — an assertion that is not a top-level `Forall` but contains a quantifier |
| `multi-binder-prefix` | **1** | `prefix.len() == 1` fails for every universal, so `has_multi_binder_prefix` |
| `refutation-loop` | **0** | — |

Q1's population is sledgehammer output: universals nested inside universals is
its normal shape, which is also why `collect_nested_registrations_rec` produces
the 360 inert registrations Q1 found. The same nesting that makes half of
category A inert is what stops MBQI at the door.

**The guards are whole-query, not per-assertion.** One wrong-shaped assertion
out of 500 aborts the call. Census over all 9,728 top-level assertions in the
slice:

| bucket | assertions | share | loop accepts it? |
|---|---:|---:|---|
| `qf` (ground) | 897 | 9.2% | yes, as ground |
| `prenex1` — `forall x. <qf>` | **1,498** | 15.4% | **yes — the only universal shape it takes** |
| `prenexN` — `forall x…z. <qf>`, N > 1 | 5,775 | 59.4% | no |
| `nested` — quantifier still in the matrix | 1,521 | 15.6% | no |
| `other` — quantifier not under a top-level `Forall` | 37 | 0.4% | no |

Every one of the 32 files carries at least one assertion outside the accepted
set. Prenex widths run to 13.

## 4. Relaxing the guards does not help, and the number is 7

The obvious fix is to stop aborting: keep the assertions the loop can handle
and let it run. Refuting a subset refutes the whole, so the `unsat` direction
survives, and the `sat` direction is already re-gated by
`certify_mbqi_candidate` plus `check_model` against the original assertions.

It reaches nothing, for a reason one level below the guards.

When the loop finds a candidate value `v` at which the model falsifies
`body[x:=v]` — a genuine refinement — it must turn `v` into a term:

```rust
let Some(c) = value_to_const(arena, &v) else {
    continue;
};
```

`value_to_const` (`auto.rs`) is

```rust
match value {
    Value::Bool(b) => …, Value::Int(n) => …, Value::Real(r) => …,
    Value::Bv { width, value } => …,
    _ => None,
}
```

and a declared sort produces `Value::Uninterpreted { sort, value }`, which is
the `_`. There is no constant term for a domain element of an uninterpreted
sort in this IR, so every such refinement is dropped and the round adds nothing.
The `mbqi_instance_via_mbp` fallback below it is LIA/LRA model-based projection
(`is_arith_atom` admits only `Int`/`Real`), so it declines on the same queries.

Measured on two minimal controls, both single-binder prenex — the ideal shape,
with the guards satisfied:

| control | `[mbqi-inst]` row |
|---|---|
| `forall ((x Int)) (> (f x) 0)` | `candidates=5 falsified=1 unrepresentable=0 instances=1` |
| `forall ((x S)) (p x)`, `S` declared | `candidates=2 falsified=2 unrepresentable=2 instances=0` |

On the uninterpreted-sort query MBQI found **both** refinements and could write
down **neither**.

And that is what the slice is made of. Of the 1,498 `prenex1` universals — the
entire population a guard relaxation would unlock:

| binder sort of the `prenex1` universals | count |
|---|---:|
| uninterpreted (`Value::Uninterpreted`, no constant term) | **1,491** |
| `Bool` / `Int` / `Real` / `BitVec` (representable) | **7** |

The 7 are `f01` (2), `f04` (1), `f09` (4). Three files, and on each of them the
other 40-plus `prenex1` universals are still unreachable, so those 7 are not a
refutation, they are a rounding error.

## 5. Does z3 decide these files *with* MBQI? Almost never — but once, uniquely

Before pricing a build, it is worth asking whether the reference solver uses
this mechanism on this slice at all. Three z3 configurations, same 32 files,
`-T:15` each (z3 4.13.3):

| configuration | files `unsat` |
|---|---:|
| default (e-matching **and** MBQI) | **19** |
| `smt.mbqi=false` (e-matching only) | **19 — the identical 19, file for file** |
| `smt.ematching=false smt.mbqi=true` (MBQI only) | **7** |

**Turning MBQI off costs z3 nothing on this slice.** Every file z3's default
decides, it decides by e-matching. MBQI is not the mechanism by which the
reference solver beats us here, which is a direct constraint on Q1's *"reaching
them means model-based instantiation"*: whatever z3 is doing on these 19, it is
not that.

MBQI-only decides 7, and 6 of those are also in the default's 19. The seventh
is not:

| file | default | `smt.mbqi=false` | `smt.ematching=false smt.mbqi=true` |
|---|---|---|---|
| `f30` — `UF/sledgehammer/NS_Shared/smtlib.678332.smt2` | timeout | timeout | **unsat** |

Reproduced three times at `-T:30`, stable in all three configurations. This is
z3's own portfolio failing to harvest a verdict its own MBQI can reach, because
e-matching spends the budget first — the same starvation shape our ladder has,
in the reference implementation.

So **the measured ceiling for a working MBQI on this slice is one file**, and
that file is named. `f30`'s census is
`assertions=17 qf=2 prenex1=1 prenexN=13 nested=0 other=1 max_prenex_width=10`,
with its single `prenex1` binder over an uninterpreted sort — so reaching it
needs both of the expensive builds in §6, not the cheap one.

**A counter to not merge with the source note's.** The source note records
*"z3 refutes the same files with 2-10 instantiations in <= 0.21 s"*. z3's
`:quant-instantiations` statistic on the default run gives 4 (`f27`), 4
(`f31`), 18, 26, 60, 75, 88, ... up to 12,055 (`f26`). `f31` agrees at 4; most
do not. These are different counters — instantiations *performed* versus proof
steps *used* — and neither number is wrong, but they must not be quoted
interchangeably. Check which was measured before citing either.

**Caveat on the denominator:** 13 of 32 time out at `-T:15` on a loaded box, so
"19 of 32" is not a capability claim about z3 and is not comparable to the
parity list's construction budget. The ablation is valid because all three arms
ran at the same budget on the same box; the absolute count is not.

## 6. What this says about Q1's 267

Q1's conclusion — *"reaching them means model-based instantiation"* — is not
refuted by this note. It is unblocked-cost-checked, and the cost is three
builds, not one:

1. **prenexing or per-assertion admission**, to get past the whole-query guards
   (1,521 nested + 37 other assertions);
2. **multi-binder instantiation**, because `prefix.len() == 1` rejects 5,775 of
   the 9,728 assertions and widths reach 13;
3. **term representatives for uninterpreted-sort domain elements**, without
   which the loop produces zero instances even on the shapes it already accepts
   (§4).

(3) is the one that is not a refactor. z3 does not instantiate at value
constants; it instantiates at *ground terms whose model value is the element*.
Doing that here needs a model-element-to-term map that this MBQI does not have
and `Value` cannot express.

None of the three is worth starting on the strength of a *mechanism*
argument, and §5 removes the strongest version of that argument: the reference
solver decides 19 of these files with MBQI switched **off**. The bar the brief
sets is a verdict, and the slice decides 1 of 32.

## 7. Verdict, and the one thing not ruled out

**DO NOT BUILD the guard relaxation** (per-assertion admission, prenexing, or
lifting `prefix.len() == 1`). Measured residual: 7 universals on 3 files, all
of which still sit in files whose remaining universals are unreachable.

**Not ruled out, and not built here: model-guided ground-term instantiation
over uninterpreted sorts.** It is the one route that is *selection* rather than
capacity, which matters because the source note's headline is that we
over-produce instances by three orders of magnitude and never select the right
one. Its shape: for `∀x:S. body`, probe the ground terms of sort `S` already in
the query, keep the one the model falsifies. That needs no new value
representation — the term is its own witness.

**What would show it worked:** a file in this 32-file slice moving from
`unknown` to `unsat`. Not more instances, not "MBQI now runs", not a lower
triggerless count. The slice decides 1 today.

§5 names the target and bounds the prize: **`f30`
(`UF/sledgehammer/NS_Shared/smtlib.678332.smt2`) is the one file in the slice
that z3 decides by MBQI and by nothing else** — its own default portfolio
times out on it. It is the single measured instance on this population where
MBQI is the deciding mechanism rather than a redundant one, so it is both the
right first target and the whole expected return. A build that lands `f30` and
nothing else has hit its ceiling, not fallen short of it.

**The cheap pre-check that should be run first, and would kill it:** count the
ground terms of each uninterpreted sort on these files. The e-graph loop already
pins at `MAX_GROUND_TERMS = 8192`; if the sort-`S` ground population is in the
thousands, model-guided probing over it is the same flooding Phase 3 measured
at zero from two directions, wearing a different hat, and the item closes
without a build. **This check did not run in this lane.**

## 8. What would refute each claim here

1. *The rung is entered on all 32.* Refuted by an `[mbqi-rung]` line reading
   `state=no-remaining-budget` or `state=unbounded-config` on any file, or by
   no `[mbqi-rung]` line at all.
2. *Its refutation loop runs on none of them.* Refuted by an
   `[mbqi-shape] exit=refutation-loop` or any `[mbqi-inst]` row on any of the
   32. The probe is not dead: it prints `exit=refutation-loop` and four
   `[mbqi-inst]` rows on the `Int` control in §4.
3. *The decline is a shape guard, not the budget.* Refuted by re-running any
   file with a much larger `--timeout-ms` and getting a different
   `[mbqi-shape] exit=`. The classifying walk precedes every solve call in the
   function, so this should hold at any clock.
4. *1,491 of 1,498 `prenex1` binders are uninterpreted.* Refuted by a
   `[mbqi-census]` line whose `prenex1_representable` exceeds its
   `prenex1_uninterpreted` on any file. The counter discriminates: the two §4
   controls report `1/0` and `0/1` respectively.
5. *Relaxing the guards reaches 7 universals.* Refuted by implementing
   per-assertion admission and observing any `[mbqi-inst]` row with
   `instances > 0` attributable to a universal outside those 7.
6. *z3 needs MBQI for none of these files but `f30`.* Refuted by any file where
   `z3 smt.mbqi=false` times out and plain `z3` does not, at the same budget on
   the same box. The ablation's own positive control is `f30`, where the
   MBQI-only arm and the other two arms disagree — so the configuration flags
   demonstrably reach the engine.

## 9. Did not run

- The ground-term population count of §7 — the pre-check that decides the only
  surviving build.
- Whether our MBQI, if it were reachable, resembles z3's closely enough to
  decide `f30`. z3's MBQI builds a finite model with a term representative per
  sort; ours probes model values. They are different algorithms, and §5 shows
  only that *an* MBQI decides `f30`, not that ours would.
- Any change to solver behaviour. Everything here is diagnostic; the slice
  decides the same 1 of 32 before and after.
- `cargo test --workspace`, by instruction. `cargo clippy -p axeyum-solver
  --lib --features full -- -D warnings` is clean.
