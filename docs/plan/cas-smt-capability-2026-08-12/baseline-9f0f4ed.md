# Baseline at `9f0f4ed005220b4985bf6edd97f052e3a4a19163`

**Commit measured:** `9f0f4ed005220b4985bf6edd97f052e3a4a19163`
(`merge origin/session/rado-claim-ledger-2026-08-12 into the proof lane`,
2026-08-12 20:32:15 -0400) — the last commit **before** the CAS bridge
`175372bdc` landed.

The harness was built against a `git archive` of that exact commit extracted to
a scratchpad directory, **not** against the shared working tree, because another
lane was editing `crates/axeyum-solver/` and `crates/axeyum-cas/` concurrently.
Without that, "the baseline" would have silently absorbed whatever their
in-progress edit happened to be at build time.

**The box was contended (load average 4.32 on 4 cores at run start). Every wall
time below is an upper bound, not a timing.**

## Summary

```
    67  DECIDED-OK
     2  OPEN-STAYS-UNKNOWN
    11  UNDECIDED-EXPECTED
    13  UNDECIDED-GAP

  axis A: decided  10   unknown   5      axis F: decided  10   unknown   4
  axis B: decided   8   unknown   2      axis G: decided   4   unknown  11
  axis C: decided  10   unknown   4      axis H: decided   5   unknown   0
  axis D: decided  20   unknown   0

  ALARMS: 0   ANCHOR REGRESSIONS: 0   BAD MODEL REPLAYS: 0
```

**Zero wrong verdicts across 93 queries.** Every decided verdict agrees with the
independently established ground truth; every failure is `unknown`.

## Deciding routes

| route | queries decided |
|---|---:|
| `nia-linearize` | 32 |
| `int-real-relax` | 16 |
| `int-blast-ladder` | 5 |
| `lia-simplex` | 5 |
| `dl-online` | 3 |
| `nia-square` | 2 |
| `uf-arithmetic` | 2 |
| `lia-dpll` | 1 |
| `lia-diophantine` | 1 |

## The 13 gaps are structural, not budget-starved

Re-running only the `UNDECIDED-GAP` entries at **6× budget** (60 s) leaves
**13/13 still undecided** (`gaps-6x-9f0f4ed.out`). Three decline in under a
fifth of a second regardless of budget: `A14-mod-phrasing` 0.19 s,
`F3-sum2sq-3` 0.07 s, `G4-pell-square-d` 0.07 s.

Every gap has the same trace signature:

```
probe: fragment {int}
 | dl-online: declined (not-applicable)
 | lia-simplex: declined (unsupported)
 | lia-dpll: declined (unsupported)
 | nia-square: declined (not-applicable)
 | nia-linearize: declined (verifier-rejected: relaxation model failed
     ground-evaluator replay against the originals)
 | nia-bounded-blast: declined (not-applicable)
 | int-blast-ladder: declined (incomplete: no model within the bounded integer
     width 32; widen the bound)            <- or (budget: ... timeout reached)
```

So the failure is **not** "no route handles nonlinear integers". It is:
`nia-linearize` builds a candidate and then correctly **rejects its own
candidate** at its verify-before-return step; the only route left is
`int-blast-ladder`, bounded at integer width 32, which cannot refute an
unbounded-integer claim.

## The counterintuitive pairs (the sharpest findings)

| decides in 0.00 s | times out |
|---|---|
| `A5` `a>=2 /\ p>=1 /\ a*p=1` → `int-real-relax` | `A1` `a>=2 /\ a*p=1` |
| `A6` `a>=2 /\ b>=1 /\ (a*b)*p=1` → `nia-linearize` | `A1` (the *simpler* query) |
| `B3` `r = a^2*(w-s) /\ 1<=r<=a^2-1` → `nia-linearize` | `B1` `M>=1 /\ 1<=M*c<=M-1` |
| `A10` non-divisibility by **remainder witness** | `A9` the same fact stated **directly** |

`B5` (`M >= 4 /\ 1 <= M*c <= M-1`) also times out, which sharpens route-B's
"generalising made it harder" observation: supplying the *bound* `a^2 >= 4` does
not help. It is the **form** `a^2`, not the magnitude, that `nia-linearize`
needs.

Axis D is **20/20 decided at the baseline**. Polynomial identities of degree 2–4
in 2–3 variables, including with an opaque uninterpreted atom (`B9`/`B10`), are
already fully handled by `int-real-relax` and `nia-linearize`. Any change that
only adds polynomial-identity checking therefore cannot move this corpus.

## Full results

| id | tier | expect | verdict | route | secs | status |
|---|---|---|---|---:|---:|---|
| `A1-unit-direct` | core | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 10.00 | UNDECIDED-GAP |
| `A2-unit-ctrl-a1` | core | sat | sat | `nia-linearize` | 0.00 | DECIDED-OK |
| `A3-unit-neg` | core | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 10.00 | UNDECIDED-GAP |
| `A4-unit-ctrl-neg` | core | sat | sat | `nia-linearize` | 0.00 | DECIDED-OK |
| `A5-unit-signed` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `A6-unit-product` | core | unsat | unsat | `nia-linearize` | 0.00 | DECIDED-OK |
| `A7-notdiv1-witness` | core | unsat | unsat | `lia-dpll` | 0.00 | DECIDED-OK |
| `A8-notdiv1-wit-ctrl` | core | sat | sat | `dl-online` | 0.00 | DECIDED-OK |
| `A9-div-var-x` | core | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 10.00 | UNDECIDED-GAP |
| `A10-nondiv-x-witness` | core | unsat | unsat | `int-real-relax` | 0.02 | DECIDED-OK |
| `A11-div-var-x-ctrl` | core | sat | sat | `nia-linearize` | 0.02 | DECIDED-OK |
| `A12-cube-nondiv` | core | unsat | unknown(Incomplete) | `decl:int-blast-ladder` | 5.23 | UNDECIDED-GAP |
| `A13-cube-nondiv-ctrl` | core | sat | sat | `nia-linearize` | 1.74 | DECIDED-OK |
| `A14-mod-phrasing` | core | unsat | unknown(Incomplete) | `decl:int-blast-ladder` | 0.19 | UNDECIDED-GAP |
| `A15-mod-phrasing-ctrl` | core | sat | sat | `nia-linearize` | 0.00 | DECIDED-OK |
| `B1-opaque-window` | core | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 10.00 | UNDECIDED-GAP |
| `B2-opaque-window-ctrl` | core | sat | sat | `nia-linearize` | 0.00 | DECIDED-OK |
| `B3-inst-window` | core | unsat | unsat | `nia-linearize` | 0.01 | DECIDED-OK |
| `B4-inst-window-ctrl` | core | sat | sat | `nia-linearize` | 0.01 | DECIDED-OK |
| `B5-opaque-window-M4` | core | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 10.00 | UNDECIDED-GAP |
| `B6-opaque-mono` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `B7-inst-mono` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `B8-opaque-mono-ctrl` | core | sat | sat | `nia-linearize` | 0.00 | DECIDED-OK |
| `B9-uf-opaque-identity` | core | unsat | unsat | `uf-arithmetic` | 0.00 | DECIDED-OK |
| `B10-uf-opaque-ctrl` | core | sat | sat | `uf-arithmetic` | 0.01 | DECIDED-OK |
| `C1-mono-k2-colour1` | core | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 10.01 | UNDECIDED-GAP |
| `C2-mono-k2-no-gcd` | core | sat | sat | `nia-linearize` | 0.66 | DECIDED-OK |
| `C3-L1-cancel` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `C4-L1-cancel-ctrl` | core | sat | sat | `nia-linearize` | 0.00 | DECIDED-OK |
| `C5-L2-positivity` | core | unsat | unsat | `nia-linearize` | 0.00 | DECIDED-OK |
| `C6-L2-positivity-ctrl` | core | sat | sat | `nia-linearize` | 0.00 | DECIDED-OK |
| `C7-L3-mono` | core | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 10.00 | UNDECIDED-GAP |
| `C8-L3-mono-ctrl` | core | sat | sat | `nia-linearize` | 0.03 | DECIDED-OK |
| `C9-L4-endpoint` | core | unsat | unsat | `lia-simplex` | 0.00 | DECIDED-OK |
| `C10-L4-endpoint-ctrl` | core | sat | sat | `lia-simplex` | 0.00 | DECIDED-OK |
| `C11-L5-distribute` | core | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 10.00 | UNDECIDED-GAP |
| `C12-L5-distribute-ctrl` | core | sat | sat | `nia-linearize` | 0.02 | DECIDED-OK |
| `C13-L6-bezout` | core | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 10.00 | UNDECIDED-GAP |
| `C14-L6-bezout-ctrl` | core | sat | sat | `nia-linearize` | 0.03 | DECIDED-OK |
| `D1-id2-square` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `D2-id2-square-ctrl` | core | sat | sat | `nia-linearize` | 0.01 | DECIDED-OK |
| `D3-id3-cube` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `D4-id3-cube-ctrl` | core | sat | sat | `nia-linearize` | 0.01 | DECIDED-OK |
| `D5-id3-sumcubes` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `D6-id3-sumcubes-ctrl` | core | sat | sat | `nia-linearize` | 0.01 | DECIDED-OK |
| `D7-id4-binom` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `D8-id4-binom-ctrl` | core | sat | sat | `nia-linearize` | 0.02 | DECIDED-OK |
| `D9-id2-three-var` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `D10-id2-three-var-ctrl` | core | sat | sat | `nia-linearize` | 0.01 | DECIDED-OK |
| `D11-id3-cyclic` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `D12-id3-cyclic-ctrl` | core | sat | sat | `nia-linearize` | 0.04 | DECIDED-OK |
| `D13-id4-sophie-germain` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `D14-id4-sophie-ctrl` | core | sat | sat | `nia-linearize` | 0.01 | DECIDED-OK |
| `D15-id4-difference` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `D16-id4-difference-ctrl` | core | sat | sat | `nia-linearize` | 0.01 | DECIDED-OK |
| `D17-id-congruence` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `D18-id-congruence-ctrl` | core | sat | sat | `nia-linearize` | 0.00 | DECIDED-OK |
| `D19-id4-brahmagupta` | core | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `D20-id4-brahmagupta-ctrl` | core | sat | sat | `nia-linearize` | 0.03 | DECIDED-OK |
| `F1-square-eq-2` | core | unsat | unsat | `nia-square` | 0.00 | DECIDED-OK |
| `F2-square-eq-4` | core | sat | sat | `nia-square` | 0.00 | DECIDED-OK |
| `F3-sum2sq-3` | core | unsat | unknown(Incomplete) | `decl:int-blast-ladder` | 0.07 | UNDECIDED-GAP |
| `F4-sum2sq-5` | core | sat | sat | `int-blast-ladder` | 0.00 | DECIDED-OK |
| `F5-sum3sq-7` | hard | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 20.00 | UNDECIDED-EXPECTED |
| `F6-sum3sq-6` | core | sat | sat | `int-blast-ladder` | 0.01 | DECIDED-OK |
| `F7-pythag-3-5` | core | unsat | unsat | `nia-linearize` | 1.53 | DECIDED-OK |
| `F8-pythag-3-4` | core | sat | sat | `nia-linearize` | 0.16 | DECIDED-OK |
| `F9-linear-gcd-3` | anchor | unsat | unsat | `lia-diophantine` | 0.00 | DECIDED-OK |
| `F10-linear-gcd-2` | anchor | sat | sat | `lia-simplex` | 0.00 | DECIDED-OK |
| `F11-sqrt2-descent` | hard | unsat | unknown(Incomplete) | `decl:int-blast-ladder` | 6.75 | UNDECIDED-EXPECTED |
| `F12-sqrt2-descent-ctrl` | core | sat | sat | `nia-linearize` | 0.00 | DECIDED-OK |
| `F13-square-eq-cube` | core | sat | sat | `int-blast-ladder` | 3.34 | DECIDED-OK |
| `F14-mordell-7` | hard | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 20.00 | UNDECIDED-EXPECTED |
| `G1-pell-61` | tripwire | sat | unknown(Timeout) | `decl:int-blast-ladder` | 20.00 | UNDECIDED-EXPECTED |
| `G2-pell-109` | tripwire | sat | unknown(Timeout) | `decl:int-blast-ladder` | 20.00 | UNDECIDED-EXPECTED |
| `G3-pell-61-neg` | tripwire | sat | unknown(Timeout) | `decl:int-blast-ladder` | 20.00 | UNDECIDED-EXPECTED |
| `G4-pell-square-d` | core | unsat | unknown(Incomplete) | `decl:int-blast-ladder` | 0.07 | UNDECIDED-GAP |
| `G5-flt-4` | hard | unsat | unknown(Incomplete) | `decl:int-blast-ladder` | 13.59 | UNDECIDED-EXPECTED |
| `G6-flt-4-nearmiss` | core | sat | sat | `nia-linearize` | 0.00 | DECIDED-OK |
| `G7-flt-3` | hard | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 20.01 | UNDECIDED-EXPECTED |
| `G8-taxicab-1729` | core | sat | sat | `int-blast-ladder` | 3.35 | DECIDED-OK |
| `G9-three-cubes-4` | hard | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 20.00 | UNDECIDED-EXPECTED |
| `G10-three-cubes-5` | hard | unsat | unknown(Timeout) | `decl:int-blast-ladder` | 20.00 | UNDECIDED-EXPECTED |
| `G11-three-cubes-3` | core | sat | sat | `int-blast-ladder` | 0.01 | DECIDED-OK |
| `G12-three-cubes-33` | tripwire | sat | unknown(Timeout) | `decl:int-blast-ladder` | 20.00 | UNDECIDED-EXPECTED |
| `G13-three-cubes-114-OPEN` | open | open | unknown(Timeout) | `decl:int-blast-ladder` | 20.00 | OPEN-STAYS-UNKNOWN |
| `G14-three-cubes-390-OPEN` | open | open | unknown(Timeout) | `decl:int-blast-ladder` | 20.00 | OPEN-STAYS-UNKNOWN |
| `G15-brocard-5` | core | sat | sat | `nia-linearize` | 1.09 | DECIDED-OK |
| `H1-linear-sat` | anchor | sat | sat | `lia-simplex` | 0.00 | DECIDED-OK |
| `H2-linear-unsat` | anchor | unsat | unsat | `lia-simplex` | 0.00 | DECIDED-OK |
| `H3-mul-lower-bound` | anchor | unsat | unsat | `int-real-relax` | 0.00 | DECIDED-OK |
| `H4-dl-negative-cycle` | anchor | unsat | unsat | `dl-online` | 0.00 | DECIDED-OK |
| `H5-dl-zero-cycle` | anchor | sat | sat | `dl-online` | 0.00 | DECIDED-OK |
