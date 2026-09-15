# ADR-2100: typed route ownership — whether the ladder stops is a declaration on the route, not the error variant a function returned

Status: accepted
Index-summary: Whether a dispatch rung's non-decision STOPS the ladder was decided per call site by which error variant a function happened to return — `Err(Unsupported)` meaning "not mine, keep going" and `Ok(Unknown)` meaning "mine, tried, failed, stop" — with 38 `Unsupported` mentions in `auto.rs`, seven sites of the shape that matches a decision or an unknown in one arm and an unsupported refusal in the other, and nothing checking them against each other. **The same defect shipped five times** (ADR-1927, 1966, 1980, 2030, 2065), four of the five found by accident while chasing something else, and the fifth enumerated 72 sites mechanically and then had to be REVERTED for turning seven assertions red. Decision: **each route DECLARES the construct classes it owns, and the ladder consults the declaration.** A route that does not own every construct the query carries cannot stop the ladder whatever it returned; one that does, can; and an `Err(Unsupported)` from an owning route is a recorded inconsistency carrying a fixed greppable marker rather than a silent fall-through. `hand_back_unless_refuted` — this rule hand-written for ONE rung by ADR-2065 — is DELETED, and its own doc comment names why it had to be narrow: a repair inside the route "would require this route to reason about what OTHER routes can do". A declaration consulted by the LADDER requires nothing of the kind. The declaration is DERIVED, not invented: almost every rung already opens with a `Features` conjunction that returns `Ok(None)`, and that conjunction IS the statement of what it refuses. `RouteKind::{Decider, FastPath}` is not a softening but the distinction ownership ALONE gets wrong — `datatype-elim` (ADR-0022 step A) refuses BY DESIGN so step B gets the query, and under ownership alone that hand-off reads as an inconsistency on every `QF_DT` file. **The sites are enumerated by the COMPILER**, ADR-2060's method: `DispatchError` has no `From<SolverError>`, so every `?` and `return Err` in the ladder is a type error until its site names a rung — **`rustc` named 17**, fifteen closed by a route and two by position (ADR-1966's own "terminal — it is the last rung"). **SIZING FIRST, and the ceiling is ZERO of 645** undecided Tier 1 rows, inside lane PLAN-SIZING's frame of 604 `stopped_by_unknown` — joined 645/645 by corpus PATH, with the script ABORTING rather than reporting a smaller number. Three corrections got there: a first answer of 102 that modelled the ladder from SOURCE TEXT rather than control flow (`dispatch_nonlinear_int_tail` is a `return`, so `qf-bv` is unreachable from any integer query), a second of 5 that confused owning a construct with being ENTERABLE on it (0 occurrences of `Array` in any of the five files), and the finding worth more than the ceiling: **482 of 643 undecided Tier 1 rows — 75 % — never reach the quantifier-free dispatch ladder at all.** Phase 1 is still worth doing for the bug class and this ADR says so rather than implying a gain. Measured: all **19** `dispatch/reason:` suites plus the four DT suites and 93 `auto::tests` green **with the helper deleted**; solver lib sweep 1,805/0; `progress_frontier` 12/12. Interleaved two-binary A/B (the runner REFUSES if the arms hash the same), nine divisions × 200 files, both arms back to back on one pinned core, order alternating, 24 s / 8 GiB: **0 `sat`↔`unsat` flips, 865 `:status` comparisons with 0 disagreements, +2/−2 net 0** — and, with all 11 movers re-run 3× per arm, **2 STABLE-GAIN, 2 STABLE-LOSS**, so **exit criterion 3 is NOT MET on losses and that is reported rather than smoothed**. One of the two losses is literally a file ADR-1966 named as its own reproducible loss from the identical mechanism: a rung that declines instead of stopping makes more routes run, and on a quantified file the extra work lands inside `solve`'s sub-solves. The lane's own instruments caught two defects reading did not: the mutation control came back **SURVIVED** on its first run because preprocessing folds the fixture's read-over-write before dispatch so `lira-dpll` never ran — its non-vacuity guard had accepted `nra` as well, and **a non-vacuity check that admits a route other than the one under test is not one** — and this lane's trace runner reproduced ADR-2075's bug four weeks later, anchoring on `^; route ` and dropping the 103 rows whose watchdog path prints `; partial route `.
Index-status: accepted
Date: 2026-09-15

## Context

A rung of `check_auto_dispatch_inner` (`crates/axeyum-solver/src/auto.rs`) has
two ways to not decide:

- `Err(SolverError::Unsupported(_))` — "not mine, keep going";
- `Ok(CheckResult::Unknown(_))` — "mine, tried, failed, stop".

The distinction is right. **It is decided per call site by which variant a
function happened to return**, and nothing checks the two against each other.
`auto.rs` mentions `SolverError::Unsupported` 38 times and has seven sites
matching the `Ok(Sat|Unknown) | Err(Unsupported)` shape.

The same bug has now shipped five times:

| ADR | what happened |
|---|---|
| [1927] | three quantified rungs propagated a speculative sub-solve's `Unsupported` with a bare `?`; `AUFDTLIRA` scored 0 of 200 at `attempts=2` |
| [1966] | enumerated **72** propagation sites mechanically; sized the largest at +22/−2 and **reverted it** — it turned 7 assertions red in four other ADRs' suites |
| [1980] | landed that same site by RELOCATING the assertions to where their guard lives: **+79 across three divisions** |
| [2030] | "missing wiring" refuted — the fallback WAS offered; `OverboundOutcome::NotEngaged` means BOTH "not my fragment" and "the bound did not fire" |
| [2065] | a rung that started ADMITTING an atom silently became an owner, so its decline stopped the ladder; fixed by `hand_back_unless_refuted` — this rule, hand-written for one rung |

Each fix was local. The next instance is guaranteed.

## The rule

Each route declares the **construct classes it owns**. On a non-decision the
ladder consults the declaration rather than the variant:

| route's answer | route owns every construct in the query | route does not |
|---|---|---|
| `Ok(Sat)` / `Ok(Unsat)` | decides | decides |
| `Ok(Unknown)` | **terminal** — the ladder stops | **decline** — the ladder continues |
| `Err(Unsupported)` | **reported inconsistency** | **decline** — the ladder continues |

"Owns every construct in the query" is `query_constructs ⊆ route.owns()`: only a
route that can in principle handle the whole fragment gets to say "mine, tried,
failed".

This subsumes [2065]'s `hand_back_unless_refuted`. That helper exists because
`lira-dpll`'s opaque-real abstraction started admitting a real-sorted
`(select a i)`, so the route returned a terminal `Ok(Unknown)` and
`array-fast-path` — which decided the same query in 2 ms — was never reached.
Under the declaration `lira-dpll` owns `{Int, Real}` and the query carries
`Array`, so the `Unknown` is a decline and the ladder continues. The helper's own
doc comment says why it had to be written narrowly:

> The obvious repairs … all require this route to reason about what OTHER routes
> can do, which it cannot do soundly and which would need re-deciding every time
> the ladder changes.

A declaration consulted *by the ladder* needs no route to know about any other
route. That is the whole difference.

**Soundness is structural, not argued** — the same argument [1927] and [1966]
make. Declining can only lose completeness: the ladder continues with the
ORIGINAL assertions, the arena is append-only during solving, and every rung it
reaches applies its own discipline (a `sat` is still replay-checked against the
original assertions at the front door; an `unsat` still comes from an
equisatisfiable reduction). The risk to exclude is the other direction — that
running more rungs manufactures a wrong `unsat` — and that is what the A/B's
flip column and the `:status` cross-check are for.

**The cost is real and is not confined to the queries whose refusal it
converts.** [1966]'s `UFLIA` control, chosen precisely because nothing in it
could trigger the guard, still lost one file reproducibly: the ladder took a
longer path, `q:egraph` ate 19.3 s of the budget, and the route that had decided
the file in 2.0 s never got there. That is the mechanism the A/B in criterion 3
has to measure rather than assume.

## The construct classes

Derived from `Features` (`auto.rs:11648`), which is the scan the dispatcher
already runs before every rung. One class per flag, so the declaration is stated
in the same vocabulary the gates are:

| class | `Features` flag |
|---|---|
| `Real` | `has_real` |
| `Int` | `has_int` |
| `BvOrFloat` | `has_bv_or_float` |
| `Datatype` | `has_datatype` |
| `Function` | `has_function` (any `Op::Apply`) |
| `UninterpretedSort` | `has_uninterpreted_sort` |
| `Array` | `has_array` |
| `NonBvArray` | `has_non_bv_array` |
| `NonBoolBvArray` | `has_non_bool_bv_array` |
| `NestedArray` | `has_nested_array` |
| `WideInt` | `has_wide_int` |

`has_bitblast` is deliberately **not** a class: it is a derived disjunction of
four others, not an independent construct, and admitting it would let a route
claim ownership of `Int` by claiming `bitblast`.

`Bool` is not a class either: every route owns Boolean structure, so a class
every route declares distinguishes nothing.

## How each route's ownership is derived — not invented

**The declaration is read off the route's own gate.** Almost every rung already
opens with a `Features` conjunction that returns `Ok(None)` — that conjunction
*is* the statement of what the route refuses, and the owned set is its
complement. `dispatch_uf_nra` is the clearest instance:

```rust
if !features.has_real
    || !features.has_function
    || features.has_int
    || features.has_array
    || features.has_datatype
    || features.has_uninterpreted_sort
{ return Ok(None); }
```

so `uf-nra` owns exactly `{Real, Function}`. Deriving rather than inventing is
what keeps the declaration from becoming a second thing that drifts, and it is
why the first test below re-derives the gate conjunctions from the source.

| route | gate in source | owns |
|---|---|---|
| `datatype-elim` | `features.has_datatype` | `{Datatype, Int, Real, BvOrFloat, Function, UninterpretedSort}` |
| `datatype-native` | same branch | `{Datatype, Int, BvOrFloat}` |
| `dl-online` | `dl_online::scan_dl` | `{Int, Real}` |
| `lira-dpll` | `has_real && has_int` | `{Int, Real}` |
| `uf-nra` | the conjunction above | `{Real, Function}` |
| `nra-real-root` | `has_real && has_nonlinear_real` | `{Real}` |
| `nra` | `has_real` | `{Real, Function}` |
| `uf-arith-overbound-probe` | `has_int && !has_real && !has_array && has_function` | `{Int, Function}` |
| `bv2nat-blast` | `has_int && has_bv_or_float && !has_function && !has_array && !has_uninterpreted_sort && !has_datatype` | `{Int, BvOrFloat}` |
| `int-linear-refuters` | `has_int` | `{Int}` |
| `uf-routes` | `has_function \|\| has_uninterpreted_sort` | `{Function, UninterpretedSort, Int, Real, BvOrFloat, Array}` |
| `abv-online-cdclt` | `!has_function && !has_int && !has_real && !has_non_bool_bv_array && !has_uninterpreted_sort && !has_datatype` | `{Array, BvOrFloat}` |
| `array-fast-path` | three sub-gates on `has_non_bv_array` / purity | `{Array, NonBvArray, Int, Real, Function, UninterpretedSort, BvOrFloat}` |
| `nonlinear-int-tail` | `has_int` | `{Int}` |
| `qf-bv` (`check_with_all_theories`) | no gate; the tail | `{BvOrFloat, Int, Array, Function, UninterpretedSort}` |

Two entries carry a deliberate asymmetry worth naming:

- **`NestedArray` is owned by nobody.** `Sort::array_sorts` returns `None` for a
  nested array sort, so every array route that predates nesting already refuses
  one ([1955]/[1965]). Declaring it unowned makes that refusal a named decline
  rather than an accident of a helper returning `None` — which is the reason the
  flag exists at all.
- **`WideInt` is owned by nobody**, per ADR-1702 slice 2: the opt-in is
  per-route and nothing has opted in. `wide_int_admission` already declines with
  a named reason before dispatch, and is the closest thing in the tree today to
  a route declaring what it owns.

## The compiler enumerates the sites, not a grep

[2060] established the method: **give the declaration a payload and the type
errors are the site list.** A name scan found six constructions of
`Decision::TimedOut`; giving the variant a payload found the same six plus, by
transitive closure over the cause-erasing returns that feed them, **28 program
points carrying 15 distinct causes**. [1966] found the same shape from the other
direction — counting only `?` gave 37 sites, and adding tail position and
`return f(..)` took it to 72.

Two payloads here, and both are load-bearing:

1. **The funnel takes a `DispatchRoute`, not a `&'static str`.** Changing
   `rung_or_decline(route: &'static str, …)` to `rung_or_decline(route:
   DispatchRoute, …)` makes every call site a type error until it names a
   variant, and `DispatchRoute::owns` is an exhaustive `match` — a route added
   without an ownership declaration does not compile.
2. **The ladder's error channel gets a type with no `From<SolverError>`.**
   `check_auto_dispatch_inner` returns `Result<CheckResult, DispatchError>`
   where `DispatchError` carries the route that produced it. Every `?` and every
   `return Err(..)` in that body is then a type error, and `rustc` prints the
   file:line of each one. That list is the enumeration criterion 1 asks for, and
   it is produced by the compiler rather than by reading the file.

`grep` is used afterwards only to check the compiler's list against [1966]'s
pinned 72-site baseline, never to produce it.

## Sizing — the ceiling is ZERO, and Phase 1 is still worth doing

**The number first, because the exit criterion asks for it up front: 0, on all
seven Tier 1 divisions, against a denominator of 645.**

### The frame

Lane PLAN-SIZING's inventory
(`bench-results/dispatch-plan-sizing-20260915/phase1-ceiling.tsv`) fixes it:
645 undecided Tier 1 rows, of which **604 are `stopped_by_unknown`** — the last
recorded attempt's reason is `budget` / `incomplete` / `verifier-rejected`, an
actual `Ok(Unknown)`, so the ladder STOPPED rather than running out of rungs.
The other 40 ended on an `unsupported` / `not-applicable` decline, which already
let the ladder continue, so the ownership rule has nothing to change about them.

That lane could not compute the ceiling and said so plainly:

> The Phase 1 ceiling as the plan defines it … needs the ladder's fixed ORDER
> and each route's Features-ownership predicate. **That predicate does not exist
> yet — building it is Phase 1's own deliverable**, so it cannot be used to size
> Phase 1 before Phase 1 exists.

This ADR supplies the predicate, and this is the answer. The sweep was not
re-run: the construct evidence comes from this lane's own `--trace` capture of
the same 645 rows, joined to PLAN-SIZING's inventory by corpus-relative PATH —
**645 of 645 join, checked, and the script ABORTS rather than reporting a
smaller number if any row is missing from either side.**

### The numbers

| division | undecided | stopped by `Unknown` | a route below OWNS | …and is ENTERABLE | never reached the QF ladder |
|---|---:|---:|---:|---:|---:|
| AUFLIRA | 22 | 20 | 0 | **0** | 20 |
| UFNIA | 147 | 136 | 5 | **0** | 130 |
| UFLIA | 115 | 107 | 0 | **0** | 107 |
| AUFDTLIRA | 79 | 68 | 0 | **0** | 67 |
| QF_NIA | 116 | 114 | 0 | **0** | 0 |
| UF | 110 | 108 | 0 | **0** | 108 |
| UFDTLIRA | 56 | 51 | 0 | **0** | 50 |
| **total** | **645** | **604** | **5** | **0** | **482** |

(PLAN-SIZING's `undecided` and `stopped_by_unknown` columns; the last three are
this lane's, over the 643 rows its own re-capture scored — two of the 645 came
back `unsat` this time, an ambient flip, and one produced no output at all.)

**This is the seven-division Tier 1 frame and NOT the 16-division public board**
(`bench-results/board-ab-20260915/`), which is a different, QF_\*-heavy division
set on a different harness. `UF` and `QF_NIA` appear on both, as separate sample
runs. Do not add these counts to that board's totals.

Artifacts: `bench-results/route-ownership-20260915/` — `trace-run.sh`,
`launch-trace.sh`, `size-ceiling.py`, the per-row trails in
`trace-tier1-undecided.tsv`, and the run in `sizing.txt`.

### Phase 1 is still worth doing, and this ADR says so rather than implying a gain

The dispatch plan says the same in advance: *"None of these phases is measured in
files decided. Phase 1 is measured in bug class killed."* The five ADRs this
closes cost roughly a lane each, **four of the five were found by accident while
chasing something else**, and the fifth enumerated 72 sites mechanically and then
had to be reverted for turning seven assertions red. What this buys is that the
sixth instance is a compile error or a named trail entry rather than a sixth ADR.

### Three corrections the sizing produced, each of which would have been a claim

**The first number was 102 and it flattered the lane.** `size-ceiling.py`'s first
run reported 102 of 116 `QF_NIA` rows reachable, every one with
`owner-below=qf-bv`. The ladder order it used was read off the SOURCE TEXT, and
`dispatch_nonlinear_int_tail` is reached as `return dispatch_nonlinear_int_tail(..)`
inside `if features.has_int` — so `qf-bv`, textually below it, is unreachable
from any integer query. **A route ordering read off the text rather than off the
control flow bounds nothing.**

**The second number was 5 and it was also wrong.** All five remaining rows name
`array-fast-path` as the owner below. It owns `{…, Int, …}` and runs only
`if features.has_array`. Owning a construct and being ENTERABLE on a query are
different questions, and the second is what decides whether the route gets a
turn. Confirmed against the corpus text: **0 occurrences of `Array` in any of the
five** (`UFNIA/2019-Preiner/qf/t3_rw{353,597,658,1283,1466}.smt2`). Each
correction is a comment beside the rule that implements it, so the next reader
does not re-derive them.

**The finding worth more than the ceiling: 482 of 643 undecided Tier 1 rows —
75 % — never reach the quantifier-free dispatch ladder at all.** Their budget
goes to the `q:` rungs of the quantified ladder in `solve`, which is a different
ladder with its own decline discipline (ADR-1927). No amount of quantifier-free
route ownership can move them. `QF_NIA` is the one division where every row
reaches the ladder, and it is also the only quantifier-free division in the set.
That is a statement about where Tier 1's remaining mass is, it is measured rather
than asserted, and the per-row trails are committed.

### What the sizing does NOT say

It does not bound the change's effect on **decided** rows, which is the risk side
and is what the A/B measures. ADR-1966's `UFLIA` control — chosen because nothing
in it could trigger the guard — still lost one file reproducibly, because a route
the ladder now reaches ate the budget the deciding route needed. A ceiling of 0
on the undecided population says nothing about that.

## What shipped

`route_ownership`, a module inside `crates/axeyum-solver/src/auto.rs`:

- **`Construct`** — eleven classes, one per `Features` flag. `has_bitblast` is
  deliberately not one: it is a derived disjunction of four others, and a class
  for it would let a route claim ownership of `Int` by claiming `BitBlast`.
- **`ConstructSet`** — a bitset, so the subset test the ladder runs on every
  non-decision is one instruction. Its `not_covered_by` returns the WITNESS
  rather than a bool, because a decline whose reason is "the rule said so" is
  one a reader cannot check.
- **`DispatchRoute`** — twelve rungs, with `label`, `owns` and `kind` as
  exhaustive `match`es. A rung added without a declaration does not compile.
- **`RouteKind::{Decider, FastPath}`** — see below.
- **`settle_rung` / `record_route_refusal`** — the rule, applied once.
- **`DispatchError`** — the error channel with no `From<SolverError>`.

`hand_back_unless_refuted` and `ArithRun::abstracted_opaque_reals` are deleted
from `crates/axeyum-solver/src/dpll_lia.rs`.

### `RouteKind` is the distinction ownership ALONE gets wrong

Ownership by itself gets the datatype branch wrong, and getting it wrong is
instructive. `datatype-elim` (ADR-0022 step A) and `datatype-native` (step B)
are two halves of one decision procedure: step A folds read-over-construct and
**refuses by design** when free datatype variables remain, precisely so step B
gets them. Under ownership alone that refusal reads as "a route refused a
fragment it declared" — the inconsistency report — on every `QF_DT` file, for a
hand-off working exactly as intended.

The fix is not "datatype is special". It is that a route is either the ladder's
decision procedure for a fragment or an accelerator sitting above one, and the
two have different contracts for a non-decision. ADR-1927 found the same class
from the other side: it wrote a guard for `checked_quantified_fast_path`,
measured it firing **0 times in 800 files**, and deleted it rather than ship an
un-failable check — a fast path's refusal was never terminal there either.

Five rungs are `FastPath` (`datatype-elim`, `uf-nra`,
`uf-arith-overbound-probe`, `bv2nat-blast`, `abv-online-cdclt`) and seven are
`Decider`. Two of the five already implemented the `FastPath` contract by hand:
`bv2nat-blast` converts its own `Unknown` to a decline and falls through, and
`abv-online-cdclt` does the same inside `dispatch_abv_online`. Their behaviour
is unchanged; what changed is that the contract is now stated once instead of
written twice and assumed everywhere else.

### The compiler named seventeen sites

Exit criterion 1 asks for the `Err(Unsupported)` sites **enumerated by the
compiler**. `DispatchError` has no `From<SolverError>`, so inside
`check_auto_dispatch_inner` every `?` and every `return Err(..)` is a type error
until its site names the rung it belongs to. `rustc` printed **17**:

| what | count | closed as |
|---|---:|---|
| the six rung funnels (`rung_or_decline(DispatchRoute::…, …)?`) | 6 | `DispatchError::at(<that rung>, e)` |
| `datatype-elim` / `datatype-native` / `lira-dpll` / `nra` non-`Unsupported` arms | 4 | `DispatchError::at(<that rung>, e)` |
| the `datatype-native` `Propagate` policy arm (ADR-1980's lever) | 1 | `DispatchError::at(DatatypeNative, …)` |
| `decide_real_poly_constraint` and the two `bv2nat-blast` sub-calls | 3 | `DispatchError::at(Nra / Bv2NatBlast, e)` |
| the `ite` lift (ladder machinery, no rung) | 1 | `DispatchError::ladder(e)` |
| the two TAILS — `dispatch_nonlinear_int_tail` and the bit-blast fallback | 2 | `DispatchError::ladder(e)` |

The two tails are the only sites left without a route, and ADR-1966 already
classified `dispatch_nonlinear_int_tail` the same way — *"terminal — it is the
last rung"*. They stop the ladder whatever they declare, so an ownership
declaration decides nothing about them; declining there would return `Ok(None)`
to a ladder with nothing below it and force the dispatcher to manufacture a
second `unknown` that says strictly less than the one it discarded.

The value of the type is not the one-off list. It is that the list stays
produced by the compiler as the ladder changes: ADR-1966's own instrument went
from 37 sites to 72 the moment it counted tail position, and warned that *"any
future scan of this kind that counts only `?` is under-reporting by about
half"*. Nothing here counts.

### ADR-1966's 72 sites, re-derived

**72 is the number ADR-1966 ENUMERATED; 67 is the number it PINNED**, and the
difference is its own five closures. Confusing the two is the "site count is not
file count" family of error that ADR-1966 itself catalogues (143→6, 51→2,
173→10, 84→49, 27,150→1,135, 19,620→0), one level up.

`scripts/enumerate-dispatch-refusal-propagation.py` re-derived on this tree:

| | pinned at `df5030319` | this tree |
|---|---:|---:|
| `sites_core` | **67** | **67** |
| distinct `(file, fn, kind, callee)` | 63 | 63 |
| `core_with_a_rung_below` | 35 | **34** |
| `can_return_unsupported` (the seed) | 1,206 | 1,222 |
| `dispatch_reachable` | 3,816 | 3,901 |

Two entries change spelling and one real site closes:

- **GONE** `check_auto_dispatch --propagate-?-- check_with_datatype_native`.
  This is the site ADR-1966 sized at +22/−2 and declined to take, and ADR-1980
  took behind a lever. The typed channel is what makes it **no longer a
  propagation at all** — and `core_with_a_rung_below` 35 → 34 is that one site.
- **GONE / NEW** `dispatch_nonlinear_int_tail` moves from
  `check_auto_dispatch` to `check_auto_dispatch_inner`. One site, two
  attributions: the enclosing function resolves as `_inner` now that the ladder
  body carries its own error type. Same classification, and it is ADR-1966's own
  — *"terminal — it is the last rung"*.
- **NEW** `check_auto_dispatch --propagate-tail-- relabel_with_datatype_refusal`,
  visible because the datatype `?` above it is gone. Not a rung: it relabels a
  result the ladder has already produced, and nothing runs after it.

The remaining 62 "intra-route" sites — a CEGAR loop's own sub-solve, an NRA
branch-and-bound relaxation, a warm incremental check — are unchanged, because
**the enclosing function is one route, not a ladder**, and the ownership rule is
about ladders. That classification is ADR-1966's and this ADR does not revisit
it; what it adds is that the sites which ARE ladder rungs can no longer be
written without naming a route.

The pin is updated, and `repin-ratchet.sh` checks BOTH directions rather than
just re-pinning: the clean tree exits 0 (0 new against 63), and a tree with one
bare `?` re-introduced at the `lira-dpll` rung exits non-zero and names that
site. **A gate that "fails" unconditionally looks exactly like a working one
until you check that it also passes when it should** — the inverted control
ADR-1966's own lane caught in itself.

## The two defects this lane's own instruments found

Neither was found by reading, and both would have shipped.

### The fixture was vacuous and the mutation control said so

`route-ownership-ladder`'s first run came back **SURVIVED — 20 tests ran, none
depend on this guard**. The fixture
`the_ladder_reaches_the_route_that_owns_the_construct` was asserting `unsat`
through `check_auto_explained`, and with the default config the word-level
reduction folds `select(store(a,i,v), i)` to `v` BEFORE dispatch. The residual
is pure real, the trail is

    ["probe", "dl-online:Declined", "nra-real-root:Declined", "nra:Decided(Unsat)"]

and `lira-dpll` — the rung the test exists to pin — never runs at all. The test
passed either way.

Its own non-vacuity guard did not catch it, and the reason generalises: the
guard accepted "one of `lira-dpll` | `nra` | `array-fast-path` appeared", and
`nra` appears on the folded trail. **A non-vacuity check that admits a route
other than the one under test is not one.** With `preprocess: false` and an
assertion naming `lira-dpll` exactly, the mutation kills exactly one fixture.

The fixture took three attempts before it reached the rung at all, each caught
by that same guard:

1. `select(store(a,i,v), i) > v` — difference logic, and `dl-online` is a
   COMPLETE decider that runs first. Refuted at `attempts=2`.
2. `3·read > 3·v` — normalises straight back to a difference. Same trail.
3. `3·read − 2·v − w > 0 ∧ w = v` — three distinct symbols in one atom, which
   is what puts it outside difference logic.

ADR-1966's module note records the identical trap from the other end: its first
fixture was refuted by `int-box-eval` at `attempts=3`, before the rung under
test, so it passed on the UNFIXED tree and tested nothing.

### This lane's own trace runner had ADR-2075's bug

`bench-results/route-ownership-20260915/trace-run.sh` anchored on `^; route `
and reported **103 of 645 rows** as having no trace. The watchdog-kill path
prints `; partial route ` — a deliberate prefix — which is exactly the finding
ADR-2075 published four weeks earlier and which cost it twelve files in two
ADRs' censuses. Fixed to `-E '^; (partial )?route '` and the 103 re-captured on
the same binary.

The general shape is worth naming because it has now happened to a lane that had
read the ADR: **a prefix a producer adds is a prefix every consumer must be
written to strip, and prose in an ADR does not make that happen.** ADR-2101's
`partial` FIELD is the structural fix; this runner predates the field reaching
the artifact it reads.

## The A/B

**Two binaries, because ADR-2100 is not a lever.** The ownership rule is
unconditional code, so there is no env value to flip and the arms have to be two
builds — which makes one failure mode possible that a one-binary A/B cannot
have: *the same binary in both arms*, producing a perfect zero that looks
exactly like agreement. `ab-run.sh` refuses unless the two binaries hash
differently, the check ADR-2060's runner established for the same reason.

- **A** = `main` at this branch's merge-base, `6ac97756c9fffe865c3bff7b2e1ef8c807c9ee12`,
  built from a `scripts/lane-snapshot.sh` extraction (`--touch`-stamped, so
  cargo cannot serve a stale artifact for an older commit).
- **B** = this branch.
- Nine divisions × 200 files: the seven Tier 1 divisions plus `QF_LIA` and
  `QF_LRA`. **1,800 rows, 0 malformed.**
- Both arms **back to back on the same file on the same pinned physical core**,
  arm order alternating per file, 24 s wall, 8 GiB `ulimit -v`, 12 shards across
  s5/s6/s7.
- Exit status recorded per arm as **its own column**, never folded into the
  verdict: ADR-2045 measured `losses=0` by verdict and five new ABORTS
  underneath it.

### Why the A arm scores below the published single-arm board, and why that is not a finding

| division | A arm here | published 2026-09-14 board | delta |
|---|---:|---:|---:|
| AUFLIRA | 172 | 178 | −6 |
| UFNIA | 54 | 53 | +1 |
| UFLIA | 78 | 85 | −7 |
| AUFDTLIRA | 117 | 121 | −4 |
| QF_NIA | 61 | 84 | **−23** |
| UF | 78 | 90 | −12 |
| UFDTLIRA | 138 | 144 | −6 |

An interleaved A/B runs **two** 24 s solves per file on one core, at twelve
shards, so every row competes with its own other arm and with eleven siblings;
the published board was a single arm. The same binary has scored **77, 79 and
85** on one division in a single day purely on ambient load. **A single-arm
level is only comparable against another single-arm run at similar load; the
DIFFERENCE is what survives contention**, which is the entire reason the arms
are interleaved rather than swept. The A-arm column above is reported so nobody
reads the B-arm column as a board row, and neither column is one.

### The raw pairing

| division | rows | A | B | net | gain | LOSS | FLIP | `rc` differs | `:status` comparable | disagree |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 117 | 116 | −1 | 2 | 3 | 0 | 0 | 116 | 0 |
| AUFLIRA | 200 | 172 | 172 | +0 | 0 | 0 | 0 | 0 | 172 | 0 |
| QF_LIA | 200 | 115 | 116 | +1 | 1 | 0 | 0 | 0 | 113 | 0 |
| QF_LRA | 200 | 99 | 99 | +0 | 0 | 0 | 0 | **1** | 93 | 0 |
| QF_NIA | 200 | 61 | 62 | +1 | 1 | 0 | 0 | 0 | 62 | 0 |
| UF | 200 | 78 | 78 | +0 | 0 | 0 | 0 | 0 | 76 | 0 |
| UFDTLIRA | 200 | 138 | 140 | +2 | 2 | 0 | 0 | 0 | 140 | 0 |
| UFLIA | 200 | 78 | 78 | +0 | 0 | 0 | 0 | 0 | 78 | 0 |
| UFNIA | 200 | 54 | 53 | −1 | 0 | 1 | 0 | 0 | 15 | 0 |
| **total** | **1,800** | **912** | **914** | **+2** | **6** | **4** | **0** | **1** | **865** | **0** |

**0 malformed rows.** ADR-1966 had to exclude 39 by name because the harness
wrote a refusal sentence into the row; reading a parse failure of the results
file as "no movement" is how a measurement manufactures a null, so the count is
published even when it is zero.

### Every moved row re-run THREE TIMES PER ARM

Reporting the raw column alone would overstate both directions. ADR-1966
reported 25 raw movers and 22 after re-checking — **11 of its 18 movers outside
the treatment division vanished**. All 11 rows that moved here (verdict OR exit
status) were re-run 3× per arm on one pinned physical core at the same 24 s /
8 GiB envelope, arms alternating within the three passes:

| classification | rows |
|---|---:|
| **STABLE-GAIN** (A never decided, B decided 3/3) | **2** |
| **STABLE-LOSS** (A decided 3/3, B never decided) | **2** |
| BOTH-DECIDE (the pairing's difference was ambient) | 5 |
| NEITHER-DECIDES | 1 |
| UNSTABLE | 1 |

- **STABLE-GAIN**: `AUFDTLIRA/…/N624-020__perm_rem__perm.adb_130_45_index_check2`,
  `UFDTLIRA/…/Q327-014__no_pre__dispatch.adb_24_24_overflow_check`.
- **STABLE-LOSS**: `AUFDTLIRA/…/Q525-025__controlling_result__fixed_string.adb_18_11_length_check`,
  `AUFDTLIRA/…/R509-011__higher_order_proof__why_bfafe7_…fold-T-defqtvc`.
- **UNSTABLE**: `UFNIA/sledgehammer/FFT/z3.885941.smt2`, A `unsat/unknown/unsat`.
  This is the row ADR-2030 and ADR-2035 both name as *"the same row that produced
  EVERY loss in both arms"* and which ADR-2035 re-ran UNSTABLE in the opposite
  direction. It is a budget-boundary file, not a signal.
- **The one exit-status difference is ambient.** `QF_LRA/LassoRanker/…/yPositive-SIscaled50…`
  came back `none/134` on **all six passes, both arms**. The single pairing had A
  abort and B not; re-run, both abort identically. **0 exit-status differences
  after re-check.**

**Net: +2 / −2 = 0. Zero `sat`↔`unsat` flips, in the raw pairing and in every
re-check pass. 865 comparisons against the files' declared `:status`, 0
disagreements** — with the comparable denominator published beside the zero
because 49 decided rows carry no `:status` at all, and ADR-1966 published a
"three-way check" one of whose authorities was comparable on 0 of 23.

### Exit criterion 3 is NOT MET, and the two losses are the documented cost of this change class

The criterion is **0 losses**. There are **2**, both reproducible 3/3, and
saying so is the point of measuring.

Both are exactly the mechanism ADR-1966 measured and named, and one of the two
files is *literally in ADR-1966's own loss list*:

> two `…higher_ordermnfold-T-defqtvc…` files — base `unsat` 3/3, fixed `unknown`
> 3/3. **Real, reproducible losses.** The ladder now runs to `attempts=20` and
> `attempts=43` instead of 8 and 15, and spends the budget.

#### The mechanism, read off both arms' trails rather than assumed

A loss count is not a diagnosis. `why-lost.sh` runs both arms with `--trace` on
one pinned core at the same envelope, and the two rows say the same thing:

```
Q525-025 …length_check
  A unsat    route decided_by=q:egraph bound_by=q:mbqi last=q:egraph bound_ms=10616 total_ms=14822 attempts=35
  B unknown  give-up kind=Watchdog
             partial route decided_by=none bound_by=q:mbqi last=q:egraph bound_ms=10599 total_ms=15528 attempts=25

why_bfafe7 …fold-T-defqtvc
  A unsat    route decided_by=q:egraph bound_by=q:mbqi last=q:egraph bound_ms=10425 total_ms=14362 attempts=45
  B unknown  give-up kind=Watchdog
             partial route decided_by=none bound_by=q:mbqi last=q:egraph bound_ms=10428 total_ms=15322 attempts=25
```

**Nothing about the ROUTING of the quantified ladder changed.** `decided_by` in
A and `last` in B are the SAME route, `q:egraph`; `bound_by` is `q:mbqi` in both
and costs the same to the millisecond (10,616 vs 10,599; 10,425 vs 10,428). What
changed is the price of an attempt: **the same fifteen seconds buys 25 attempts
instead of 35 and 45.** Each quantified rung decides its sub-query through
`check_auto`, and a sub-solve that used to stop at a rung's terminal `Unknown`
now runs the rest of the quantifier-free ladder. `q:egraph` therefore never
reaches the instantiation round that refutes, and the watchdog fires.

That is ADR-1927's own cost note made concrete a second time — *"the refusal was
fast because it was wrong"* — and ADR-1966's `UFLIA` control lost one file to
exactly this while being structurally unable to trigger its guard at all. The
general form is theirs: **the cost of this change is not confined to the queries
whose refusal it converts.**

What this ADR will not do is trade the rule for the two files. The obvious
narrowings — declare more, exempt the datatype branch, re-order — each put a
route back in the position of deciding on another route's behalf, which is the
defect. The honest accounting is **net 0 verdicts, 0 flips, 0 soundness
disagreements, 0 exit-status differences, and a bug class closed**, with the two
files named so a later lane can take them rather than rediscover them.

## What this ADR does NOT claim

- **No new theory capability.** Nothing in the datatype, UF, array, NRA or
  arithmetic backends changed; the same routes decide the same fragments. What
  changed is which routes get to run, and on what authority.
- **The quantified ladder in `solve` is untouched.** It is a different ladder
  with its own decline discipline (ADR-1927), and **75 % of Tier 1's undecided
  mass ends there**. Typing its rungs the same way is the obvious next slice and
  nothing here is evidence about it.
- **The refusal SENTENCE an undecided file ends on can change.** When a route's
  `Unknown` becomes a decline and nothing below decides either, the message the
  caller sees is the tail's rather than that route's. ADR-1980 built
  `relabel_with_datatype_refusal` for exactly this on the datatype branch and it
  is untouched; outside that branch the tail's sentence now wins on the affected
  rows. A verdict A/B cannot see that, and a blocker census keyed on those
  strings should be re-taken rather than inherited — which is ADR-1927's own
  headline finding pointing at this change.
- **`bv2nat-blast` and `abv-online-cdclt` did not change behaviour.** Both
  already implemented the `FastPath` contract by hand; only their labels now
  come from the declaration. That their hand-written behaviour matches the
  general contract is evidence the contract is the right one, not a result.
- **The 40 Tier 1 rows that were NOT `stopped_by_unknown`** already let the
  ladder continue before this change. The rule has nothing to do for them and
  they are outside every number here.
- **The capability ratchet's five artifacts are deliberately NOT re-pinned.**
  `progress_frontier` passed 12 of 12 with every family `comparable: true`,
  `ratchetable: true`, `verdict: ok`, and it rewrote its own JSON on the way
  through — one family, `bv_reduction`, reading **38 against a committed 39**
  (baseline 30, so far above the ratchet). That family's committed history is
  **40 → 34 → 39** at a fixed baseline, so one point is inside its own
  variance and a single run is not grounds to move a shared pin in either
  direction — `frontier-ratchet-reference-frame.md`'s own rule. The artifacts
  are restored; the observation is recorded here instead of being re-pinned
  silently or dropped.

## Exit criteria, each MET or NOT MET

**1. Every `Err(Unsupported)` site in the ladder reachable only from a route
that does not own the construct, enumerated by the COMPILER — MET, with two
sites named as exceptions.** `DispatchError` has no `From<SolverError>`, so
`rustc` named **17** sites in `check_auto_dispatch_inner`; fifteen are closed by
`DispatchError::at(<rung>, e)` and the ownership rule, and two — the int tail and
the bit-blast fallback — carry `DispatchError::ladder` because they are terminal
by position and have no route below to hand anything to, which is ADR-1966's own
classification of the first. ADR-1966's population re-derived: `sites_core`
**67 → 67**, `core_with_a_rung_below` **35 → 34**, the removal being the
datatype `?` the typed channel closes. The pin is updated and `repin-ratchet.sh`
proves the ratchet still fires on a re-introduced site.

**2. The named suites green with `hand_back_unless_refuted` DELETED — MET.**
All **19** suites of `hooks/pre-push`'s `dispatch/reason:` block (the list read
out of the hook, not retyped), plus `datatype_native` (24), `datatype_elim` (6)
and `datatype_int_fields` (5), plus all **93** `auto::tests`. The whole solver
unit sweep is **1,805 passed / 0 failed**; `corpus_regression` 2/2;
`progress_frontier` **12/12 with no frontier regression**. Five assertions in
`lra_opaque_real_apps` were RELOCATED rather than weakened (ADR-1980's method),
and the suite's module comment carries the four-row table of which went where.

**3. Interleaved A/B, 0 losses / 0 flips / identical exit status — NOT MET on
losses; MET on flips and exit status.**

| channel | required | measured |
|---|---|---|
| `sat`↔`unsat` flips | 0 | **0** — raw pairing and every re-check pass |
| exit status | identical per file | **0 differences after re-check** (the one raw difference is `none/134` on all six passes of both arms) |
| losses | 0 | **2**, reproducible 3/3, named below |
| soundness | — | **865 comparisons vs `:status`, 0 disagreements** |
| net verdicts | — | **+2 / −2 = 0** over 1,800 rows |

The two stable losses are
`AUFDTLIRA/…/Q525-025__controlling_result__fixed_string.adb_18_11_length_check`
and `AUFDTLIRA/…/R509-011__higher_order_proof__why_bfafe7_…fold-T-defqtvc`. The
second is **literally one of the two files ADR-1966 named as its own real,
reproducible losses** from the identical mechanism.

**4. Mutation: delete the ownership check on one route, exactly one named
fixture dies — MET.**

| mutation | suite run | kills |
|---|---|---|
| the ownership check on a decider's non-decision | `--test lra_opaque_real_apps` | **exactly 1**: `the_ladder_reaches_the_route_that_owns_the_construct` |
| the inconsistency report on an owning decider's refusal | `--lib auto::tests::` | 1: `an_owning_deciders_refusal_is_reported_and_a_declining_routes_is_not` |
| the `FastPath`/`Decider` distinction | `--lib auto::tests::` | 2 |

Registered as `route-ownership-ladder` and `route-ownership-marker` in
`scripts/tests/mutation_controls.py`; `--check-anchors` reports
`suites=133|anchors=1055|stale=0`. **The first run of the first mutation came
back SURVIVED**, and that is how the vacuous fixture above was found.

**5. The sizing stated up front — MET, and the number is 0.** It is under ten,
so this ADR says in its own sizing section that **Phase 1 is worth doing for the
bug class** rather than implying a gain, which is what the criterion asks for.

[1965]: adr-1965-the-nested-array-prize-was-never-the-array-theory-it-was-congruence.md
[1927]: adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md
[1955]: adr-1955-the-nested-array-sort-is-the-first-of-three-gates-and-the-only-one-the-ir-owns.md
[1966]: adr-1966-a-rungs-refusal-of-a-construct-a-later-rung-owns-is-a-decline.md
[1980]: adr-1980-the-cheap-check-was-the-whole-target-a-dispatch-decline-not-a-datatype-capability.md
[2030]: adr-2030-the-fallback-was-already-offered-and-the-lemma-batch-is-the-whole-set-at-once.md
[2060]: adr-2060-the-give-up-variant-could-not-tell-six-gates-apart-and-nothing-asked-it-to.md
[2065]: adr-2065-the-real-collector-can-hold-a-term-and-the-sat-exits-close-by-type.md
