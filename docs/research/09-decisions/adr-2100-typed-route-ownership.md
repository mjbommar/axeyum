# ADR-2100: typed route ownership — whether the ladder stops is a declaration on the route, not the error variant a function returned

Status: proposed
Index-summary: DRAFT — the design note landed first so the ownership table could
be reviewed before any dispatch code moved. Sizing, implementation and the
interleaved A/B follow in this same file.
Index-status: proposed
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

`scripts/enumerate-dispatch-refusal-propagation.py` still runs, and its pinned
baseline is `bench-results/dispatch-decline-audit-20260913/refusal-propagation-baseline.json`.
Re-derived on this tree, the population and its classification are unchanged
except for the one site this ADR moves: `check_auto_dispatch` →
`check_with_datatype_native` was already converted by ADR-1980, and the
remaining 62 "intra-route" sites — a CEGAR loop's own sub-solve, an NRA
branch-and-bound relaxation, a warm incremental check — are unchanged, because
**the enclosing function is one route, not a ladder**, and the ownership rule is
about ladders. That classification is ADR-1966's and this ADR does not revisit
it; what it adds is that the ten sites which ARE ladder rungs can no longer be
written without naming a route.

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

## Exit criteria

1. Every `Err(Unsupported)` site in `auto.rs` reachable only from a route that
   does not own the construct, enumerated by the compiler; [1966]'s 72 sites
   re-derived on this tree, each closed by the declaration or listed with a
   reason.
2. The nine named suites plus the whole 19-suite `dispatch/reason:` block green
   **with `hand_back_unless_refuted` deleted**.
3. Interleaved per-file A/B on the seven Tier 1 divisions plus `QF_LIA` and
   `QF_LRA`: 0 losses, 0 `sat`↔`unsat` flips, identical exit status per file.
4. Mutation: delete the ownership check on one route, exactly one named fixture
   dies; the anchor registered in `scripts/tests/mutation_controls.py`.
5. The sizing number above, stated up front. **If it is under ten, Phase 1 is
   still worth doing for the bug class**, and this ADR says so rather than
   implying a gain.

[1965]: adr-1965-the-nested-array-prize-was-never-the-array-theory-it-was-congruence.md
[1927]: adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md
[1955]: adr-1955-the-nested-array-sort-is-the-first-of-three-gates-and-the-only-one-the-ir-owns.md
[1966]: adr-1966-a-rungs-refusal-of-a-construct-a-later-rung-owns-is-a-decline.md
[1980]: adr-1980-the-cheap-check-was-the-whole-target-a-dispatch-decline-not-a-datatype-capability.md
[2030]: adr-2030-the-fallback-was-already-offered-and-the-lemma-batch-is-the-whole-set-at-once.md
[2060]: adr-2060-the-give-up-variant-could-not-tell-six-gates-apart-and-nothing-asked-it-to.md
[2065]: adr-2065-the-real-collector-can-hold-a-term-and-the-sat-exits-close-by-type.md
