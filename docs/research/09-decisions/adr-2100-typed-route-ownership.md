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

**The number first, because the exit criterion asks for it up front: 0 of 643.**

Method: all seven Tier 1 divisions, 200 files each, the **645 rows the
2026-09-14 board left undecided**, re-run single-arm with `--trace` at 24 s /
8 GiB `ulimit -v` on 12 pinned physical core pairs across s5/s6/s7 (two came
back `unsat` this time, an ambient flip in the other direction, leaving 643).
Then, per row: the last dispatch-ladder rung on its `; route-trail`, and whether
a route BELOW it both **owns** the query's constructs and is **enterable** on
them.

| division | undecided rows | a route below owns | …and is enterable | never reached the ladder |
|---|---:|---:|---:|---:|
| AUFDTLIRA | 78 | 0 | 0 | 68 |
| AUFLIRA | 22 | 0 | 0 | 14 |
| QF_NIA | 116 | 0 | 0 | 1 |
| UF | 110 | 0 | 0 | 79 |
| UFDTLIRA | 56 | 0 | 0 | 52 |
| UFLIA | 115 | 0 | 0 | 92 |
| UFNIA | 146 | **5** | **0** | 124 |
| **total** | **643** | **5** | **0** | **430** |

Artifacts: `bench-results/route-ownership-20260915/` — `trace-run.sh`,
`launch-trace.sh`, `size-ceiling.py`, the raw per-row trails in
`trace-tier1-undecided.tsv`, and the run in `sizing.txt`.

**Phase 1 is still worth doing, and this ADR says so rather than implying a
gain.** The dispatch plan says the same in advance: *"None of these phases is
measured in files decided. Phase 1 is measured in bug class killed."* The five
ADRs above cost roughly a lane each and four of the five were found by accident
while chasing something else; the fifth (ADR-1966) enumerated 72 sites
mechanically and then had to be reverted. What this buys is that the next
instance is a compile error or a named trail entry rather than a sixth ADR.

### Three corrections the sizing produced, each of which would have been a claim

**The first number was 102 and it was wrong, in the direction that flatters the
lane.** `size-ceiling.py`'s first run reported 102 of 116 `QF_NIA` rows
reachable, every one with `owner-below=qf-bv`. The ladder order it used was read
off the SOURCE TEXT, and `dispatch_nonlinear_int_tail` is reached as
`return dispatch_nonlinear_int_tail(..)` inside `if features.has_int` — so
`qf-bv`, textually below it, is unreachable from any integer query. **A route
ordering read off the text rather than off the control flow bounds nothing.**

**The second number was 5 and it was also wrong.** All five remaining rows named
`array-fast-path` as the owner below, which owns `{…, Int, …}` and runs only
`if features.has_array`. Owning a construct and being ENTERABLE on a query are
different questions, and the second is what decides whether the route gets a
turn. Confirmed against the corpus text: **0 occurrences of `Array` in any of
the five** (`UFNIA/2019-Preiner/qf/t3_rw{353,597,658,1283,1466}.smt2`). Each
correction is in the script as a comment beside the rule that implements it, so
the next reader does not re-derive them.

**The finding worth more than the ceiling: 430 of 643 undecided Tier 1 rows —
67 % — never reach the quantifier-free dispatch ladder at all.** Their whole
budget goes to the `q:` rungs of the quantified ladder in `solve`, which is a
different ladder with its own decline discipline (ADR-1927). No amount of
quantifier-free route ownership can move them. That is a statement about where
the remaining Tier 1 mass is, and it is measured rather than asserted: the
per-row trails are committed.

### What the sizing does NOT say

It does not bound the change's effect on **decided** rows, which is the risk
side and is what the A/B in criterion 3 measures. ADR-1966's `UFLIA` control —
chosen because nothing in it could trigger the guard — still lost one file
reproducibly, because a route the ladder now reaches ate the budget the deciding
route needed. A ceiling of 0 on the undecided population says nothing about
that.

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
