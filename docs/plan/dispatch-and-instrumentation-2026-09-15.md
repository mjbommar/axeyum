# Dispatch and instrumentation: a plan

**2026-09-15.** Four phases, sequenced by dependency, each with an exit criterion
that can fail. Written after eleven lanes on the quantified divisions measured
budget policy at zero from every angle and found, instead, one dispatch bug five
times and five instruments that reported the wrong thing.

## 0. The evidence this plan rests on

Every claim below is measured and merged; the ADR is the receipt.

**One dispatch bug, five times.** A rung has two ways to not decide: return
`Err(Unsupported)` ("not mine — keep going") or `Ok(Unknown)` ("mine, tried,
failed — stop"). The distinction is correct. **It is decided per call site by
which variant a function returns**, with 32 refusal sites in `auto.rs` alone and
nothing that checks consistency across them.

| ADR | what happened |
|---|---|
| 1927 | a rung's refusal of a construct a later rung owns became the query's verdict |
| 1966 | enumerated 72 such sites; a `?`-only scan found half; sized the largest at +22 and reverted it — it turned 7 assertions red in four other ADRs' suites |
| 1980 | landed that site by relocating the assertions: **+79 across three divisions** |
| 2030 | "missing wiring" refuted — the fallback WAS offered; an ordered probe was needed to separate "never reached the site" from "reached it and came out the other side" |
| 2065 | a rung that started ADMITTING an atom silently became an owner, so its decline stopped the ladder; a fixture obligation broke; fixed at zero cost by handing the refusal back |

Each fix was local. The next instance is guaranteed.

**Five instruments that lied, one shape.** Every instrument reports through a
**string**, every consumer reads it with a **grep**, and nothing typechecks the
contract between them.

| ADR | the instrument | how it lied |
|---|---|---|
| 2075 | route trace | census grepped `^; route `; the watchdog path prints `; partial route ` — a DELIBERATE prefix whose consumer half was never written. Twelve files printing fourteen diagnostic lines each were "the second-largest unexplained bucket" in two ADRs |
| 2060 | give-up reason | one string for **28 program points and 15 causes**; an `i128` overflow reported as a timeout; the route's two trust anchors (model replay, Farkas self-check) rendered as a clock expiring |
| 2020 | census separator | split on `;` when the `why=` field contains `;`; truncated its own largest bucket |
| 2085 | staleness gate | `git log -G<symbol>` matches patch TEXT; a function body does not repeat its own name; flagged doc comments and tests, missed 16 real rows |
| 2065 | a lane's enumerator | cut each file at the first `#[cfg(test)]` — which is mid-file — dropping 5,500 lines of production code and printing a clean answer |

**What already exists and is under-used.** `route_trace.rs` records every attempt
as a struct (`RouteTrace { attempts: Vec<RouteAttempt>, elapsed: Vec<Duration> }`)
with a byte-stable `to_json()` — and every census re-parses the CLI's prose
rendering of it instead. `portfolio.rs` (1,075 lines) races arms on separate
cores, with the right analysis of when that beats sequencing — and is wired at
**one** site with two arms. `config_registry.rs` enumerates **488** constants,
100 dated; ladder order and budget shares are literals in source.

**What does not exist.** Any accumulation of outcomes across runs. Every sweep
this week produced `(file → route that decided → elapsed → routes declined and
why)` and discarded it after one comparison.

## 1. Non-goals, stated so they are not drifted into

- **Not a rewrite of `auto.rs`.** The ladder's shape is fine; its *ownership
  contract* is untyped. Fix the contract.
- **Not a new dispatch algorithm.** The portfolio's own docstring says where
  racing beats sequencing (two routes each needing most of one clock) and where
  it does not. Widen it to where the data says; do not replace the ladder.
- **Not machine learning.** Phase 3 is a table. Phase 4 derives constants from
  the table. Anything past that is a decision for after Phase 4 shows what the
  table contains.
- **Not a numerator lane.** None of these phases is measured in files decided.
  Phase 1 is measured in bug class killed; Phase 2 in censuses that cannot lie
  that way again; Phase 3 in questions answerable in one query that today cost
  a lane. A phase that ships a capability gain on the side is welcome and is
  reported separately.

## 2. Phase 1 — typed route ownership

**Goal.** Whether the ladder stops after a rung is decided by a **declaration on
the route**, not by which error variant a function returned.

**Shape.** Each route declares the constructs it owns (a `Features` predicate —
the scan already exists). The ladder, on a non-decision, consults the declaration:
a route that does not own the query's constructs cannot stop the ladder no matter
what it returned; one that does, can. `Err(Unsupported)` from an owning route is
then a **bug the type system reports**, not a silent fall-through.

**Why this and not another local fix.** ADR-2065's fix — `hand_back_unless_refuted`
— is correct and is exactly this rule, hand-written for one rung: "if the
abstraction admitted an atom and did not refute, return the refusal the route
would have returned without it." Phase 1 is that rule for every rung, stated
once.

**Exit criteria, each of which can fail:**
1. Every one of the 32 `Err(Unsupported)` sites in `auto.rs` is reachable ONLY
   from a route that does not own the construct — enumerated **by the compiler**
   (give the declaration a payload and let type errors list the sites; ADR-2060
   did this and found 28 where a name scan found 6).
2. ADR-1966's 72 enumerated sites re-derived on the new tree; every one is
   either closed by the declaration or listed with a reason.
3. The five ADRs' regression fixtures (`dispatch_rung_refusal_declines`,
   `nested_array_gate_map`, the four DT suites, `lra_opaque_real_apps`) all
   green **with `hand_back_unless_refuted` deleted** — the general rule must
   subsume the local one, or it is not the general rule.
4. Interleaved A/B on every Tier 1 division: **0 losses, 0 flips, exit status
   identical.** Gains are reported but are not the criterion.
5. Mutation: delete the ownership check on one route and require that exactly
   one fixture dies. Six of seven guards in one suite here were removable with
   everything still green.

**Sizing before building.** Count, on the current tree, how many undecided rows
end with `decided_by=none` AND have a route below the last-attempted one that
declares ownership of their features. That is the ceiling. If it is under ten
across Tier 1, Phase 1 is still worth doing for the bug class, and the ADR says
so rather than implying a gain.

**What Phase 1 must not do.** Weaken a fixture. ADR-1966 was reverted for turning
seven assertions red; ADR-1980 landed the same change by relocating them to
where their guard actually lives. Expect that and do the same.

## 3. Phase 2 — the trace is the API; the prose is a rendering

**Goal.** No census, gate or lane reads a `; route` line. They read `RouteTrace`.

**Shape.**
- The CLI emits `to_json()` (it exists, byte-stable, tested) as the primary
  artifact per file — one JSON object, complete OR partial, with the
  completeness a **field** rather than a prefix.
- The 32 route names become an `enum` with `Display`. A census that names a
  route that does not exist fails to compile.
- The give-up vocabulary gets the ADR-2060 treatment where it has not had it:
  every terminal reason is a variant with a detail, the exhaustive `name()`
  refusing to compile until each producer is named, and a test that DRIVES each
  producer rather than listing it.
- One shared reader (`bench-results/*/census.py` today, N copies) becomes one
  library function that parses the JSON and exposes `decided_by`, `bound_by`,
  `attempts`, `elapsed`, `partial`, and the decline reasons — so the separator
  bug (ADR-2020) and the prefix bug (ADR-2075) are structurally impossible.

**Exit criteria:**
1. Every existing census script under `bench-results/` that reads `; route`
   either reads the JSON or is deleted, with the count published.
2. ADR-2075's twelve rows, ADR-2020's truncated bucket, and ADR-2060's 28 sites
   are each re-derived through the new reader and match the corrected ADR
   figures. **A reader that reproduces the OLD wrong numbers is the failure
   mode** — check it reproduces the corrected ones.
3. The `partial` field is exercised by a positive control: a run killed
   mid-search yields a JSON object the reader accepts with `partial: true`, and
   an aggregate that sums `decided_by` over a mix refuses unless told to
   include partials.
4. Verdict invariance still pinned: `check_auto_explained(..).map(|(r,_)| r) ==
   check_auto(..)` over the deterministic corpus, unchanged.

**What Phase 2 must not do.** Break the human-readable lines. They stay, derived
from the JSON, for `git grep` and for eyes. The rule is direction: JSON → prose,
never prose → parse.

## 4. Phase 3 — the outcome ledger

**Goal.** One table, appended by every sweep, that answers in one query the
questions that today cost a lane each.

**Schema (per file, per run):**

    corpus_path      -- the PATH, not the basename (ADR board-ab-20260914: 370 of
                        3,200 basenames are ambiguous; the canonical board's
                        population is not reconstructible from what is committed)
    binary_sha       -- the tree, so a row cannot be mis-attributed to main
    features         -- the `Features` scan, serialised
    verdict          -- sat / unsat / unknown / abort, with EXIT STATUS as its
                        own column (ADR-2045: `losses=0` by verdict, five new aborts)
    decided_by       -- route enum, or none
    bound_by         -- route enum
    attempts         -- count, plus the ordered trail
    elapsed_ms       -- total and per attempt
    partial          -- bool
    decline_reasons  -- the typed reasons, per attempt
    host, core, load -- so a level can be read against its conditions (the same
                        binary scored 77/79/85 on one division in one day)

**Why this is worth a phase on its own.** This week's lanes each spent a day
re-deriving a population that a previous lane had already measured and
discarded. ADR-2035 found 8 of 22 "declining" rows decided anyway; ADR-2050
re-derived 13 rows per-row to check an inherited list; core-select is
re-deriving 1,400 rows right now. With the ledger, "which files does route X
decide, in how long, on what features, and did that change at commit Y" is a
query.

**Exit criteria:**
1. The board A/B runner, the Tier 1 runner and the per-lane A/B runner all
   append to it. Three writers, one schema.
2. Three questions answered from the ledger alone, each cross-checked against
   the ADR that originally measured it: ADR-2065's 14 movers; ADR-2045's 74-of-93
   one-route bucket; ADR-2075's nine partial rows.
3. A staleness rule: a row whose `binary_sha` is not an ancestor of `main` is
   flagged, so a branch measurement cannot be read as a main one.

**What Phase 3 must not do.** Replace the A/B. The ledger records; the
interleaved A/B is still how a claim is made. A ledger-derived delta between two
single-arm runs at different loads is the 77/79/85 error with a database in
front of it.

## 5. Phase 4 — derived ladder policy (conditional)

**Runs only if Phase 3's ledger shows structure.** Specifically: if, for some
feature class, one route decides a large majority of what gets decided and a
different route is tried first, then ladder order for that class should come
from the table.

**Shape.** Per feature class: order routes by (decision rate, then median
elapsed) from the ledger. The 488 constants' budget shares become derived
defaults with the hand-set value as an override. `config_registry.rs` already
records which constants are dated — the ledger makes them RE-datable
automatically.

**Exit criteria:**
1. A derived order for at least one feature class, A/B'd interleaved against
   the hand-set order on every division that class touches. **Losses count;
   gains are the goal.**
2. The portfolio widened to exactly the rungs where the ledger shows two routes
   each needing ≥50 % of a clock on the same files — its own docstring's
   criterion, now measured rather than asserted.
3. Every constant whose derived value differs from its hand-set value by more
   than its own noise band is listed, with the measurement, in one ADR.

**What Phase 4 must not do.** Learn from a single run. The ledger's minimum for
deriving a default is the same as this repository's minimum for claiming a gain:
three passes per arm, a published noise floor, and an interleaved comparison.

## 6. Sequencing and dependencies

    Phase 1 (ownership)  ──┐
                           ├──▶  Phase 3 (ledger)  ──▶  Phase 4 (derived policy)
    Phase 2 (trace API)  ──┘

Phases 1 and 2 are independent and can run as parallel lanes. Phase 3 needs
Phase 2's typed reasons (or it stores strings and inherits the bug). Phase 4
needs Phase 3's table.

**Each phase is one lane, one ADR, and lands on its own.** A phase that is half
done is reported as half done with the exit criteria it met listed — this
repository's standing rule is that a keystone is sliced and each slice ships,
not deferred to "fresh context".

## 7. Risks, named so they can be watched

- **Phase 1 turns fixtures red.** Expected (ADR-1966 did). The response is
  relocation, never deletion.
- **Phase 2's JSON becomes a second thing that drifts.** Mitigated by the
  direction rule (JSON → prose) and by the reader being one function.
- **Phase 3 becomes the number.** The ledger is not a board. Every aggregate it
  serves must carry `binary_sha`, load, and `partial` — or it is the single-arm
  error again.
- **Phase 4 optimises the sample.** The 200-file pinned lists are what we
  measure on; the corpus is 60× larger. A derived order is checked on a held-out
  draw before it ships.

## 8. What to do first

**Phase 1 and Phase 2 as two lanes, today.** Both have a compiler-enumerable
exit criterion, both close a bug class rather than an instance, and neither is
measured in files — so neither can be tempted into shipping a lever to have a
number. Phase 3 follows the moment Phase 2's typed reasons land.

## 9. Outcome (2026-09-15, end of day)

Every phase ran; each has an ADR with its exit criteria marked MET or NOT MET.

| phase | ADR | verdict |
|---|---|---|
| 1 | 2100 | ownership typed on the QF ladder; `hand_back_unless_refuted` deleted; sizing **0 of 645**; A/B net 0 with two stable losses |
| 1b | 2103 | same rule on the `q:*` ladder; eight bare `?`s closed; bounded continuation; A/B **net +4, 0 stable losses**, the two losses recovered |
| 2 | 2101 | `partial` a field, `Route` a type, one reader; three live consumer defects found by the migration |
| 2b | 2104 | 25 decline details typed (not 44 — helper callers); three orphan controls registered |
| 3 | 2102 | one ledger, three writers; ADR-2065's 14 movers reproduced exactly from rows |
| 3b | 2105 | typed name and construct set in the trail; the process-global recorder deleted |
| 4 pre | — | structure on 5 of 12 groups; two with a ceiling in time |
| 4 | 2106 | order is data; derived order **27–35× faster and 8–11 files worse** on both draws; hand order ships |

**What it bought.** The refuse/decline bug class is closed by construction on
both ladders; the instruments read a typed trail instead of prose; a question
that cost a lane costs a query. **What it did not buy.** Files: neither ladder
had a routing gain hiding in it (0 of 645, 0 of 482), and the one derived order
that the ledger justified loses files at the budget even while running an order
of magnitude faster. That is the plan's non-goal confirmed by measurement: the
lever for the board is capability, and two independent instruments (PLAN-SIZING
604/645 stopped on `Unknown`; ADR-2090's 193 of 230 failed on z3's own minimal
core) point at the same four give-up classes in the quantified engine.

**Still open from this plan.** `int-real-relax` decides 0 of 198 QF_NIA/Int
rows while costing 754 s (ADR-2106); the order table cannot express budget
dependence; the `AlgS` shape duplicates red the hygiene gate on any host with a
fresh `shape_search` binary (not this plan's).
