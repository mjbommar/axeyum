# ADR-1801: An admission bound that fires on every lost file is not protecting the search

Status: accepted
Date: 2026-09-08
Index-summary: Measured on the committed 200-file `QF_UFLIA` list after the 2026-09-08 reachability fix: on 44 of the 50 files we lose, the last route reached is the online EUF+LIA combination — the architecture Z3 and cvc5 both use — and it refuses 40 of them in under a millisecond on two admission ceilings, `MAX_BOOLEAN_ATOMS = 512` (27 files, observed atom counts 595–2,972) and a 64-pair interface-split ceiling (13). Both are justified by doc comments that say the *deadline-aware spine, not admission* should decide tractability; neither had ever been measured against a population. This ADR sets the rule the two changes follow: an admission bound whose stated purpose is to defer to a deadline must be measured against the population it admits, and where the route below it honours the deadline the bound is raised to where the route stops deciding rather than kept at where somebody guessed. The interface ceiling is NOT raised — pairs are quadratic in the interface-term count, so raising it removes a termination bound — and is answered instead by a care-graph filter plus truncation, which is sound in both directions (`sat` replay-gated, `unsat` a relaxation refutation) and incomplete by construction.
Index-status: accepted

## Context

Three facts, all measured on 2026-09-08 and all on the committed 200-file
`QF_UFLIA` division list under the parity protocol (24 s, 8 GiB, one file at a
time), sharded across three idle 16-core hosts. The full diary is
[`uflia-interface-caps-2026-09-08.md`](../12-performance/uflia-interface-caps-2026-09-08.md).

**1. The route that matches both reference solvers runs now, and gives up
instantly.** The `euf-driver-mbtc` lane made the online model-based EUF + LIA
combination reachable earlier the same day
([`uf-arith-overbound-2026-09-08.md`](../12-performance/uf-arith-overbound-2026-09-08.md)).
On the 50 files we still lose, 44 are watchdog timeouts, and on **all 44** the
last route reached is `uf-arith-online`. It declines 40 of them in 0.1–0.3 ms:

| what it reported | files | the operative guard |
|---|---:|---|
| `too many theory atoms … N > 512` | 27 | `uflia_online::MAX_BOOLEAN_ATOMS` |
| `incremental combined state could not be built safely` | 8 | `combined_theory_lia::MAX_SPLIT_PAIRS = 64` |
| `too many interface pairs for the online combination split` | 5 | the same 64 |
| `combined CDCL(T) leaf did not rebuild a replaying model` | 4 | a genuine leaf failure |

**2. Both ceilings are justified by a doc comment whose own argument says they
should not be doing this.** `MAX_BOOLEAN_ATOMS`'s doc: *"deliberately above the
current `QF_AUFLIA` fair-slice frontier (`bug330` has 339 atoms) so the
deadline-aware CDCL(T) spine, not admission, decides whether that scalar
abstraction is tractable."* The registry recorded its justification as
`undated("doc comment")`. It had never been measured against a population, and
the population it meets is 595–2,972 atoms — one to six times the ceiling.

**3. Two of the four reported strings did not name their own cause.** The
"could not be built safely" string is the caller's rendering of a bare `None`
with four causes (a deadline, a partition failure, an arena error, and the
64-pair ceiling), and reads as a safety property rather than a capacity bound.
That is the third time in two days a printed reason in this tree was not the
operative one.

## Decision

**1. An admission bound whose stated purpose is to defer to a deadline must be
measured against the population it admits, and re-derived from that measurement
or reclassified.**

A bound like `MAX_BOOLEAN_ATOMS` makes a falsifiable claim: *above me, the route
below could not finish anyway, so refusing is free*. That claim is checkable in
one sweep, and on this division it was false for 27 files. The rule this ADR
sets is that such a bound carries a `dated` justification naming the sweep, and
its value is chosen from two measured quantities:

- the largest size at which the route below is **observed to decide** within the
  budget, and
- the largest size at which admitting the query is **observed to cost** a file
  the solver previously decided.

Where the second is absent — where the route below honours the deadline and a
refused query is simply a query nobody tried — the bound is raised past the
first. Refusing at a size the route decides is not protection; it is the
solver declining to try.

**2. A bound whose cost is superlinear in the admitted size is NOT raised. It is
answered with a filter.**

The interface-pair ceiling is the counter-example that keeps rule 1 honest.
`interface_pairs` proposes **every** unordered pair of atomic integer terms with
at least one EUF endpoint, so the proposal is quadratic in the interface-term
count and the DFS branches up to three ways per pair. Raising 64 to admit a
221-pair query (`hard12.smt2`, measured) does not admit a bigger search, it
removes the termination bound. So the value stays and the **proposal** changes:

- `UfliaInterfacePolicy::CareGraph` keeps only pairs that could fire a
  congruence — corresponding arguments of two applications of the same function
  at the same arity — which is cvc5's care graph, restricted to pairs the
  existing rule already proposes.
- `UfliaInterfacePolicy::CareGraphTruncate` additionally keeps a deterministic
  prefix of the ceiling instead of declining.

**Dropping a proposed pair is sound in both directions**, and this is what makes
the trade available at all:

- `sat` cannot become wrong: a leaf model is accepted only after it replays
  against the original literals (`replays_literals` / `replays_assertions`), so
  a model assembled under a coarser arrangement either replays or is declined.
- `unsat` cannot become wrong: each dropped pair removes the forced
  `s = t` / `s < t` / `s > t` from the LIA side and the matching arrangement
  fact from the EUF side, so every explored branch is a **relaxation** of the
  branches it stands for; if all coarse branches are infeasible, so is every
  fine branch inside them.

What it costs is **completeness**, and that cost is stated rather than hidden:
an arrangement that would have been separated is not, and the search reports
`Unknown`. Against a ceiling that returns `Unknown` for the whole query at 65
pairs, more `Unknown` is not the comparison; the comparison is a route that runs
against one that does not.

**3. Z3's model-randomisation filter is recorded as unavailable here, with the
architectural reason, rather than left as an unexplained omission.**

Z3 randomises each coinciding shared variable inside its slack before proposing
an interface equality, so only forced coincidences survive. We cannot: we
materialise the `eq`/`lt`/`gt` interface atoms up front, at combined-state
construction, before any literal is asserted and therefore before any model
exists to randomise. Z3 filters at final check, where it has one. Adopting that
filter means moving interface atoms to **dynamic registration at final check**,
which is a separate slice — and naming it here stops the next lane pricing a
re-architecture as a filter.

**4. A give-up must name the guard that produced it, including which of several
it was.**

`CombinedIncrementalLia`'s construction failure is one variant per cause with a
`detail()` that names the ceiling and the size that crossed it; a deadline is
reported as `UnknownKind::Timeout` rather than as an incompleteness; the Boolean
CDCL(T) leaf arm forwards the inner `UnknownReason.detail` instead of relabelling
every cause as a replay failure. A bench trace that cannot distinguish a
capacity bound from a modelling gap sends the next lane to the wrong subsystem,
which is what happened here and what the previous lane's own diary warned about.

**5. Every admission ceiling on this route carries a counter, and the counters'
entry site is the ROUTE, not the work.**

`UfliaInterfaceCounters::entries` increments at `check_qf_uflia_online`, not at
the interface-pair proposal, because on 40 of the 44 files the instrument exists
to explain, the proposal never happens. An instrument whose entry site is inside
the code that did not run reports nothing on exactly the population that
motivated it. Admission sites publish to the live board on every call so the
reading survives a watchdog kill; the DFS publishes on a cadence.

## Consequences

- The `QF_UFLIA` losing population stops being a story about the lazy CEGAR's
  budget and becomes one about two capacity bounds, which is a different and
  much cheaper class of work.
- Any future lane raising an admission bound in this tree owes the two measured
  quantities in rule 1, in the registry entry, with a `Basis` the gate checks.
- `care-truncate` makes the online combination **incomplete in a new way**. The
  counters (`care_filtered`, `truncated`, `pair_cap_declines`) are what keep
  that visible rather than silent, and they are the reason the arm is
  measurable at all.
- The `QF_UFLRA` copies of the same two constants are deliberately untouched:
  this lane did not measure that division, and re-linking them would claim it
  had.

## Open

- The dispatch ORDER is now the obvious next question and this ADR does not
  settle it. The online combination decides most of the files it wins in
  0.4–2 s, and it runs *after* the lazy CEGAR has spent 18 s of a 24 s budget.
  Z3 and cvc5 run the combination first. Re-deriving
  `UF_ARITH_LADDER_RESERVE_SHARE`, or reordering, needs its own measurement
  against the files the CEGAR decides — the previous lane measured four of those
  needing 12.7–23.7 s.
- The leaf failures (`combined model build failed`, `interface distinct branch
  inconclusive`) are a real capability gap in the LIA sub-solve at a consistent
  leaf, and are untouched here.
