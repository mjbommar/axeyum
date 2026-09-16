# Lane: lra-propagation — implied-bound propagation into the SAT core (ADR-2122)

<!-- plan-section: lane-status -->

**Lane LRA-PROPAGATION (`WIP`, lra-propagation, 2026-09-15).** [ADR-2111] named
theory propagation as the largest lever it did not pull: over the 23 of 93
undecided `QF_LRA` rows that reach the online CDCL(T) engine, a median **19
theory propagations against 836,531 decisions**. This lane built it, sized it
before building it, and scored it. ADR-2122 is **`proposed`**; the lever ships
`off`.

**Sizing first, and it is the headline.** `AXEYUM_LRA_BOUND_PROPAGATION=probe`
builds the identical column-bound table and offers nothing, so it measures the
search that actually ran. Over the same 23 rows (re-derived from ADR-2111's
committed census by the `decisions` column being present — the other 70 never
reach the engine and contribute nothing, not a zero): **405,738 of 1,654,631
decisions on tracked atoms, 24.5 %, were on an atom the bounds already
entailed.** Of ALL decisions it is 7.0 %; both denominators are printed because
a `QF_LRA` skeleton has Tseitin variables the theory cannot reach. Median
per-row share **19.0 %**, min 0.3 %, max 70.5 % — **the spread is the finding**.
`theory_propagations` reads a median 18.5 today, re-deriving ADR-2111's 19 on a
different run.

**Two rows the lever provably cannot help**: `miplib/pp08a-1000` and
`pp08a-7349` take 291,314 and 169,645 decisions with **`tracked = 0`** — not one
decision on an atom the theory tracks. `pp08a-7349` is ADR-2111's own median row.

**What was built.** A COLUMN-bound table, not a scan of the tableau's rows, and
that is forced rather than chosen: z3's `is_unit_var` makes `x ≤ 3` a column
bound with **no row at all** (`theory_lra.cpp:807-809,856-857`), while ours
makes a slack row per template, so **no problem variable ever carries a bound**
and a direct port of `propagate_bounds_for_touched_rows` would have been INERT.
Seeds from unit constraints, rounds over the asserted rows (one candidate per row
entry per direction — z3's actual shape), emission when an atom's expression is
confined to one side of zero. Basis-independent, so the offered sequence does not
depend on the last check's pivots.

**Three of ADR-2111's citations are corrected**, one of which would have cost a
successor: **z3 does NOT yield at most two implied bounds per row.** `analyze()`
returns at most 2, but that counts DIRECTIONS; `limit_all_monoids_from_below`
(`bound_analyzer_on_row.h:196-220`) calls `limit_j` once per row ENTRY, so a row
of length *n* emits up to 2*n*. Also: `try_add_bound` does not exist
(`add_bound`, `lp_bound_propagator.h:150-190`), and `:54-80` truncates
`analyze()` mid-body.

**Soundness by a checker that shares no arithmetic with the producer.** Every
offered literal's reasons plus its own NEGATION go to the simplex, which must
refute them. Over 1,000 LCG systems: **904 verified, 0 inconclusive, 0 refuted**,
with an asserted floor of 200 so a propagator that goes quiet dies rather than
passing by checking nothing. The soundness-negative fixture is a PAIR with the
satisfiable arm first, and the positive control carries its own negative control
(the form-level scan offers nothing on the same state).

**The mutation run found a guard that was decoration and it was not engineered
away.** The self-explanation `continue` was removable with all 38 tests green —
unreachable, because every reason atom is asserted and the target is not. It is
now a `debug_assert!` stating that invariant, and the mutation suite watches a
guard that is real instead.

[ADR-2111]: ../../research/09-decisions/adr-2111-qf-lra-what-the-same-simplex-does-differently.md

<!-- plan-section: landed-changes -->

| 2026-09-15 | `03dc0e33c` | lra-propagation: implied-bound propagation into the SAT core -- `ImpliedBounds` column table, the `note_decision` driver hook, six additive trail counters, five registered caps, the simplex-backed explanation checker, lever `off` |
| 2026-09-15 | `ef4492312` | lra-propagation: the sizing sweep -- the ceiling is **24.5 %** of tracked decisions, with the per-row spread and the two rows the lever provably cannot reach |
| 2026-09-15 | `cc949ea74` | lra-propagation: the scratch reset was half the propagator's cost, and one guard the mutation run found was decoration |
| 2026-09-15 | `4f8ebf8cd` | lra-propagation: two A/B runner defects that let an EMPTY run print `AB-DONE`, and the workspace gate script |
