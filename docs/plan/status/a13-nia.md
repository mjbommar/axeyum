# Lane a13-nia — ADR-2136's lemma lever split three ways: slice, class, iteration

<!-- plan-section: lane-status -->

**Lane a13-nia (`DONE`, a13-nia, 2026-09-17).** The stock-take's queue item 3
asked whether [ADR-2136](../../research/09-decisions/adr-2136-order-and-monotonicity-lemmas-for-nia.md)'s
three `unsat → unknown` losses were the SLICE its lever widened (a later
ladder route starved) or the LEMMAS it emitted. Traced per route in both arms
([ADR-2148](../../research/09-decisions/adr-2148-nia-lemmas-versus-slice-versus-iteration.md),
artifacts in
[`bench-results/nia-refine-share-20260917/`](../../../bench-results/nia-refine-share-20260917/README.md)):
all three losing files carry small-domain splits, so the shipped arm ALREADY
had the wide slice, and it is decided by the refinement loop itself in 2–6 s;
the armed loop adds 20–39 order/monotone lemmas at round 0 and does not refute
the same system in the same slice. Not a starved route — the lazy LIA driver
on a reshaped relaxation.

**Three levers instead of one.** `AXEYUM_NIA_REFINE_SHARE` decides the slice
on a product-only query; `AXEYUM_NIA_ORDER_LEMMAS` is a mode — `1` both
classes (ADR-2136), `2`/`3` one class, `4` iterate with tangent planes only,
the control ADR-2136 never ran. On its 13 moved files: the share is the
mechanism of no loss and two gains; the classes are the mechanism of every
loss in every combination that emits them and are worth `305` and `39`; and
**eight of the ten "lemma" gains are iteration gains** — mode 4 decides them
with no class lemma and loses nothing (on an envelope file it is the shipped
code).

**Shipped: mode 4 with share 3** (`NIA_ORDER_LEMMAS_ARMED = 4`,
`NIA_REFINE_SHARE = 3`, ADR-2148 `accepted`). Two four-population A/Bs against
the old default (800 files each, interleaved, movers re-checked 3× per arm):
0 disagreements, 0 `:status` contradictions, **0 stable losses**, 6 and 8
stable gains, `QF_NRA` control 0/0. The seeded, disjoint `UFNIA` held-out
draw: 51 → 58, 6 stable gains, 0 losses. `UFNIA` 54 → 61 pinned (+13 %);
`QF_NIA` +1 pinned, +0 on its held-out draw — stated, not absorbed. The two
lemma classes stay OFF behind the lever: a 2-for-2 trade against the
`splits > 0` Farkas family.

**Handed forward.** (a) The classes' cost is the lazy LIA driver's search on
20–39 guarded implications on a relaxation it refutes alone in 1–4 rounds; a
class emitted only for pairs with no exact split, or capped on the round's
tangent count, are the untested candidates. (b) The ceiling on `QF_NIA` is
still the relaxation's round-0 `unknown` on 67 of 116 undecided rows
(ADR-2136 §C1). (c) A `cargo build` on the measurement host contaminated
three recheck rows; build elsewhere and copy.

<!-- plan-section: landed-changes -->

| 2026-09-17 | `1505f035c` | `feat(nia)`: the slice share is its own lever (`AXEYUM_NIA_REFINE_SHARE`); `refinement_setup` computes iteration and slice independently; five unit tests, mutation suite `nia-refine-share`. |
| 2026-09-17 | `fc6c70f04` | `measure(nia)`: the sizing — head recheck of the 13 files, per-route traces of the three losses, the 2×2. |
| 2026-09-17 | `770d23545` | `feat(nia)`: `AXEYUM_NIA_ORDER_LEMMAS` selects the class (2 order, 3 monotonicity, 4 iterate with tangents only). |
