# Theory-interface completeness across the seven online theories (2026-09-10)

**Lane E6, Phase C of
[the CDCL consolidation plan](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md).**

Phase C asks three questions of every online theory with a `propagate`
implementation, and the plan is explicit that the answers must come from the
code, not from a capability string:

1. Does `propagate` emit **both polarities**?
2. Does it implement ADR-1701's `final_check`, or default it away?
3. Is there a benchmark family where our conflict count is far above the
   reference's?

The template is `e4e6378b8`: `EufTheory::propagate` emitted entailed-`true`
equalities and nothing `false`, and implementing the `false` direction took one
QF_UF file from 94,100 theory conflicts to 623 against z3's 559.

## Headline

**All seven already emit both polarities.** Three of them do so *because of*
`e4e6378b8` and not by their own code: `combined_theory`, `combined_theory_lia`
and `ufbv_online` delegate to `EufTheory::propagate`, so the EUF fix reached
them the moment it landed. Two of those three still carry a doc comment saying
the opposite — see [§3](#3-two-live-and-wrong-doc-comments).

`final_check` is a different story: **one of the seven implements it**
(`lra_online`), and six keep the trait default.

## 1. The audit table

Read as: *emits `value: false`* is the EUF question — can this `propagate` ever
push a literal at negative polarity — with the line that does it. *Restriction*
is what the polarity coverage is **not**, stated as the code states it.

| theory | `propagate` at | emits `value: true` | emits `value: false` | restriction (from the code) | `final_check` |
|---|---|---|---|---|---|
| `lra_online::LraTheory` | `lra_online.rs:1098` | `:1118` | **`:1126`** | `AtomKind::Equality`/`Unsupported` `continue` at `:1112` — an equality's negation is a disjunction the conjunctive probe cannot represent | **implemented**, `:1267` |
| `lra_online::LraTheory` (deferred mode) | `propagate_bounds`, `lra_online.rs:816` | `:839` loop | `:839` loop | the pair `[(when_true, true), (when_false, false)]` is one loop, so both polarities by construction; `AtomKind::Order` only | as above |
| `lia_online::LiaTheory` | `lia_online.rs:1443` | `:1481` (Order), `:1499` (Equality) | **`:1490` (Order), `:1510` (Equality)** | none by polarity — this is the *most* complete of the seven; equality is probed at both signs where LRA skips it | default (`FinalCheckOutcome::Sat`) |
| `dl_online::DlTheory` | `dl_online.rs:1719` | `for value in [true, false]`, `:1737` | same loop | `MAX_PROPAGATION_VERTICES` / `MAX_PROPAGATION_PROBES` caps and the deadline; a large graph propagates nothing | default |
| `string_theory::StringTheory` | `string_theory.rs:788` → `variable_equality_propagations`, `:651` | `:690` (class roots equal) | **`:710` (an asserted disequality separates the roots)** | whole-atom `Seq` equality over *variables* only; sub-component `Fact`s do not map to tracked atoms (module doc, `:58-63`) | default |
| `ufbv_online::CombinedUfbvTheory` | `ufbv_online.rs:905` | `euf.propagate()` + BV probe | `euf.propagate()` + BV probe | BV half is **model-guided** (`refresh_propagation`, `:685`): it reads the atom's value under `last_model`, probes the opposite, and emits the model's polarity — so either sign, one atom per refresh, capped by `MAX_BV_PROPAGATION_PROBES` | default |
| `combined_theory::CombinedIncremental` | `combined_theory.rs:760` | `euf.propagate()` + `lra.propagate()` | same, inherited | the incremental surface does **not** run `interface_propagations` (`:315`), which the per-call `CombinedTheory::propagate` (`:251`) does | default |
| `combined_theory_lia::CombinedIncrementalLia` | `combined_theory_lia.rs:891` | `euf.propagate()` + `lia.propagate()` | same, inherited | same interface gap as the LRA twin | default |

For reference, the template it is measured against:

| theory | `propagate` at | emits `value: true` | emits `value: false` | restriction | `final_check` |
|---|---|---|---|---|---|
| `euf_egraph::EufTheory` | `euf_egraph.rs:596` | `:628` | `:651` (since `e4e6378b8`) | — | default |

`lra_theory::LraTheory` (`lra_theory.rs:191-211`) is not an eighth theory: it is
a thin forwarding wrapper whose `propagate`, `final_check`, `propagate_into` and
`engine_counters` all delegate to the `lra_online::LraTheory` it holds as
`inner`. It is the adapter that puts the LRA theory on the native core.

### Which driver each theory actually runs on

Needed to read the counters: only a CDCL(T) driver publishes `TheoryLayerStats`.

| theory | shipping driver | `route_solo` name |
|---|---|---|
| `lra_online::LraTheory` | `native_cdclt::solve_native` via `lra_theory.rs:363`; also `lra_online::Dpll` | `lra-online-cdclt`, `lra-dpll` |
| `lia_online::LiaTheory` | `native_cdclt::solve_native` via `lia_theory.rs:219`; also `lia_online::Dpll` (`:2154`, `:2306`) | `lia-online-cdclt`, `lia-dpll` |
| `dl_online::DlTheory` | `native_cdclt::solve_native`, `dl_online.rs:2279` | `dl-online` |
| `string_theory::StringTheory` | `native_cdclt::solve_native`, `string_theory.rs:1069` | (not in `route_solo`'s table) |
| `ufbv_online::CombinedUfbvTheory` | `CdclT::new`, `ufbv_online.rs:1386` | `ufbv-online-cdclt` |
| `combined_theory::CombinedIncremental` | `solve_native_counted`, `uflra_online.rs:1431` | `uflra-online` |
| `combined_theory_lia::CombinedIncrementalLia` | `solve_native_counted`, `uflia_online.rs:1841` | `uflia-online` |

The native core does call `final_check` (`native_cdclt.rs:403-408`), so the six
defaults are genuine defaults and not a driver that skips the hook.

## 2. `final_check`: one of seven

`lra_online.rs:1267` is the only override among the seven, and it is conditional
on `self.deferred_final_check` — the instance opted into the ADR-1701 split. The
other six inherit `FinalCheckOutcome::Sat` from `euf_egraph.rs:103`.

**This is not by itself a defect.** ADR-1701's own wording is that "a theory
whose `assert` already decides everything needs no second opinion and keeps the
default". Six of the seven do decide at `assert`:

- `lia_online` decides feasibility in `assert` unless
  `defer_feasibility_until_propagate` is set, in which case it routes the
  conflict through `propagate` (`lia_online.rs:1447-1451`) rather than through
  `final_check` — a *different* deferral mechanism than ADR-1701's, reaching the
  same place.
- `dl_online`, `string_theory`, `combined_theory`, `combined_theory_lia` and
  `ufbv_online` all refute at `assert` time.

So the honest reading of column 6 is: **`final_check` is under-used, not
wrongly-defaulted**, and the case for moving any of the six onto it has to be
made on a measured conflict count, not on the shape of the trait. That is
[§4](#4-the-conflict-count-measurement).

## 3. Two live-and-wrong doc comments

`combined_theory.rs:756` and `combined_theory_lia.rs:886` both say:

> The `Refuted` direction (an interface eq forced *false*) is not emitted:
> `EufTheory` defers disequality-entailment, and **omitting** a propagation is
> always sound

The clause after the colon has been false since `e4e6378b8`. `EufTheory` no
longer defers disequality-entailment, and since both `propagate` bodies are
`self.euf.propagate()` plus a sub-theory, both of these surfaces started
emitting the refuted direction for every interface equality the e-graph
separates — without either file changing.

This is the same class of defect Phase A of the plan is clearing out for BatSat:
a live comment making a false claim about a neighbouring module's behaviour.
It is corrected in this lane's commit.

What remains true in those comments, and is worth keeping, is the *interface*
gap: the incremental surface never calls `interface_propagations`, so an
interface equality that the EUF e-graph does not itself register as an atom is
still only reachable through the structural clauses and the search.

## 4. The conflict-count measurement

**Instrument.** `route_solo --stats` (added in this lane) prints the CDCL(T)
driver's own `TheoryLayerStats` for whichever route was run, so the
conflict-count ratio against `z3 -st`'s `:conflicts` is one command per side on
any division — not just QF_UF, which is where `qfuf_rung_timing` had it. The
counters are thread-local to the worker thread, so they are read inside the
worker closure; a read after the join would report zero for every route.

**Population.** The parity-loss lists under
`bench-results/parity-losses-20260908/`: `QF_LRA.txt` (49), `QF_LIA.txt` (22),
`QF_IDL.txt` (19), `QF_UFLIA.txt` (23), `QF_SLIA.txt` (7) — 120 files. The
sharpest file per division is chosen the way `iso_icl_repgen004` was chosen for
QF_UF: smallest z3 time against our 24 s over-budget.

*(Measurement in progress at the time of this commit; results follow in the same
document.)*
