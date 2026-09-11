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

**Reference side.** `z3 -st -T:30` over all 120, once per file. Three `QF_IDL`
files did not measure: their names contain `=`, which z3 reads as a parameter
and refuses. They are excluded from the z3 columns and marked; they are *not*
excluded from our own sweeps.

### 4.1 Per division: what the losses actually are

Our side is `route_solo --route <route> --timeout-ms 20000 --stats`, one process
at a time. `route_solo` is not the front door (it decides the flat view with no
preprocessing, and disagrees with the shipped front door on 134 of 397
benchmarks), so every decline below is a lower bound on the route, never a
statement about the dispatcher.

| division | route | what the losses are | conflict ratio vs z3 |
|---|---|---|---|
| QF_LRA | `lra-online-cdclt` | **not a conflict-count loss.** 49 of 49 declined or timed out; **21** answer `online CDCL(T) LRA model did not replay (arithmetic outside the incremental engine)`, **20** hit the atom-count admission screen (`… exceeds the 1024 a 640 MiB budget admits`), **7** decline at **0 ms** with `boolean skeleton outside the online CDCL(T) LRA encoder`, and **1** times out. Seventeen of the 21 replay declines land in under 110 ms. | n/a — the search barely runs |
| QF_LIA | `lia-online-cdclt` | **not a conflict-count loss.** Same two shapes. On `v30_problem_2__023.smt2.slack.smt2` the whole 20 s went into **one** `theory_assert` (`decisions=0`, `theory_conflicts=0`, `t_assert_ms=20174`) — the integer feasibility solve, not the search. | n/a |
| QF_UFLIA | `uflia-online` | **the route is fine and the ratio is close.** `mathsat/EufLaArithmetic/medium9.smt2`: we return **unsat in 18 ms** with 215 theory conflicts against z3's 122 (**1.8x**); `medium16.smt2` unsat in 82 ms, 482 against 321 (**1.5x**). These are on the loss list, so the loss is upstream of the route. The other shape is `combined CDCL(T) leaf did not rebuild a replaying model: interface distinct branch inconclusive` — model reconstruction, not propagation. | **1.5x – 1.8x** |
| QF_IDL | `dl-online` | **this is the one.** See §4.2. | **2.3x – 39.7x** |
| QF_SLIA | — | **did not run.** The string route (`check_qf_s_online_cdclt`) has no entry in `route_solo`'s table, so there is no per-route measurement here. z3 needs 1–211 conflicts on six of the seven and times out on the seventh. | did not run |

So four of the five divisions answer Phase C's third question with *no*: their
parity losses are encoder-admission, model-replay and theory-combination gaps,
and the conflict counts are either close to the reference or never reached.
**QF_IDL answers yes.**

### 4.2 QF_IDL: the theory is silent on nine of nineteen, and it is a cap

`dl_online::propagate`/`propagate_into` both open with

```rust
if self.symbols.len() > MAX_PROPAGATION_VERTICES || past_deadline(self.deadline) {
    return;                       // MAX_PROPAGATION_VERTICES = 256
}
```

**Nine of the nineteen QF_IDL parity losses declare more than 256 symbols**, and
on exactly those nine difference-logic propagation never runs at all.

The declared-symbol count is a *proxy* — the cap reads `scan_dl`'s vertex count,
which is derived from the query's numeric leaves, not from `declare-fun` lines.
It agrees with the cap on all nineteen files here, but the claim does not rest on
it. What does: `theory_propagations` is exactly `0` on all nine and nonzero on
all ten others, and lifting the cap (§4.3) takes those same nine from `0` to
68 k–469 k propagations. That is the cap firing, established by intervention
rather than by correlation.

(The other ten move too, by up to 19% — `j8_per20_0` 289,982 -> 344,994,
`super_queen29-1` 1,178,013 -> 999,718. That is not noise to wave at: the best
variant also changes the scan order below the cap, and these runs are all
budget-limited on a shared box, so their counts measure how much fitted in 20 s.
Neither effect can produce a 0, which is why the nine are the finding and the ten
are the control.)

| file | symbols | decisions | theory conflicts | theory propagations | z3 conflicts |
|---|---:|---:|---:|---:|---:|
| `graph-colouring-nodes=130-…` | 8,695 | 195,807 | 545 | **0** | not measured |
| `15.3.schur.lp` | 15,290 | 664,821 | 1,314 | **0** | 126,761 |
| `solitaire-center-time=26` | 21,419 | 5,433,202 | 17,768 | **0** | not measured |
| `solitaire-edge-time=29` | 23,194 | 6,277,598 | 20,190 | **0** | not measured |
| `wire.10.x.10.b.5.a.20` | 24,978 | 5,453,367 | 7,085 | **0** | 20,291 |
| `qlock-4-10-21` | 1,202 | **2,550,272** | **10,202** | **0** | **257** |
| `qlock-4-10-27` | 1,532 | 5,089,704 | 21,103 | **0** | 1,827 |
| `qlock-4-10-33` | 1,862 | 5,489,293 | 20,862 | **0** | 1,403 |
| `qlock-4-10-39` | 2,192 | 6,948,844 | 20,285 | **0** | 6,654 |

`qlock-4-10-21` is the sharpest and is the EUF shape exactly: **39.7x** the
reference's conflicts, 2.55 M decisions, and a theory that says nothing.

**The stated reason for the cap does not apply to `propagate_into`.** Its doc
said "the per-probe search would dominate the search loop", and the cost it
names is real but belongs to the **other** scan: `would_conflict` runs behind
`&self`, cannot borrow the theory's `Scratch` mutably, and so calls
`Scratch::new(|V|)` — three `O(|V|)` vectors — once per probe. `propagate_into`
probes through `cycle_for`, which reuses the theory's one persistent `Scratch`
and pays none of that. On the reading alone, lifting the cap there is free.

### 4.3 It is not free, and the A/B is why the cap stays

Lifting it does exactly what the diagnosis predicts to the conflict counts, and
then loses anyway. Three variants were built and measured, in this order:

1. **Cap removed outright.** Conflicts fell 2.4x–11.9x on all nine; propagations
   went from 0 to 68 k–469 k. `theory_propagate` became **42.1 s of a 43.1 s
   wall** on `qlock-4-10-21`.
2. **Plus a work budget** — a shared allowance of edge relaxations per call,
   charged inside the Dijkstra. At 32,768 `theory_propagate` was 16.7 s of 20.0 s;
   at **128** it was still 16.4 s. The budget never bound: the cost is not the
   reduced-cost search, it is the scan's fixed per-call overhead on a driver that
   propagates to a fixpoint after every assignment.
3. **Probe count scaled by graph size, plus a resuming scan cursor** — pay for
   *less* propagation rather than none, and stop re-walking the assigned prefix
   from index 0 on every call. This was the best variant and is the one A/B'd.

A/B, same host, one process at a time, **120 s** budget so the marginal verdicts
are not budget artifacts, nine over-cap files:

| file | capped (shipping) | lifted (best variant) | conflicts |
|---|---|---|---|
| `graph-colouring-nodes=130-…` | unknown | unknown | 789 → 324 |
| `15.3.schur.lp` | **sat 6.6 s** | **unknown at 120 s** | 1,314 → 707 |
| `solitaire-center-time=26` | sat 13.4 s | sat 14.1 s | 17,768 → 5,801 |
| `solitaire-edge-time=29` | **sat 47.4 s** | **unknown at 120 s** | 29,431 → 19,091 |
| `wire.10.x.10.b.5.a.20` | unsat 16.6 s | unsat 53.4 s | 7,128 → 4,249 |
| `qlock-4-10-21` | sat 5.9 s | sat 13.7 s | 10,202 → 1,312 |
| `qlock-4-10-27` | sat 17.5 s | sat 28.6 s | 21,615 → 3,099 |
| `qlock-4-10-33` | sat 27.3 s | sat 22.6 s | 25,294 → 2,650 |
| `qlock-4-10-39` | sat 44.0 s | sat 52.3 s | 32,027 → 3,961 |
| **decided** | **8 of 9** | **6 of 9** | — |

Conflicts fall 1.5x–8.1x on every one of the nine. We decide **two fewer** and
run 1.5x–3.2x slower on five of the six we still decide. **So the change is not
shipped**, and the cap keeps its place with the measurement attached to it.

Eight of the nine are satisfiable, which is the explanation: a `sat` is reached
by finding a model, and pruning a search that is going to succeed anyway is a
cost with no return. On EUF (`e4e6378b8`) conflicts and wall clock fell together
because the file was `unsat` and the propagation was an e-graph lookup; here they
trade.

### 4.4 What this changes about the instrument

Phase C calls the conflict-count ratio against `z3 -st` "the instrument", and it
earned that on EUF. This division sharpens the claim:

> **The conflict ratio is the instrument that finds a silent theory. It is not
> on its own the instrument that says making it speak will pay.**

It separated "our search is weak" from "our theory is silent" here exactly as
advertised — `theory_propagations = 0` beside 2.55 M decisions is not a
heuristics problem and no restart policy reaches it. What it did not predict is
the sign of the wall-clock change, and on a satisfiable family the sign was
negative. A conflict-count win is a **hypothesis about wall clock**, and an A/B
at a budget where the verdicts are robust is what decides it. The 20 s sweep
would have reported this change as costing one file; the 120 s A/B says two, and
the 120 s number is the one to quote because at 20 s five of the nine baseline
verdicts had not landed yet.

## 5. Phase C exit, per theory

Phase C's exit is "per theory, either both-polarity propagation with a measured
conflict-count ratio, or a recorded reason it is not applicable."

| theory | both polarities | measured ratio | status |
|---|---|---|---|
| `lra_online` | yes | not applicable — the route declines or fails model replay before the search does work (§4.1) | **recorded reason** |
| `lia_online` | yes | not applicable — same, plus a single 20 s `theory_assert` (§4.1) | **recorded reason** |
| `dl_online` | yes | **2.3x – 39.7x**, cause identified, fix measured and rejected (§4.2, §4.3) | **measured** |
| `string_theory` | yes | **did not run** — no `route_solo` entry for the string route | **open** |
| `ufbv_online` | yes | not measured on QF_UFBV; its EUF half is the `e4e6378b8` route | **open** |
| `combined_theory` | yes (inherited) | not measured on QF_UFLRA | **open** |
| `combined_theory_lia` | yes (inherited) | **1.5x – 1.8x** on QF_UFLIA `mathsat/EufLaArithmetic` (§4.1) | **measured, close to z3** |

Three cells are open and are named as open rather than inferred. The two that
would close cheapest are `string_theory` (add the string route to `route_solo`'s
table — it is a one-entry change now that `--stats` exists) and
`combined_theory` on QF_UFLRA.

## 6. What the next lane should not re-derive

- **`capabilities.rs:489`/`:613` are still misleading and still not a defect.**
  Re-checked from the code this session, not inherited from the plan: `lra_online`
  skips equality atoms (principled), `lia_online` skips nothing. Neither is EUF's
  gap.
- **Lifting `MAX_PROPAGATION_VERTICES` off `propagate_into` is measured and
  rejected** (§4.3). The A/B is pinned in the constant's own doc comment and
  guarded by `both_propagation_scans_stop_above_the_vertex_cap`, which is the
  single test that dies if the cap is removed from that scan (verified by
  mutation: 1695 passed, 1 failed, and it was that one).
- **QF_LRA and QF_LIA parity losses are not theory-propagation work.** They are
  encoder admission and model replay. A lane aimed at "LRA conflicts" will find
  the search never ran.
