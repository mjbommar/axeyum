# The arithmetic gap: which route loses the file, and to which missing capability

Survey lane `research-arith-gap`, 2026-09-08. Read-only: no build, no test, no
production change. The question this lane was pointed at is **empirical and
route-level** — of the 214 arithmetic files we lose, *which pass consumes the
budget and what capability is it missing* — not the general theory-solver
literature, which is the companion lane's file
[`theory-solvers.md`](theory-solvers.md) in this same directory. Where the two
overlap I cite that file rather than re-deriving it.

**Claim tags.** `[C]` read from source, cited `path:line`. `[P]` a paper. `[D]`
a solver's own system description. `[I]` my inference from `[C]`/`[P]` —
argued, never measured here. **Did not verify** where I did not check.

**Standing caution.** This lane could not run the corpus: the parity benchmark
files live on s5–s7, not in this checkout, and the brief forbids cargo. So
**every quantity below is either read from source, quoted from a committed
measurement artifact, or explicitly marked as an unmade measurement.** Nothing
here is a benchmark result produced by this lane.

---

## 0. The one-paragraph answer

Across all six arithmetic divisions, the recurring shape is not *we lack the
algorithm*. We have the Dutertre–de Moura simplex, δ-rationals, Farkas
certificates, Cotton–Maler incremental negative-cycle difference logic,
model-based theory combination for EUF+LIA, Gomory cuts, branch-and-bound, and
NIA incremental linearization with tangent planes — every one of them read from
source below, so **anyone briefed to "build X" for these divisions should check
§4 first**. The shape is instead **a route we own does not run, or runs on a
fraction of the budget, or re-solves from scratch what it should update**. The
single largest instance is QF_UFLIA: the route whose architecture matches what
Z3 and cvc5 actually do — our online model-based EUF+LIA combination — is
**structurally unreachable** on the population we lose, because a lazy
Ackermannization CEGAR route returns before it in dispatch. That is finding #1
and it is a route-ordering fact readable in twenty lines of `auto.rs`.

---

## 1. Answer to the most important question (Q5): one lever, and which side of the CDCL line

**The arithmetic bottleneck is ABOVE the CDCL(T) line, and it was below it
until three weeks ago.** That transition is measured, not argued:

| division | where the budget went | source |
|---|---|---|
| QF_IDL | `CdclT::unit_propagate` clause rescan, **19.4 s of 24 s, theory at 0 ms** — *below* the line | [arith timeout profiles](../../11-design-review/2026-09-05-arith-timeout-profiles.md) `[C]` |
| QF_LRA | `LraTheory::final_check → feasibility → simplex`, **84% of wall** — *above* the line | [same](../../11-design-review/2026-09-05-arith-timeout-profiles.md), [S4](../../11-design-review/2026-09-05-s4-simplex-warm-start-measured.md) `[C]` |
| QF_UFLIA | the lazy UF+arith CEGAR loop, 31 timeouts + 21 admission declines of 58 — *above*, and not even in a theory solver | [parity loss census](../../11-design-review/2026-09-05-parity-loss-census.md) `[C]` |
| QF_LIA | `lia-dpll`'s pre-SAT admission rectangle, 15 of 27 — *above*, in dispatch | census `[C]` |
| QF_NIA | `int-blast-ladder` timeouts + its CNF cap, 47 of 61 — *above*, in dispatch | census `[C]` |

S1 and S1b harvested the below-the-line half: QF_IDL 70 → 105 and QF_RDL
107 → 142 on the board, with the QF_LRA population barely moving `[C]`
([parity plan progress log](../../../plan/smt-parity-plan-2026-09-05.md)). What
is left in arithmetic is above the line. S7/S8 (engine unification and native
core throughput) will still help every division, but on the current board they
are not where the 214 files are.

**The single shared piece that most determines all six is the
atom-to-tableau encoding in the linear-arithmetic layer**, and it is upstream
of the companion lane's #1 (sparse rows) and the direct cause of why its #3
(row-based implied-bound propagation) is currently impossible:

> `build_simplex_engine` opens **one tableau row per atom template**, with no
> interning by linear form, and every bound lives on that row's slack variable —
> so every *problem* variable is unbounded and no tableau row can ever imply a
> finite bound on anything (`crates/axeyum-solver/src/lra_online.rs:1458-1535`)
> `[C]`. The integer engine does the same
> (`crates/axeyum-solver/src/lia_online.rs`, `build_int_simplex_engine` and
> `open_row`) `[C]`.

Z3 does the opposite, and it is one function:
`theory_lra::internalize_linearized_def`
(`references/z3/src/smt/theory_lra.cpp:853-878`) `[C]`. A *single-variable*
term short-circuits (`if (is_unit_var(st) && v == st.vars()[0]) return ...`,
`:857-858`) — no row, the bound goes on the variable's own column. A compound
term gets **one** `lp::add_term` column (`:870`), and because the term is
hash-consed by the AST manager, every atom over the same linear combination
shares that one column; the atoms become *bounds*, not rows.

The consequences chain, and all of them are already visible in our own
committed measurements:

1. **Row count.** `QF_LRA/2019-ezsmt/blending/1.smt2` runs a **350 × 425**
   tableau — i.e. 350 rows over **75** problem variables
   ([S4 §1](../../11-design-review/2026-09-05-s4-simplex-warm-start-measured.md))
   `[C]`. 350 rows for 75 variables on an LP blending benchmark is what
   one-row-per-atom looks like. `[I]` — I did not count the file's distinct
   linear forms, because the corpus is not in this checkout.
2. **Cost per pivot.** 1.41 ms before S4, 0.27 ms after `[C]`. Both numbers are
   `O(rows × pivot-row-nonzeros)` in a dense `Vec<Vec<Rational>>`
   (`crates/axeyum-solver/src/simplex.rs:295-333`) `[C]`; cutting rows cuts
   this directly, on top of whatever sparsity buys.
3. **Propagation is structurally dead.** The S4 lane wrote this down rather
   than guessing: *"bounds live only on the slack variables, one per atom,
   while every problem variable `xⱼ` is unbounded… no row implies a finite
   bound on anything. The general row scan is left unbuilt and this is the
   reason, not an omission"* `[C]`. Change the encoding and the standard
   theory-propagation lever becomes available; leave it and that lever cannot
   be built at all.
4. **Admission.** `simplex::Incremental::new` declines above
   `MAX_TABLEAU_CELLS = 4_000_000` dense cells
   (`crates/axeyum-solver/src/simplex.rs:75`, `:910-922`) `[C]`, and a decline
   drops `LraTheory` back to **Fourier–Motzkin**
   (`lra_online.rs:945-960`, the `if let Some(cell) = &self.simplex` arm) `[C]`.
   Cells are `rows × (nvars + rows)`, so the row count enters *quadratically*.
   The ADR-1752 memory budget reserves 128 MiB of its 640 MiB for that dense
   tableau at `BYTES_PER_TABLEAU_CELL = 32` (`lra_online.rs`) `[C]`.
5. **Reach.** `LraTheory` serves QF_LRA and the LRA half of QF_UFLRA;
   `LiaTheory` serves QF_LIA and, through `CombinedIncrementalLia`, QF_UFLIA;
   the QF_RDL census attributes 23 of 47 losses to the LRA atom cap `[C]`. Four
   divisions, one encoding. QF_IDL/QF_RDL's *fast* path is the DL graph and is
   untouched by this.

**So the answer to Q5 is: the arithmetic preprocessing/normalization layer —
specifically how an atom becomes a tableau object — not the simplex core and
not the theory-propagation interface.** The propagation interface is already
widened (ADR-1701) and the simplex core is already the right algorithm; both
are being starved by what they are handed. This is above the CDCL(T) line.

---

## 2. Ranked findings

Ranked by (expected files) / (effort). Effort is S ≈ under a day, M ≈ a few
days, L ≈ a slice. Every "expected files" figure is an upper bound drawn from
the committed census populations — **none of them is a measured yield**, and
the first thing each item needs is the measurement named in its last column.

| # | Finding | Kind | Divisions | Upper-bound population | Effort | First measurement |
|---|---|---|---|---:|---|---|
| 1 | The online MBTC combination route is **unreachable** on the losing QF_UFLIA population | **have it, never runs** | QF_UFLIA | 52 of 58 | **S** | Re-run the 58 with the CEGAR block bypassed |
| 2 | `LiaTheory` re-solves integer feasibility **from scratch, via an arena clone and the offline branch-and-bound**, per theory check — and again per literal to minimize the core | have it, too slow | QF_LIA, QF_UFLIA, QF_LIRA | 27 + 58 | M | Count `check_terms` calls and their wall on 5 traced QF_LIA files |
| 3 | One tableau **row per atom**, bounds on slacks only (§1) | have it, wrong shape | QF_LRA, QF_LIA, QF_UFLIA, QF_UFLRA, QF_RDL | 52 + 27 + 58 + 12 | M | Print `assign_forms`'s `forms.len()` beside `rows_sparse.len()` on the 33-file LRA population |
| 4 | The `lia-dpll` pre-SAT admission rectangle and wide-core budget are justified **entirely by BatSat's allocator**, and ADR-1703 retired BatSat | gives up early, on a stale reason | QF_LIA, QF_LRA, QF_RDL | 15 of 27 QF_LIA | **S** | Re-run the four cited control files under `IncrementalSat`'s native core and re-derive the rectangle |
| 5 | NIA incremental linearization runs on a **600 ms slice of a 24 s budget** unless McCormick envelopes fired | gives up early | QF_NIA | 30 timeouts of 61 | **S** | Sweep `NIA_SLICE_MS` over the 61 |
| 6 | Pure Bland's rule as the *only* entering rule; Z3 uses a short-row heuristic with a 1000-repeat Bland fallback | have it, slow rule | same as #3 | — | **S** | The companion lane's #2; ~40 lines |
| 7 | Difference logic declines on `i128` overflow of the denominator LCM and on any coefficient other than ±1 | have it, narrow admission | QF_RDL | ≤ 14 | S | Count `scan_dl` returning `None` on the 14 |
| 8 | **Secant-based linear bounds** for `x^k` / `x^k·y^l` over unit intervals — a new lemma schema in the refinement loop we already own | **lack it**, small | QF_NIA | non-`VeryMax` remainder | **S** | Emit them and score outside the `VeryMax/ITS` family |
| 9 | Integer reasoning ordered as Z3 orders it — GCD, HNF cuts and Diophantine tightening **before** branch-and-bound, all as in-loop lemmas | lack the first two; have the rest, wrongly ordered and offline | QF_LIA, QF_UFLIA | 27 + 58 | L | Follows #2; the companion lane's #9 is the same conclusion |

### 1. QF_UFLIA: the route that matches Z3 and cvc5 cannot run

This is the highest-value item on the board and it is a dispatch-ordering fact.

`dispatch_uf_fast_paths` (`crates/axeyum-solver/src/auto.rs:2803`) does this,
in this order `[C]`:

```
2837:  if features.has_function
2838:      && has_arithmetic_function(arena)
2839:      && let Some(result) =
2840:          crate::euf::try_lazy_arith_for_overbound(arena, assertions, config, "UF+arithmetic")?
2841:  {
2842:      let array_unknown = features.has_array && matches!(result, CheckResult::Unknown(_));
        ...
2853:      if !array_unknown {
2854:          return Ok(Some(result));
2855:      }
2856:  }
```

`try_lazy_arith_for_overbound` returns `Some(...)` **exactly when** the eager
Ackermann bound would have fired — `if refuse_oversized_ackermann(...).is_none()
{ return Ok(None); }` (`crates/axeyum-solver/src/euf.rs:309-311`), and that
bound is `MAX_ACKERMANN_CONGRUENCE_PAIRS = 64` (`euf.rs:64`, `:125`) `[C]`.

So for a **non-array** QF_UFLIA query with more than 64 Ackermann congruence
pairs, the lazy CEGAR result — *including its `Unknown`* — is returned at
`auto.rs:2854`, and everything after it in the function is unreachable:

- `euf-online`, the CDCL(T) e-graph (`auto.rs:2887`);
- `euf-offline` (`auto.rs:~2920`);
- **`dispatch_uf_arith_online` (`auto.rs:2963`)** — our online model-based
  Nelson–Oppen EUF+LIA combination, whose own doc comment at `auto.rs:3227`
  calls it "the **online** EUF + linear-arithmetic combination, tried *before*
  the eager Ackermann route"; on this population it is tried *after* something
  that never falls through;
- the eager `check_with_uf_arithmetic` (`auto.rs:2965`).

The census attributes **52 of 58 QF_UFLIA losses** to that CEGAR loop — 31
search timeouts at `uf-arith-lazy-overbound`, 21 admission declines inside the
same loop `[C]`. Those 52 are exactly the files where `pairs > 64`, hence
exactly the files on which the MBTC route is dead code. `[I]` — the
identification of "census class = CEGAR" with "pairs > 64" follows from the
guard, but I did not run the population to confirm the pair counts.

**Why this matters more than a tuning knob: neither reference solver does what
we do here.** Read from source by this lane's sub-agent:

- Z3 has no `qfuflia` Ackermannization tactic at all; everything under
  `references/z3/src/ackermannization/` is wired only into the **BV** pipeline
  (`qfufbv_tactic.cpp`, `qfaufbv_tactic.cpp`), and `setup_QF_UFLIA`
  (`references/z3/src/smt/smt_setup.cpp:457`) just calls `setup_lra_arith`,
  registering `theory_lra` over native congruence closure `[C]`. Its only
  Ackermann device on this path is **dynamic** Ackermannization
  (`references/z3/src/smt/dyn_ack.cpp:197,227,407-434`), which adds a single
  congruence clause for a pair that has appeared in conflict analysis more than
  `m_dack_threshold = 10` times, with GC — a targeted assist, not a
  whole-formula abstraction `[C]`.
- cvc5's Ackermannization pass is opt-in (`--ackermann`, default false, expert
  category, `references/cvc5/src/options/smt_options.toml:5-9`) and its own doc
  says it exists for **eager bit-blasting**; `set_defaults.cpp:493-506` forces
  it back off whenever UF or arrays are present with model production `[C]`.
  QF_UFLIA runs native congruence closure plus the care graph
  (`combination_care_graph.cpp:33`) and `ArithCongruenceManager`
  (`references/cvc5/src/theory/arith/linear/congruence_manager.cpp:746,808,326`,
  1,175 lines), which pushes bound-forced equalities `x = y` **directly** into
  the shared equality engine when a watched slack is pinned to zero `[C]`.

So the architecture both references ship is: congruence closure inside the
search, plus a *cheap filter* deciding which interface equalities are worth
proposing (Z3: hash-bucket shared arith variables by their current LP model
value, `theory_lra.cpp:1593,1614-1621`; cvc5: an operator-indexed `TNodeTrie`
walk pruned by known disequalities, `theory_uf.cpp:582`,
`node_trie_algorithm.cpp:17`) `[C]`. **We have the first half already**
(`uflia_online.rs`, `combined_theory_lia.rs`, `theory_combination.rs`); the
companion lane's findings #5 and #5b are the second half. Neither is worth
anything while `auto.rs:2854` returns first.

**The cheapest honest experiment.** Do not delete the CEGAR route. Give it a
bounded probe budget the way `dispatch_uf_arith_online` already gives itself one
(`probe_budget`, `auto.rs:3148`, used at `:3269`), let its `Unknown` fall through instead
of returning, and re-run the 58. If the MBTC route declines on all of them at
`MAX_BOOLEAN_ATOMS = 512` / `MAX_OPAQUE_BOOLEAN_ATOMS = 128`
(`uflia_online.rs:97,104`) `[C]`, that is a *different* and equally useful
finding — and it is one measurement away.

### 2. QF_LIA / QF_UFLIA: the integer theory has no incremental check at all

`LiaTheory` is described in its own header as "re-decided-incremental"
(`crates/axeyum-solver/src/lia_online.rs:14-27`) `[C]`, and the path is worse
than that phrase suggests. `feasibility_with_core_minimization`
(`lia_online.rs:889`) does `[C]`:

1. a warm rational filter on the shared `simplex::Incremental` — cheap, and it
   short-circuits on a refutation or an integral point;
2. otherwise **`live_terms` clones the entire `TermArena`**
   (`lia_online.rs:863-877`) and rebuilds one IR term per live literal;
3. then `check_with_lia_simplex_within` — the *offline* decider, i.e. a fresh
   branch-and-bound with a 50,000-node cap (`lra.rs:1198`) plus a bounded round
   of Gomory cuts built on **its own separate `GomoryTableau`**
   (`lra.rs:1425,1731-1810`);
4. and on `unsat`, `minimize_core` re-runs `check_with_lia_simplex` **once per
   literal it tries to drop** (`lia_online.rs:1541-1581`).

Every one of those steps happens inside a `TheorySolver::assert`
(`lia_online.rs:1483-1499`) — i.e. potentially per literal the CDCL(T) search
assigns, throttled only by `DEFER_LIA_FEASIBILITY_ATOMS = 128`
(`lia_online.rs:90`) `[C]`.

The references do none of this. cvc5 keeps the integer machinery *on the same
tableau* the LP runs on and rolls it back with the SAT context
(`CDList`/`CDO` in `partial_model.h:200-222`, `constraint.h:1049-1055`) `[C]`;
Z3 keeps the basis and pops only the trail (`lar_core_solver.h:123-143`) `[C].`

**And Z3's integer reasoning is not an offline procedure at all — it is
theory-propagated literals inside the CDCL(T) final check.** `int_solver::check`
is called from `theory_lra::final_check_status`
(`references/z3/src/smt/theory_lra.cpp:1761`, `:2020-2095`), and its result is
translated straight into search machinery `[C]`:

- `lia_move::cut` → the cut becomes a bound literal, its explanation is
  collected into `m_core`/`m_eqs`, and `assign(lit, m_core, m_eqs, m_params)`
  hands it to the SAT core **as a theory-propagated literal usable in later
  conflict analysis** (`theory_lra.cpp:2056-2080`);
- `lia_move::branch` → a fresh bound atom is created and `FC_CONTINUE`
  returned, with the source comment *"at this point we have a new unassigned
  atom that the SAT core assigns a value to"* (`:2034-2055`) — **branch-and-bound
  is ordinary Boolean case-splitting on learned atoms, not a tree walked
  outside the SAT solver**;
- `lia_move::conflict` → `set_conflict()`, feeding conflict analysis directly.

Three structural consequences for us:

- **Cuts are thrown away.** Ours are generated on a throwaway `GomoryTableau`
  inside an offline call and are never returned to the search as lemmas, so the
  Boolean layer can never reuse one `[C]`. Note the companion lane demotes
  Gomory cuts hard on reference evidence (its finding #11), and Z3's own
  dispatch backs that up — see below. So the fix is *stop paying for them per
  assert and let what you do derive reach the search*, not *add more cuts*.
- **Branching is invisible to the search** for the same reason: our
  branch-and-bound explores its own tree inside `check_with_lia_simplex`, so
  its 50,000-node budget is spent afresh on every theory check and nothing it
  learns survives the call `[C]`.
- **The arena clone is per check.** For a 15 MB Certora QF_UFLIA file, that is
  not a constant factor to shrug at. `[I]` — I did not measure the clone.

**Z3's shipped LIA ladder, for whoever scopes this** (`int_solver.cpp:270-291`,
read directly) `[C]`: GCD test → basic-column patching → cube tests
(`int_cube.cpp`) → **HNF cuts** (`hnf_cutter.cpp`, citing Christ & Hoenicke's
*Cutting the Mix*, `hnf_cutter.h:9-11`) → **Diophantine-equation tightening**
(`dioph_eq.cpp`, 2,765 lines, copyright 2024, following Griggio's *A Practical
Approach to Satisfiability Modulo Linear Integer Arithmetic*, `dioph_eq.h:9-10`)
→ Gomory cuts → **branch-and-bound last**. Every stage is period-throttled and
adaptive; the source comments literally say *"dio was productive: stop running
Gomory"* / *"dio persistently unproductive: start running Gomory"*. Neither the
Omega test, Cooper's method, nor Dillig-style cuts-from-proofs appear anywhere
in that file set — searched under expected names, **not** an exhaustive
repo-wide grep. We run branch-and-bound first with a bounded Gomory round; Z3
runs it last, behind two families we do not have. That ordering, plus the
companion lane's #9 (Diophantine pre-solve, which it independently ranks above
cuts on cvc5 and Yices evidence too), is the same conclusion reached twice from
different sources.

This is the integer analogue of the companion lane's §2.7 duplication finding
and it is why QF_LIA did not respond to the ADR-0538 core-minimisation fix that
moved QF_UFLIA +22: QF_LIA's cost is not wide cores, it is that a *narrow* core
costs `|core|` full branch-and-bound solves to obtain.

### 3. The atom-to-tableau encoding

Stated in full in §1. Two additional notes for whoever picks it up:

- **The interning key already exists.** `assign_forms` (`lra_online.rs:1386`)
  already computes a canonical `FormKey` per constraint template — divide
  through by the leading coefficient — and returns `forms.len()`. It is used
  only to index `bound_lower`/`bound_upper` for propagation. `open_row`
  (`lra_online.rs:1461`) never consults it and pushes a row unconditionally
  `[C]`. Mapping form → row is a small change with the key already in hand.
- **The simplex API is the real work.** `Incremental::assert_bound(i, rel, rhs)`
  takes a **row** index (`simplex.rs:947`) and `Tableau::set_row_bound` writes
  `lower[slack]`/`upper[slack]` (`simplex.rs:393`) `[C]`. Putting a bound on a
  problem-variable column, and telling `farkas` which atom owns a column's
  active bound, is the part that needs care — the certificate contract
  (`rows_to_core`, `live_indices`) is written in row indices today.

Do this **with** the companion lane's #1 (sparse rows + column lists), not
before or after: they touch the same 400 lines of `simplex.rs` and a merge of
two independent rewrites of a tableau is the exact shape CLAUDE.md warns about.

### 4. QF_LIA: an admission rectangle calibrated against a retired solver

`dpll_lia.rs` declines before solving when **both** counts cross
`MAX_PRE_SAT_ARITH_ATOMS = 1_024` and `MAX_PRE_SAT_CNF_VARS = 4_096`
(`crates/axeyum-solver/src/dpll_lia.rs:69-70`), with a "measured-safe
rectangle" exception at 1,280 / 8,192 (`:80-81`), plus a wide-core budget
`MAX_DYNAMIC_LARGE_CORE_LITERALS = 8_192` (`:112`) `[C]`. The census puts **15 of 27**
QF_LIA losses at "`lia-dpll`'s pre-SAT resource boundary" `[C]`.

Every justification written next to those constants names **BatSat**:

- *"made `BatSat` allocate past an 8 GiB process ceiling on its third solve
  with only two learned clauses, before its cooperative deadline poll"*
  (`dpll_lia.rs:63-69`) `[C]`;
- *"24 cores of roughly 430 literals were enough for `BatSat` to grow from
  1.8 GiB to the external 8 GiB ceiling and abort the process"* (`:105-111`)
  `[C]`.

[ADR-1703](../../09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
retired BatSat, and `IncrementalSat` — which is what `dpll_lia.rs` imports —
now holds a `NativeIncrementalCdcl` (`crates/axeyum-cnf/src/lib.rs:672-675`)
`[C]`. **The failure mode these constants protect against was a property of a
solver that no longer runs.** That does not make the constants wrong: the
native core has its own memory behaviour and it has not been measured on these
shapes. It makes them **unvalidated**, on 15 files, at S effort — re-run the
three named control files (`pursuit-safety-16`, `windowreal-no_t_deadlock-17`,
`tgc_io-safe-20`) under the native core and re-derive the rectangle.

This is the same trap CLAUDE.md's evidence section names: a constant whose
stated reason is no longer true reads as measured protection.

### 5. QF_NIA: incremental linearization exists and gets 600 ms

`check_with_nia` (`crates/axeyum-solver/src/nia_linearize.rs`) already
implements what MathSAT calls incremental linearization `[C]`: product
abstraction with valid sign/zero lemmas (`:104`), McCormick envelopes over
entailed constant bounds (`:1190`), an **exact small-domain product split** at
width ≤ 4 (`MAX_SMALL_DOMAIN_WIDTH`, `config_registry.rs:1730-1746`), and a
**tangent-plane refinement loop** that cuts off a spurious model and re-solves
(`:1254-1272`, `solve_with_refinement`, `MAX_REFINEMENT_ROUNDS = 64`).

It runs on `NIA_SLICE_MS = 600` milliseconds (`nia_linearize.rs:66`) — of a
24,000 ms budget — raised to `total / NIA_MCCORMICK_BUDGET_SHARE` = one third
**only when McCormick envelopes or splits were actually emitted**
(`:1245-1251`) `[C]`. Everything else falls through to `int-blast-ladder`,
which the census charges with 30 search timeouts and 17 CNF-cap declines of the
61 losses `[C]`.

The 600 ms is documented as deliberate — "the div/mod refutations are tiny and
decide well within it, and a harder relaxation declines to the width ladder"
(`:63-65`) — and the plan records that three cheap NIA levers were built and
refuted at 0, +1 and +3 files, and that 4× the clock bought 0 of 20 timeouts
`[C]`. So the prior here is *pessimistic*, and I am not claiming the slice is
the cause. What I am claiming is narrower and checkable: **the budget sweep on
the route that implements the reference technique has not been run against the
current board**, it is a one-constant experiment, and the plan's own S12 slice
(the coefficient-width rung, scored on the 32 one-live-rung files) is the
better-supported lever and should stay first.

**The one genuinely new capability in this space is small and specific.** The
2018 MathSAT lemma set is essentially what we already emit (sign, zero,
tangent planes). The 2026 revisit — Dančo, Chvalovský, Janota,
*Revisiting Incremental Linearization*, arXiv:2608.04835, §4 axiom table `[P]`
— adds **secant-based linear bounds**: over any unit interval `[v, v+1]`, the
monomial `x^k` (and mixed `x^k·y^l`) is bounded by the secant through
`(v, v^k)` with slope `v^(k-1)`, which is strictly tighter than a generic
tangent plane on power-heavy benchmarks. Their headline instance,
`x³ + y³ + z³ = 79`, times out at three minutes on cvc5, MathSAT, Yices2 **and**
Z3 and falls in ~20 s to the prototype `[P]`. For us this is a **new lemma
schema inside a refinement loop we already own** (`tangent_lemmas`,
`solve_with_refinement`) — genuinely S effort. It is not a fit for the
`VeryMax/ITS` family that is 134 of our 200 QF_NIA files and 74 of the misses,
so do not score it there; score it on the non-`VeryMax` remainder, which is
where the plan already says the honest target lives. `[I]` on the fit
judgement.

### 6–7

#6 is the companion lane's finding #2 and I defer to it entirely: our
`select_entering` is Bland's rule unconditionally (`simplex.rs:550-570`) `[C]`,
while Z3 selects for **short rows** — its own comment says *"a short row
produces short infeasibility explanation and benefits at least one pivot
operation"* (`references/z3/src/math/lp/lp_primal_core_solver.h:180-182`) — and
switches to Bland only after `m_bland_mode_threshold = 1000` repeated leaving
variables (`:645`, `:370-390`) `[C]`.

#7: `scan_dl` (`dl_online.rs:794`) refuses the whole query on any coefficient
other than ±1, a mixed `Int`/`Real` query, an uninterpreted application, or any
`i128` overflow while scaling rational bounds by the denominator LCM
(`dl_online.rs:653-706`) `[C]`. QF_RDL benchmarks carry rational constants, so
the LCM path is the plausible refusal; the query then falls to the LRA route
and the 1,024-atom cap. **Unmeasured** — count the `None`s on the 14.

---

## 3. Per-division answers to Q1–Q4

### Q1 — QF_UFLIA (gap 58): what makes combination hard, and what takes 122 → 180

**What the references do** is in finding #1 above with citations: native
congruence closure inside the search, no Ackermannization on this logic in
either solver, and a cheap filter on which interface equalities to propose
(Z3's model-value bucketing; cvc5's care graph). cvc5 additionally has a
*forced*, two-way arith↔UF equality bridge (`ArithCongruenceManager`) that Z3
does not: when simplex pins a watched slack to zero it asserts `x = y` into the
shared equality engine directly rather than proposing a split `[C]`.

**What takes us from 122 to 180 is not a new algorithm.** It is, in order: let
the MBTC route run at all (#1); make `LiaTheory` cheap enough that the
combination's inner integer checks are not full branch-and-bounds (#2); then
the companion lane's #5/#5b to make the interface-equality proposal set small.
The "clean subset relation" the brief noted — zero files we win that the
reference loses — is consistent with all 58 dying in one route, which the
census says they do.

**The wide-integer story is closed and should not be reopened.** ADR-0376's
ablation was re-run on HEAD on 2026-09-06: rescale every wide numeral, 6 of 6
still `unknown`; delete every assert mentioning one, 6 of 6 still `unknown`,
against a non-vacuous control `[C]`. The 6 `route-decline` files are
width-ladder work, not literal-type work.

### Q2 — QF_LRA (gap 52, or 84 against Yices): implementation quality, and which parts

The brief's framing is right — this is engineering, not a missing algorithm —
but two of the specific hypotheses it lists are **refuted by the reference
source**, and briefing them would waste a lane:

- **Float-first with exact fallback: not what either reference does.** Z3's
  production tableau is `static_matrix<mpq, numeric_pair<mpq>>`
  (`references/z3/src/math/lp/lar_core_solver.h:34`); `double` appears in 6 of
  126 files in `lp/`, always as a conversion helper or an NLA heuristic `[C]`.
  cvc5's `Tableau : public Matrix<Rational>` over GMP
  (`theory/arith/linear/tableau.h:37`) `[C]`. cvc5 *does* have a float layer —
  `ApproxGLPK` (`approx_simplex.cpp`, 3,674 lines) — but it is an **unsound MIP
  oracle whose guesses are replayed and re-checked exactly**, used for integer
  cuts and branches, not a fast path for LP feasibility `[C]`. Do not build a
  double-precision simplex.
- **Delta rationals: we already have them, done the same way.** Ours is
  `Delta { c, d }` with lexicographic compare (`simplex.rs:201-252`); Z3's is
  `numeric_pair<mpq>` (`numeric_pair.h:116-131`, `:297`) with δ instantiated at
  model time by `find_delta_for_strict_bounds` (`lar_core_solver.h:189-220`);
  cvc5's is `DeltaRational` with `deltaValueForTotalOrder`
  (`theory_arith_private.cpp:4610-4677`) `[C]`. No gap.
- **Explanation minimality: a real gap, and the two references solve it
  differently.** Z3 gets it *by construction* from the short-row pivot rule and
  runs **no** post-hoc minimization
  (`lar_solver.cpp:181-195`, `:1514-1526`) `[C]`. cvc5 accepts non-minimal
  Farkas certificates — its own comment says *"There is no requirement that the
  proof is minimal"* (`constraint.h:312-314`) — and then runs a greedy
  `weakestExplanation` pass (`linear_equality.cpp:682-735`) `[C]`. We do
  neither: we take whatever row the Bland loop lands on. This is a cheap
  follow-on to #6.
- **Incrementality across push/pop: we already have it, and it was measured.**
  `simplex_cold_restarts = 0` across 6,571 checks on `blending/1` `[C]`. The
  brief's hypothesis that we re-decide from scratch is the exact premise S4
  falsified before writing code. Do not re-brief it.
- **Atom preprocessing: the live gap**, and it is finding #3.

### Q3 — QF_LIA (26), QF_IDL (18), QF_RDL (12)

**Do competitive solvers specialize difference logic? Z3 yes, cvc5 no — and we
already do.**

- Z3 has `theory_diff_logic` / `theory_dense_diff_logic` over a
  `dl_graph` (`references/z3/src/smt/diff_logic.h`), with incremental
  Dijkstra-style feasibility restoration seeded from the new edge
  (`make_feasible`, `diff_logic.h:352-431`) rather than a Bellman–Ford
  recompute, and trail-scoped edge push/pop (`:865-899`) `[C]`. But the
  dispatch is surprising: the plain `setup_QF_IDL()`
  (`smt_setup.cpp:319-323`) calls `setup_lra_arith()` → **general
  `theory_lra`**; the graph theory is reached only through the
  `static_features`-analyzed overloads under `CFG_AUTO`
  (`smt_setup.cpp:325-380`), which verify `is_in_diff_logic(st)` and *throw*
  `default_exception` on a mislabeled benchmark rather than falling back `[C]`.
- cvc5 has **no** difference-logic engine at all: an exhaustive search for
  `*idl*`/`*diff*`/`bellman`/`negative.cycle`/`shortest.path` across
  `references/cvc5/src` returns nothing; `LogicInfo::d_differenceLogic` exists
  and its 8 call sites only tune simplex options (`set_defaults.cpp:817,834`)
  `[C]`.
- **We have the specialized algorithm and the references' better half.**
  `dl_online.rs` is Cotton–Maler incremental negative-cycle detection over a
  feasible potential, δ-weights for strict real bounds, integer tightening,
  unit-multiplier Farkas certificates that are *verified before being reported*,
  and replay-gated `sat` (`dl_online.rs:1-90`) `[C]`. Nobody should be briefed
  to build it. QF_IDL's remaining 18 are, per the profile, a Boolean-search and
  dispatch-overrun story (S1/S1b/S2 territory), not a theory story.

**For QF_LIA — cuts, branch-and-bound, and the bit-blast fallback — we have all
three.** Gomory fractional cuts (`lra.rs:1731-1810`), branch-and-bound with a
50,000-node cap (`lra.rs:1198`), gcd-aware strict-integer tightening, and the
`int-blast-ladder` bounded-width blast `[C]`. So the answer to "what cut
strategy is missing" is **not a cut family first**. In priority order the gaps
are:

1. **Where the reasoning runs** — ours is offline inside a theory check, Z3's is
   in-loop as propagated literals and fresh Boolean atoms (§ finding #2). This
   is the architectural difference and it dominates.
2. **What runs before branch-and-bound** — Z3 puts GCD, cube tests, HNF cuts
   and Diophantine tightening ahead of it, adaptively throttled, and reaches
   branching last (`int_solver.cpp:270-291`) `[C]`. We branch first.
3. **The admission rectangle that stops the route entirely** (#4).

Gomory itself is the *least* supported item: cvc5 generates no Gomory cuts of
its own, Yices's multi-cut path is dead code behind `if (false && …)`, and Z3
switches Gomory **off** while its Diophantine solver is productive — three
implementations, three ways of not relying on them (companion lane §5.4, and
Z3's own throttle comments) `[C]`. The Diophantine pre-solve is the item both
lanes independently rank highest in this family.

**Correcting the brief on one point.** The brief asks whether we detect and
specialize difference logic. We do, and so does Yices2 — Dutertre's CAV 2014
paper says plainly that Yices *"includes two specialized solvers for the
difference-logic fragments… These two solvers rely on a variant of the
Floyd–Warshall algorithm"* `[P]`. But QF_IDL and QF_RDL **have had no
standalone SMT-COMP division since 2023**: they were merged into
`QF_LinearIntArith` and `QF_LinearRealArith` respectively `[D]`, whose 2024/2025
winners are OpenSMT and Yices2. So there is no "QF_IDL winner's system
description" to mine; the specialization is old, documented, and we have it.

### Q4 — QF_NIA (48): the single highest-value technique

**Finding #5: we already implement the technique the reference literature
points at.** Incremental linearization — abstract each product, solve over LIA,
check the model, add valid linear lemmas, iterate — is exactly what
`nia_linearize.rs` does, and the 2018 MathSAT lemma set (sign, eq-zero,
tangent planes) is essentially the set we emit `[P]` `[C]`. It runs on 600 ms
of 24 s.

**Ranked, for a stack that already has LIA/LRA simplex, CDCL(T), McCormick
spatial branch-and-bound and bounded-integer bit-blasting:**

1. **Secant-based linear bounds** added to the existing refinement loop
   (§ finding #5). New capability, small, and the only item here that is not
   already built.
2. **Local search** — and this is where the competition results actually point.
   `QF_NonLinearIntArith` went to **Z3++** in 2023 and **Z3-alpha** in 2024 and
   2025 `[D]`. Both are *meta-level wrappers around Z3's existing engine*, not
   new decision procedures: Z3++ (Cai's group, ISCAS) bolts local search onto
   Z3 in the HybridSMT design (ICSE 2024 — CDCL(T) outer, LocalSMT inner,
   results fed back to branching); Z3-alpha (Waterloo) is an MCTS/RL **tactic
   sequencer** over Z3's own tactics `[D]`. The reported strength of
   `LocalSMT` is concentrated on the *no-Boolean-structure* slice, which its
   authors measure at 78–88% of QF_LIA/QF_NIA benchmarks by count `[P]`. A
   portfolio race (local search alongside the existing route) captures much of
   this at low cost; the deep HybridSMT integration is a separate, larger
   investment. **L effort, highest measured competition payoff.**
3. **Bound-widening around the bit-blast we already have.** The MathSAT paper
   describes this as prior art and names its limit: it finds models and *cannot
   prove unsat unless the problem is bounded* `[P]`. Our `int-blast-ladder`
   already is this; the marginal work is the widening driver, which the plan's
   S11/S12 width-rung work already targets.
4. **ICP / `nlsat`.** Lowest priority: it targets the real relaxation, which is
   where our McCormick spatial branch-and-bound already sits, so it duplicates
   an engine rather than reusing one `[I]`. And the competition evidence is
   against it as the differentiator — raw Z3 is not what wins this division;
   wrappers over Z3 are.

**The uncomfortable reading of #2, stated rather than buried:** the two
solvers that win QF_NIA win it with a *portfolio/strategy* layer over an
existing engine, not with a better arithmetic decision procedure. That is worth
knowing before a lane is briefed to build one.

---

## 3b. Who actually wins these divisions, and what that implies for our reference

The brief asked who wins each division and what their system description says.
Two structural facts change how the board should be read `[D]`, all from
`smt-comp.github.io/{2023,2024,2025}`:

**SMT-COMP merged these logics into family divisions in 2023.**
`QF_LinearIntArith` = QF_LIA ∪ QF_IDL ∪ QF_LIRA;
`QF_LinearRealArith` = QF_LRA ∪ QF_RDL;
`QF_NonLinearIntArith` = QF_NIA ∪ QF_NIRA;
`QF_Equality_LinearArith` ≈ the QF_UFLIA/QF_UFLRA family. **QF_IDL and QF_RDL
have no standalone winner after 2022.**

| Division (family) | 2023 | 2024 | 2025 |
|---|---|---|---|
| QF_LinearIntArith | Z3++ | **OpenSMT** | **OpenSMT** (Yices2 2nd) |
| QF_LinearRealArith | Yices2 | **OpenSMT** | **Yices2** (OpenSMT 2nd) |
| QF_NonLinearIntArith | Z3++ | **Z3-alpha** | **Z3-alpha** |
| QF_Equality_LinearArith | — | **SMTInterpol** | **SMTInterpol** (cvc5 2nd) |

**cvc5 does not lead a single one of the six divisions this lane covers.**
That matters because five of our six boards are measured against cvc5. The
[second-reference lane](../../../plan/smt-parity-plan-2026-09-05.md) already
found QF_LRA's real gap is **84 files, not 52** against Yices2, and QF_UFLIA is
scored against SMTInterpol. The 2023 `QF_LinearIntArith` field was decided by
**43 files across four solvers** (5776 / 5802 / 5816 / 5819) `[D]` — so
"who leads" in linear arithmetic is genuinely close, and a division-specific
reference correction is required, never a blanket discount. When quoting an
arithmetic gap, name the reference.

**The nonlinear integer winners are wrappers, not engines.** Z3++ is Z3 plus
local search (Cai's group); Z3-alpha is an MCTS/reinforcement-learning
*tactic sequencer* over Z3's own tactics `[D]`. Neither introduced a new
arithmetic decision procedure.

**OpenSMT's own 2022 system description** is mostly SAT-layer engineering —
phase saving, glue-clause heuristics, Luby restarts, rational-number pooling to
avoid allocation — and describes its QF_LIA support as "rudimentary… based on
branch-and-bound" `[D]`. Its 2024/2025 wins came after that document and the
newer description was not obtained, so **what changed is unverified**; do not
infer a technique from the win.

---

## 4. What we already have — check this before briefing "build X"

Every row read from source by this lane. This section exists because CLAUDE.md
records that more lane-hours go to re-deriving what exists than to difficulty.

| Capability | Where | Note |
|---|---|---|
| Dutertre–de Moura general simplex, δ-rationals, Farkas, warm basis | `simplex.rs` | `O(rows)` pivot update since S4; dense storage; Bland only |
| Wide-rational promotion inside the tableau (ADR-1702) | `simplex.rs:20-40` | overflow no longer abandons the search |
| Online LRA theory on `CdclT`, form-indexed implied bounds | `lra_online.rs` | propagation is same-form only |
| Online LIA theory, LP-relaxation negation probe, deletion-minimized cores | `lia_online.rs` | re-decides via the offline decider |
| Gomory fractional cuts, integer branch-and-bound, gcd tightening | `lra.rs:1198-1810` | on a separate throwaway tableau |
| Cotton–Maler incremental difference logic with verified Farkas cycles | `dl_online.rs` | full QF_IDL/QF_RDL decision procedure |
| Model-based EUF+LIA / EUF+LRA combination (Nelson–Oppen, convexity-free) | `uflia_online.rs`, `uflra_online.rs`, `combined_theory_lia.rs` | unreachable on the losing QF_UFLIA population |
| Interface-equality proposal by model value | `theory_combination.rs:120` | the MBTC proposal step, under a different name |
| Lazy Ackermann CEGAR for UF+arith | `euf.rs:301,789` | the route that currently owns QF_UFLIA |
| NIA product abstraction, sign/zero lemmas, McCormick envelopes, tangent-plane refinement, exact small-domain split | `nia_linearize.rs` | incremental linearization, on a 600 ms slice |
| McCormick spatial branch-and-bound for NRA | `nra.rs` | separate route |
| Bounded-integer bit-blast ladder | `lia.rs`, `axeyum-rewrite/src/int_blast.rs` | `DEFAULT_INT_WIDTH = 32`, `MAX_INT_BLAST_WIDTH = 64` |

---

## 5. Measurements this lane could not make

Stated plainly so nobody inherits an inference as a fact:

1. **Distinct linear forms vs tableau rows** on the 33-file QF_LRA population.
   `assign_forms` already returns the numerator; one `eprintln!` next to
   `build_simplex_engine` gives the ratio. Without it, "350 rows for 75
   variables is one-row-per-atom" is `[I]`, not `[C]`.
2. **Whether the 52 CEGAR-class QF_UFLIA files all have `pairs > 64`**, and
   what the MBTC route does on them when it is allowed to run.
3. **`LiaTheory::check_terms` call count and wall** on traced QF_LIA files —
   the number that would price finding #2.
4. **The `lia-dpll` rectangle under the native core.** The old numbers are
   BatSat's.
5. **`NIA_SLICE_MS` swept over the 61 QF_NIA losses.**
6. **`scan_dl` refusal counts** on the 14 QF_RDL losses.
7. **Secant lemmas scored outside the `VeryMax/ITS` family** — the family is
   134 of 200 QF_NIA files, so a whole-division number would hide the effect
   either way.

Two things I could not check at all, flagged so nobody inherits them as
settled: **OpenSMT's post-2022 algorithmic changes** (it now wins two of our
six families and only its 2022 description was obtainable), and **whether the
52 CEGAR-class QF_UFLIA files would in fact be admitted by
`uflia_online`** — the second is item 2 above and is the load-bearing one.

None of these needs a code change beyond a counter, and each one either
converts a `[I]` above into a `[C]` or kills it. Per this repository's standing
rule: if a route declines, find the bail-out condition rather than trusting the
printed message — on QF_UFLIA the printed message names the CEGAR loop's
deadline, and the *reason* the file was lost is that nothing after that loop
was ever going to run.
