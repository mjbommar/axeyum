# Lane: quant-compose — the four OFF levers, sized before composing them, and the one nested shape none of them reaches

<!-- plan-section: lane-status -->

**Lane QUANT-COMPOSE (`STOPPED-EARLY`, quant-compose, 2026-09-16).** The brief
was: compose ADR-2120 / ADR-2127 / ADR-2130 / ADR-2133's four OFF levers on
ADR-2113's 53 reference-minimal `UFLIA` cores, on the hypothesis that each
removes a different link of one chain and the composition moves what no single
lever moves. **The coordinator closed the round after deliverable 1 (sizing) and
the READING half of deliverable 2.** The 53-core stacked sweep, the 800-file
pinned A/B, the held-out draw, and any Rust **did not run** and are not claimed
here. No ADR was written (ADR-2138 is unspent and stays allocated to this
question).

## 1. Baseline, re-derived — and the brief's reference attribution is wrong

Every number below is counted from the row data named beside it, not inherited
from a board line or from the brief.

**The three sources are the same population.** For each division the
head-to-head TSV, `bench-results/parity-lists/<div>.txt`, and the Tier-1 ledger
carry byte-identical 200-file basename sets (`h2h==parity: True`,
`ledger==parity: True`). So the counts below are comparable without a join
caveat.

| division | ours | z3 | cvc5 | best-ref (union) | both |
|---|---:|---:|---:|---:|---:|
| `UFLIA` | **86** / 200 | 139 | 142 | **144** | 137 |
| `AUFDTLIRA` | **119** / 200 | 176 | 176 | **176** | 176 |

- **Ours** is counted from `bench-results/ledger/t1-<div>-db31113fa.tsv`, 200
  rows each, single arm `main`, single `binary_sha` `db31113fa`:
  `UFLIA` `unsat` 86 / `unknown` 114; `AUFDTLIRA` `unsat` 119 / `unknown` 81.
  **Zero `sat` in either division** — every decided row is a refutation.
- **z3 / cvc5** are counted from
  `bench-results/six-divisions-headtohead-20260912/UFLIA.tsv` and
  `bench-results/dt-divisions-headtohead-20260912/AUFDTLIRA.tsv`.

**Correction to the brief.** The brief frames `UFLIA` as "86/200 vs cvc5 144".
**cvc5 alone decides 142**; `144` is the UNION of z3 (139) and cvc5 (142) — the
`best ref` column of `docs/plan/status/board-six.md:15`, which no single
reference solver achieves. The honest gap statements are: 58 to the best-ref
union, 56 to cvc5, 53 to z3. `AUFDTLIRA`'s "119 vs z3 176" is correct as
written, and there z3 and cvc5 decide the *same* 176 (union 176, both 176), so
no union/single distinction exists.

**Freshness, stated rather than assumed.** `db31113fa` is a real commit
(`fix(solver): two clippy errors the push battery found`). This branch's HEAD is
**313 commits** ahead of it, **84 of which touch `crates/axeyum-solver/src`**.
So `86` and `119` are a *snapshot*, not a measurement of this tree, and the
ledger sweep itself was spread across `server5` (67 rows), `server6` (68) and
`server7` (65). The head-to-head reference numbers are older still (2026-09-12)
and put our own `UFLIA` at 71, against the ledger's 86 — the two disagree
because they are two different binaries a division-moving week apart, which is
exactly why a composition A/B must re-derive its own shipped arm rather than
subtract from a board. **A fresh re-derivation of the shipped arm was not run
in this round** (it is the 400-file half of a deliverable the coordinator
cancelled).

**The 53-core population is intact.** `bench-results/quant-instance-probe-20260916/uflia-cores.list`
holds **53** paths under `/nas3/data/axeyum/harness/core-select/cores/`, and all
**53 exist on disk** (`missing=0`), so the sweep's subject is still addressable.

**The lane binary exists and is freshness-verified, and it was never used.**
`bench-results/quant-compose-20260916/build.sh` built one `smtcomp_cli` at
this HEAD into a private target dir and refused to publish it unless no
`crates/**/*.rs` was newer (`FRESH: no crates/**/*.rs is newer than …`) —
the guard against cargo'''s mtime freshness handing back an earlier branch'''s
binary. sha256 `1ca58672c11008f8a679df7868cbf77a62a3e0f86606b0f39a63a07536ba1de2`,
45,415,624 bytes, at `4f81de9c1`. **No sweep was run with it**; it is recorded
so the next round'''s arms can be the same bytes, which is the whole point of
building it once.

**The three ADRs' own OFF arms do not agree with each other**, and that sets the
noise floor any composition claim must clear. On the same 53 cores at the same
24 s / 8 GiB budget: ADR-2120 §7 `OFF decided 15`, ADR-2130 §6 `OFF 15`,
ADR-2133 `OFF decides 16`. A ±1 spread at fixed code and fixed population means
**a composition that decides 16 or 17 has shown nothing**; the design threshold
has to be a *stable* gain under the 3× mover recheck, as every one of those
three ADRs already required.

## 2. The four levers, at `file:line`

| ADR | env name | constant | shipped | ON value | read site | what ON does |
|---|---|---|---|---|---|---|
| 2120 | `AXEYUM_QINST_POSITIVE_PATH` | `POSITIVE_PATH_LEVEL` (`qinst_egraph.rs:127`) | `0` | `1` | `qinst_egraph.rs:1952`, `:2739` | `positive_path_step` (`:475`) widens the tracked-polarity whitelist from `and`/`or` only (`:483`) to `not` flipping, `=>` flipping its antecedent, an `ite` BRANCH keeping (`:485-487`); and `:2739` lets the loop START on registrations alone when no top-level `forall` exists |
| 2127 | `AXEYUM_MACRO_INLINE` | — (`OnceLock`, no registry row) | off | `1` | `auto.rs:13444` via `quant_macro_inline.rs:124` | runs definitional macro inlining as a pre-pass; armed **only** by exactly `"1"` (`parse_macro_inline_lever`, `:127`) |
| 2130 | `AXEYUM_QINST_GROUND_SESSION` | `GROUND_SESSION_LEVEL` (`qinst_egraph.rs:361`) | `0` | `2` | `:423` (`ground_session_abstracts`), `:444` (`ground_session_hosts_arithmetic`), `:3032`, `:5241`, `:5249`, `:4885`, `:4902-4903` | `1` abstracts a Boolean-position term the EUF encoder has no arm for to a free propositional variable; `2` HOSTS the arithmetic ones in a `LiaTheory` sub-theory and abstracts the rest |
| 2133 | `AXEYUM_QINST_GEN_LADDER` | `GENERATION_LADDER_LEVEL` (`qinst_egraph.rs:1283`) | `0` | `1` | `:1351` (`generation_ladder_enabled`), consumed at `:5409`/`:5411` and `:5437` | replaces the single `FLOOD_FINAL_SUBSET_MAX_GENERATION` pre-check with an ascending `gen<=0, <=1, …` ladder (`generation_ladder_check`, `:5337`) under `remaining/GENERATION_LADDER_BUDGET_DIVISOR` |

**Do any two interact in code? Measured by reading every call site: no — not
one site reads two levels.** `positive_path_level()` is read at `:1952` and
`:2739`; `ground_session_level()` at `:423`, `:444`, `:3032`; `generation_ladder_level()`
at `:1351`; `macro_inline_enabled()` at `auto.rs:13444`. The only *mutual
exclusion* in the set is internal to one lever: `:5437`'s
`if !generation_ladder_enabled() && ground.len() >= FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND`
makes the ladder and the shipped single-layer pre-check alternatives of each
other, not of any other lever.

**So the composition hypothesis is a DATA-flow claim, not a control-flow one**,
and that is what a stacked A/B could and could not show:

- **It CAN show**: whether 2120's enlarged admitted set (the 660,992 tuples
  ADR-2120 §7a handed off) changes what 2130's hosted-arithmetic session and
  2133's ladder see, since both consume the same `ground` vector that 2120
  grows. The levers are ordered along one pipe: 2127 rewrites the input, 2120
  decides what enters `ground`, 2130 decides whether the warm session can exist
  over `ground`, 2133 decides what subset of `ground` the final check takes.
- **It CANNOT show** which lever is responsible for a mover from the all-ON arm
  alone — that is exactly why the brief's all-but-one arms exist, and why a
  10-arm design was the right one.
- **It cannot distinguish a gain from ambient noise at n=1 or n=2.** See the
  ±1 spread in §1.
- **It says nothing about the 476 NESTED instances** QUANT-REACH-DIFF counted
  (46.4 % of 1,025), because no lever in this set addresses them — see §3.

**One registry gap found while sizing, recorded not fixed.**
`AXEYUM_MACRO_INLINE` has **no `ConfigEntry` row** in
`crates/axeyum-solver/src/config_registry.rs` (`grep` returns zero hits),
unlike the other three, which carry `POSITIVE_PATH_LEVEL` (`:7706`),
`GROUND_SESSION_LEVEL` (`:7173`) and `GENERATION_LADDER_LEVEL` (`:7125`). It is
a `OnceLock` boolean in `quant_macro_inline.rs:124` rather than a `cap_lever!`
integer, which is why the registry's scanner never named it — the same
mechanical blind spot `ONLINE_QUANTIFIER_LIMITS`'s own registry note already
records for struct-valued constants. Not closed here (this round writes no
Rust); it is a real, small, separable increment.

## 3. Nested activation: how z3 and cvc5 do it, and what ours does instead

All reference line numbers below were verified by printing the line; paths are
relative to the (gitignored) `references/` clone root.

**z3 — activation IS a SAT assignment, and it is automatic for a nested
quantifier.**

1. A quantifier gets its own Boolean variable at internalization:
   `z3/src/smt/smt_internalizer.cpp:656` `bool_var v = mk_bool_var(q);`,
   flagged `:664` `d.set_quantifier_flag();`, registered `:665`
   `m_qmanager->add(q, generation);`. Reached from `:523`
   `internalize_quantifier(to_quantifier(n), gate_ctx);`.
2. **`add` compiles no patterns.** `z3/src/smt/smt_quantifier.cpp:166`
   `void add(quantifier * q, unsigned generation)` only records and forwards to
   the plugin (`:170`), whose `add` (`:790`) registers with the model finder
   only.
3. Patterns are compiled in the **assignment** handler:
   `z3/src/smt/smt_quantifier.cpp:818` `void assign_eh(quantifier * q) override`,
   which sets `m_active = true` (`:819`) and calls `m_mam->add_pattern(q, mp);`
   (`:849`; the lazy variant `m_lazy_mam->add_pattern` at `:845`). It is reached from `smt_context.cpp:1871` `m_qmanager->assign_eh(q);`
   ← `:1485` `assign_quantifier(...)` ← `:1482` `if (get_assignment(v) == l_true)`
   ← `:1473` `else if (d.is_quantifier())`.
4. Relevancy is a second, required gate: `smt_context.cpp:307` excludes
   quantifiers from the atom-propagation queue at relevancy level 1, and
   `:1687` `relevant_eh` / `:1694` is the other entry, whose own comment
   (`:1691-1692`) says "Quantifiers are only asserted when marked as relevant."
5. **The nested case is free.** The instance is asserted as the CLAUSE
   `qi_queue.cpp:288` `lemma = m.mk_or(m.mk_not(q), s_instance);` and then
   re-internalized at `qi_queue.cpp:336`
   `m_context.internalize_instance(lemma, pr1, gen);` →
   `smt_context.h:1784` `internalize_assertion(body, pr, generation);` →
   `smt_internalizer.cpp:288`, which splits the `or` (`:307-313`) and sends any
   disjunct that is itself a `forall` back through `:523` → `:656`. So a
   `forall` exposed by instantiation gets its own fresh `bool_var`, and becomes
   active exactly when the SAT solver assigns it true and relevant. **No
   special nested path exists, because none is needed.**

**cvc5 — a context-dependent asserted-quantifier LIST, not a dedicated
activation literal in the quantifiers module.**

1. The instance is `(=> q body)`: `cvc5/src/theory/quantifiers/instantiate.cpp:293`
   `Node lem = NodeManager::mkNode(Kind::IMPLIES, q, body);`, queued `:339`.
2. A nested `FORALL` is pre-registered as a term:
   `theory_quantifiers.cpp:83` `preRegisterTerm`, `:93`
   `getQuantifiersEngine()->preRegisterQuantifier(n);` →
   `quantifiers_engine.cpp:709`, with one-time setup at
   `quantifiers_registry.cpp:32`.
3. Activation is the SAT solver sending the `FORALL` as a **fact**:
   `theory_quantifiers.cpp:173` `preNotifyFact`, `:180` `if (k == Kind::FORALL)`,
   `:182` `assertQuantifier(atom, polarity);` →
   `quantifiers_engine.cpp:738` (`:764` register, `:766` `d_model->assertQuantifier(f);`)
   → `first_order_model.cpp:91` / `:95` `d_forall_asserts.push_back(n);`.
4. E-matching then iterates exactly that list:
   `ematching/instantiation_engine.cpp:162` `getNumAssertedQuantifiers()`,
   `:165` `getAssertedQuantifier(i, true)`, `:166`
   `if (shouldProcess(q) && m->isQuantifierActive(q))`. (`isQuantifierActive`,
   `first_order_model.cpp:297`, is a per-round suppression flag modules set —
   **not** the activation mechanism; it is cleared every round at `:220`.)

**Both references therefore get nested activation from the same place: the
instance is asserted back into the SAT/theory layer as an ordinary formula, and
ordinary registration gives the nested `forall` whatever handle the matcher
keys on.**

### Does ADR-2120's positive path cover the nested case? Reading says PARTLY, and names the exact gap

Ours has no assertion-back step. A nested universal is discovered, matched, its
tuples computed — and then the tuples are kept or dropped on whether the
registration carries a `PositiveContext`:

- `qinst_egraph.rs:7279` `if quantifier.context.is_some()` — hand off to
  `pending_positive` (counted `inactive_handed_off` / `inactive_positive_capped`,
  `:7291`);
- `qinst_egraph.rs:7294` `batch.rejects.inactive_dropped += tuples.len();` —
  otherwise thrown away outright.

A context exists at exactly one place: `qinst_egraph.rs:1937`
`context: (polarity == Some(true)).then(|| PositiveContext { … })`. And
`polarity` is forced to `None` for an entire subtree the moment the walk enters
a `forall` body — `qinst_egraph.rs:1948`
`collect_nested_registrations_rec(arena, inner_body, prefix, path, None, scan);`,
whose own comment at `:1943-1945` says "The path would now cross this binder, so
tracking is dropped". The lazy-discovery scan enforces the same thing again:
`qinst_egraph.rs:2185-2186` `if registration.context.is_none() … continue;`.

So, stated as the two halves of the question:

- **COVERED by ADR-2120 level 1**: a universal nested under `and`/`or`/`not`/
  `=>`/`ite`-branch inside a trusted formula's matrix, after that formula's own
  top-level prenex is peeled (`:2173` `peel_foralls`, `:2181` `Some(true)`). This
  is the `rej_nocontext` population QUANT-REACH-DIFF counted at **102 of 169
  MATCHED-REJECTED (60.4 %)**.
- **NOT COVERED**: a universal nested **inside another universal's binder**
  (`∀x. … (∀y. …)` where the inner one is not part of the outer prenex). It
  gets `context: None` at `:1948`, is skipped by discovery at `:2186`, and is
  `inactive_dropped` at `:7294` **with the lever ON**. Widening
  `POSITIVE_PATH_LEVEL` cannot reach it: the level is consumed only by
  `positive_path_step` (`:1956`), and `:1948` passes `None` unconditionally,
  before any level is consulted. **A crossed binder is also refused by the
  CHECKER on soundness grounds** (`positive_instance_formula`, `:1975-1980`:
  "crossing one is genuinely unsound"), so this is not a whitelist to widen —
  it needs the reference solvers' *other* mechanism: an activation record for
  the instantiated nested universal, i.e. asserting the instance body back and
  letting the nested `forall` acquire its own handle, which is what
  `qi_queue.cpp:336` and `theory_quantifiers.cpp:182` each do.

**This reading is NOT the decision the brief asked for.** The brief required
deciding from a fixture that exercises exactly that shape, and **no fixture was
built or run** — the coordinator's stop landed before the code half. What is
established here is where in our source the two branches diverge and that the
gap is structural rather than a level setting; what is **not** established is
how much of QUANT-REACH-DIFF's 476-instance NESTED class actually has this
shape, which only a fixture plus a per-core census can say. That measurement is
the next single build, sized in §4.

## 3b. Every citation in this file is checked by a script, and 13 of them were wrong

Both §2 and §3 are nothing but `file:line` claims, and a `file:line` claim is the
easiest kind of evidence to get wrong and the hardest to notice — it renders
identically whether or not it points anywhere. So the claims are checked
mechanically, by two committed scripts whose **exit status depends on the
finding**:

- `bench-results/quant-compose-20260916/check-our-citations.py` — **37** claims
  against this tree's `crates/axeyum-solver/src/`;
- `bench-results/quant-compose-20260916/check-reference-citations.py` — **34**
  claims against the (gitignored) `references/z3` and `references/cvc5` clones
  in the main checkout.

Each asserts that a named substring is present on the named line, prints the
line it actually found, points at the true line when it misses, and exits `1` on
any miss. Both now report `BAD=0`.

**They were not decoration.** On their first honest run they failed **13 of 71**:

- **10 of 37 of my own**, all off by 1–17 lines, including the two the whole §3
  argument rests on — `qinst_egraph.rs:1948` (the `None` that drops polarity
  tracking, which I had written as `:1946`) and `:7279` (the
  `context.is_some()` gate, written as `:7277`), plus all three
  `config_registry` row anchors.
- **3 of 34 of the reference citations**, which reached me from a delegated
  reading that stated "all line numbers verified by printing":
  `smt_quantifier.cpp` `m_mam->add_pattern` is at **`:849`** (not `:848`; `:845`
  is the `m_lazy_mam` variant), `smt_context.cpp`'s `l_true` activation gate is
  at **`:1482`** (not `:1483`, which is its comment), and cvc5's `preNotifyFact`
  begins at **`:173`** (not `:174`, its second parameter). A verification claim
  I did not run myself was wrong at 8.8 %.

**And both are shown to fail, not assumed to.** Each was mutated by ONE
line-number digit and required to die: `check-our-citations.py`
`qinst_egraph.rs` `1948 -> 1947`, and `check-reference-citations.py`
`smt_context.cpp` `1482 -> 1481` — the two lines the §3 argument actually
rests on. Both mutants exit **1** with **exactly one** `FAIL`, naming the
wrong line's real content (`prefix.extend(inner_vars);` and
`SASSERT(is_quantifier(...))`). Run from scratch copies, never in the shared
worktree.

## 4. Deliverables: MET / NOT MET

| # | deliverable | status | the number that says so |
|---|---|---|---|
| 1 | sizing before code | **MET** | 200/200/200-row population identity confirmed across three sources; ours 86 (`UFLIA`) / 119 (`AUFDTLIRA`); references 139/142/union 144 and 176/176/union 176; 53 of 53 cores present; the brief's "cvc5 144" corrected to union-144 / cvc5-142 |
| 2 | design at `file:line` on both sides | **HALF MET (reading only, by instruction)** | 22 verified reference line citations (z3 11, cvc5 11) + our divergence at `qinst_egraph.rs:1948` / `:2186` / `:7294`. The fixture that was to DECIDE it: **not built, not run** |
| 3 | 53-core stacked sweep | **NOT MET — did not run** | cancelled by the coordinator; 0 of the 530 planned runs executed |
| 4 | 800-file pinned A/B + held-out draw | **NOT MET — did not run** | gated on 3 by the brief, and 3 did not run |
| 5 | new Rust | **NOT MET — deliberately none** | 0 lines; `git show --stat` carries no `crates/` path |

**Ship decision: NONE. No default moves.** All four levers remain OFF exactly as
ADR-2120/2127/2130/2133 left them. No criterion line was evaluated, because the
gate that feeds it (deliverable 3) did not run.

**The next single build, sized.** Not the composition sweep — a **fixture and a
counter** first, because the composition's own hypothesis rests on an unmeasured
premise:

1. Two fixtures in `crates/axeyum-solver/tests/` over SATISFIABLE queries: one
   `∀x. P(x) ∧ (∀y. Q(x,y))` (inner universal under a crossed binder) and one
   `∀x. P(x) ∧ (Q(x) ∨ (∀y. R(y)))` (inner universal reachable without crossing
   one), asserting that ON at `AXEYUM_QINST_POSITIVE_PATH=1` the second hands
   off and the first is `inactive_dropped`. ~1 lane-hour; it turns §3's reading
   into a decision.
2. A per-core split of `inactive_dropped` into crossed-binder vs other, printed
   under the existing `AXEYUM_QPROBE_CENSUS`, so the 53-core sweep can say what
   share of the 476 NESTED instances the missing mechanism would actually
   reach. ~2 lane-hours of Rust plus one 53-core census pass.
3. Only then the 10-arm composition sweep, with a stable-mover threshold set
   above the ±1 the three ADRs' own OFF arms already spread across.

## 5. What did not run, plainly

- The 53-core stacked sweep (deliverable 3) — **did not run**, 0 of 530 runs.
- The pinned `UFLIA` / `AUFDTLIRA` 800-row A/B, the `UFNIA` control, the
  held-out 200-file draw, the 3× mover recheck (deliverable 4) — **did not run**.
- A fresh re-derivation of our own shipped-arm decided counts at this HEAD —
  **did not run**; §1's 86 and 119 are ledger rows at `db31113fa`, 313 commits
  behind this branch.
- Any fixture exercising the nested-under-a-binder shape — **did not run**.
- `cargo clippy --workspace --all-targets --all-features`,
  `cargo check --workspace --all-targets`,
  `cargo test -p axeyum-solver --features full --test …` (the five named
  suites), `cargo test -p axeyum-solver --lib --features full quant`,
  `scripts/tests/mutation_controls.py --check-anchors`,
  `scripts/check-config-registry-staleness.py`, `scripts/check-suite-gating.py`
  — **did not run**. This round changes no Rust and no registry row, so none of
  them has a subject in this diff; they are listed because the brief named them
  and "did not run" is the honest word, not "not applicable".
- `cargo fmt --all --check` — **did not run** (no Rust touched, and it is
  workspace-wide in a shared checkout).

## 6. Host note

The brief pinned `s5` as "GNU coreutils". **It is not.** Measured on `server5`
before any sweep was planned: `date +%3N` printed `811612316` — nine digits, so
the `%3N` width is ignored and the field is NANOseconds, the same uutils
behaviour already recorded for `s7`. Any `*_ms` column timed with `date` on
`s5` would have been wrong by 10^6. The lane's runner scripts were to use
`$EPOCHREALTIME`; recorded here so the next lane does not inherit the brief's
claim. `s5`'s physical pairing was confirmed rather than assumed:
`/sys/devices/system/cpu/cpu1/topology/thread_siblings_list` → `1,9` and
`cpu3` → `3,11`.

<!-- plan-section: landed-changes -->

| 2026-09-16 | `4d864e677` | Sized the four OFF quantifier levers and read nested activation on both references; **no lever moved, no Rust, no ADR** (round closed early). Corrected the standing `UFLIA` gap statement: cvc5 alone decides **142**, not 144 — 144 is the z3∪cvc5 union. Found `AXEYUM_MACRO_INLINE` carries **no `config_registry` row** (it is a `OnceLock` bool, not a `cap_lever!` int, so the coverage scanner cannot name it). Named the nested-activation gap at `qinst_egraph.rs:1948` (polarity forced `None` on entering a `forall` body) → `:2186` (discovery skips a context-less registration) → `:7294` (`inactive_dropped`), against z3 `qi_queue.cpp:336` and cvc5 `theory_quantifiers.cpp:182`, which both get it free by asserting the instance back. | `docs/plan/status/quant-compose.md`, `bench-results/quant-compose-20260916/` |
