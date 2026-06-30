# P2.7 · 08 — Evaluation, soundness gates, and ADRs

## Measurement protocol (no claim without a re-run)

- **Corpus:** the public QF_S / QF_SLIA / QF_SNIA divisions (NAS symlink +
  `corpus/public-curated/`), measured with `bench` `--backend solver`
  (`check_auto`) head-to-head vs the `z3` binary (and, where available, cvc5 /
  Z3-Noodler as references).
- **Metric:** decide-rate + PAR-2 per division, recorded in
  [bench-results/SCOREBOARD.md](../../../../bench-results/SCOREBOARD.md).
- **Rule:** *no decide-rate claim without re-running the scoreboard.* Each phase's
  exit is a **measured** delta.
- **64 GB cap:** runs via `scripts/mem-run.sh`.

## DISAGREE=0 (the soundness floor)

- `crates/axeyum-solver/tests/strings_differential_fuzz.rs` (vs Z3) gates every
  change — currently **DISAGREE=0 over 371 instances** on the bounded encoder;
  **expand it** to generate unbounded word equations, regex (incl. complement /
  bounded loops), and extended-function constraints as each phase lands.
- **Cautionary tale:** both cvc5 and Z3str4 shipped **soundness bugs flagged at
  SMT-COMP 2021**. String reasoning is subtle — the rule is *test harder, not
  faster*. Every derivation rule (`F-Split`, `F-Loop`, each reduction lemma, each
  derivative op) gets its own soundness-negative tests.

## Per-phase soundness obligations

| Phase | `sat` checkable by | `unsat` certified by | `unknown` triggers |
|---|---|---|---|
| A IR+combination | replay over new sort | **LIA/Parikh length abstraction** (re-checkable) | — |
| B word-equation core | normal-form assignment replay | derivation (premises→conflict) | budget (non-terminating fragment) |
| C regex derivatives | regex-semantics replay | derivative emptiness | unsupported regex (backrefs) |
| D extended functions | true-semantics replay | reduction lemma chain | — |
| E models + automata | **skeleton model replay** | cardinality / automata emptiness | budget across both arms |

**Non-negotiable invariants** (audited):
1. No phase returns `sat` from a non-replayable model.
2. Two arms (Phase E) never return *different* verdicts — first sound verdict wins.
3. Lazy/effort staging (Phase D) never changes a verdict, only timing.
4. Outside the decidable fragments / past budget ⇒ `unknown`, never a guess.

## Alphabet / Unicode decision (record in the Phase-A ADR)

- **SMT-LIB Unicode Strings**: code points `0x00000–0x2FFFF` (Planes 0–2; 196,608
  code points), **not** full Unicode, **not** UTF-16 surrogates.
- **Total order** on the alphabet — load-bearing for the cardinality model
  argument and for axeyum's determinism promise.
- `str.to_lower`/`str.to_upper` operate on the ASCII portion only.

## Proof / Lean-parity obligations (Track 3)

- Every new `unsat` route gets an independent checker or a
  [trust-ledger](../../track-3-proof-lean/P3.0-trust-ledger.md) entry.
- **Easiest first checkable evidence:** UNSAT via the **LIA/Parikh length
  abstraction** (Phase A) — a self-contained, replay-checkable certificate.
- **Mechanizable lemmas to align with:** *Finiteness of Symbolic Derivatives in
  Lean* (ITP 2025), *Certified Symbolic Finite Transducers* (arXiv:2504.07203),
  and the OSTRICH regularity-preserving pre-image lemmas — the certificates a
  trusted checker re-derives.

## ADRs to write (in order)

1. **ADR — first-class `Seq`/`String` sort + `axeyum-strings` crate boundary +
   Unicode alphabet/total-order.** *(Phase A)*
2. **ADR — String+LIA Nelson-Oppen combination** over `len` (politeness argument),
   Parikh over-approximation. *(Phase A)*
3. **ADR — word-equation core**: normalization invariant, arrangement rules,
   `F-Loop` termination, budget→`unknown`. *(Phase B)*
4. **ADR — symbolic-derivative regex** + native bounded loops + pure-Rust automata
   substrate choice (`regex-automata`/`aws-smt-strings`/`smt-str`). *(Phase C)*
5. **ADR — extended-function lazy-reduction strategy** + context-dependent
   simplification. *(Phase D)*
6. **ADR — model construction (bucketing+cardinality)** + the automata/stabilization
   fallback arm + portfolio dispatch soundness. *(Phase E)*

## Definition of done for P2.7

- First-class `Seq`/`String` sort; `str.len` unsat decides; String+LIA combination
  closed.
- Unbounded word equations / regex / extended functions decided over the decidable
  fragments, `unknown`-safe outside, with **measured** decide-rate on public
  QF_S/QF_SLIA approaching cvc5/Z3-Noodler.
- Unbounded SAT models constructed + replay-checked; automata fallback arm landed.
- Every `unsat` route carries a checker / trust-ledger entry; Parikh-abstraction
  certificates re-checkable.
- All six ADRs merged; foundational DAG + research-questions updated; STATUS.md
  reflects the measured pulse.
- **DISAGREE=0** throughout; the bounded encoder retained as a sound pre-check.
