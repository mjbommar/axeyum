# SMT capability gap analysis — axeyum vs Z3, cvc5, Bitwuzla (2026-08-21)

Status: **current capability audit.** Supersedes
[`gap-analysis-z3-cvc5-2026-07-07.md`](gap-analysis-z3-cvc5-2026-07-07.md) as
the capability map (which itself superseded
[`gap-analysis-z3-cvc5-2026-06-22.md`](gap-analysis-z3-cvc5-2026-06-22.md)).
It does **not** supersede
[`gap-analysis-z3-lean-2026-07-21.md`](gap-analysis-z3-lean-2026-07-21.md),
which is the *evidence* map — proof denominators, dominance audits, trust
holes — and remains current for that.

Scope: what axeyum can and cannot decide, prove, and emit, measured against the
three reference solvers it is benchmarked on. **Bitwuzla is included for the
first time**; every prior analysis in this series was "Z3/cvc5" while Bitwuzla
has been our QF_BV and QF_FP reference for months.

Interval since the last capability audit: **45 days.**

---

## 0. Method, and how to read a claim here

Three evidence classes, marked per claim:

- **[measured]** — a command was run on this host on 2026-08-21 and the output
  is what is quoted. Solver probes ran the shipped front door
  (`target/release/examples/smtcomp_cli`, the real `solve_smtlib`) against
  `/usr/bin/z3` 4.13.3.
- **[src]** — read out of source at a pinned tag, with file:line.
- **[artifact]** — read from a committed measurement artifact, with its own
  as-of date, because an artifact's commit date is **not** its measurement date.

Nothing here is quoted from a README, a doc comment, or a prior version of this
document without re-checking. That is not ceremony: this audit found a doc
comment on `literal_chars` asserting "1–5 hex digits in braces" over code that
enforced no such thing, and the divergence was a wrong verdict. It also found
four separate committed artifacts publishing numbers that were two months stale
in our own disfavour.

**The single most important reading rule.** "Solver X has feature Y" is three
different claims — *it exists*, *it is good*, and *the authors vouch for it* —
and cvc5 is the only one of the three that publishes the third
(`src/smt/set_defaults.cpp` names the theories it calls expert/experimental).
Where that distinction is available it is made below.

---

## 1. Scorecard: what the 2026-07-07 analysis said, and what actually happened

The prior audit ranked seven gaps. Reading them back is the most useful thing in
this document, because two were wrong at the time and one has been closed
without anyone noticing.

| 07-07 gap | Then | Now (2026-08-21) | Verdict |
|---|---|---|---|
| **1. Performance — "the defining chasm"** | "Z3 decides all 113 public p4dfa QF_BV in ≤1s; axeyum decides 8/113 at 20s" | Axeyum **8/113**, Z3 crate **8/113**, on partially different sets, 0 disagreements | **The premise was false.** ADR-0059 corrected it: both solvers decide 8–9. Our CNF is *smaller* than Z3's; p4dfa is search-bound, so the lever is the SAT core, not the encoding |
| **2. Quantifier sat-direction — "the biggest categorical hole"** | "refutation-only outside finite domains, which is why quantified LIA/UF rows sit at 0%" | Quantified **LIA 12/12, UF 2/5, BV 54/54** [measured] | **Closed, and nobody noticed.** E-matching with congruence closure, MBQI, finite model finding and Fourier–Motzkin QE all exist. The 0% figures were stale artifacts (§8) |
| **3. CDCL(T) migration** | driver built, arrays/BV/datatypes not ported | `cdclt.rs`, `dpll_t.rs`, `ufbv_online.rs`, `euf_egraph.rs` present and reached | Partially closed; not re-audited here |
| **4. Strings residual — "largest by count"** | a machinery tail | QF_SLIA **191/200 = 99.0% of cvc5** [artifact 08-02] | **Closed on the competition slice.** But the `unsat` half is much weaker than that number suggests (§4.4) |
| **5. NRA/NIA depth — "the genuine 15-year catch-up"** | deliberately last | QF_NIA **34/200 = 38.2%**, still the weakest row | Open, as planned |
| **6. Genuinely absent theories** | sep. logic, sets/relations, bags, transcendentals, SyGuS | sets and finite fields now exist (bounded); **transcendentals and SyGuS still absent** | Partially closed |
| **7. Dominance denominator** | 12 of 35 rows unaudited; 23 rows 100%-dominant | **all 35 audited**; 20 rows 100%-dominant | Denominator closed; the row count *fell*, and two of the four losses were the criterion tightening, not capability |

**The lesson that generalises.** Two of the seven gaps were mis-stated in a way
that made us look worse than we were, and both survived because the artifact
that would have corrected them could not fail (§8). A gap analysis is only as
good as the instruments under it, so §8 is not an appendix here.

---

## 2. Head-to-head against the reference solvers

`bench-results/PARITY.md` is the honest instrument: an external benchmark list
fixed by sha256 *before* the run, the same machine, the same budget, and a
`DISAGREEMENTS > 0` rule that voids an entry regardless of its ratio.

Latest run per logic [artifact]:

| logic | measured | axeyum | reference | ratio | disagreements | reference solver |
|---|---|---:|---:|---:|---:|---|
| QF_SLIA | 2026-08-02 | 191/200 | 193/200 | **99.0%** | 0 | cvc5 1.3.4 |
| QF_BV | 2026-08-17 | 187/200 | 194/200 | **96.4%** | 0 | Bitwuzla 0.9.1 |
| UF | 2026-08-03 | 85/200 | 91/200 | **93.4%** | 0 | cvc5 1.3.4 |
| QF_LIA | 2026-08-06 | 117/200 | 140/200 | 83.6% | 0 | cvc5 1.3.4 |
| QF_RDL | 2026-08-06 | 105/200 | 155/200 | 67.7% | 0 | cvc5 1.3.4 |
| QF_LRA | 2026-08-06 | 86/200 | 146/200 | 58.9% | 0 | cvc5 1.3.4 |
| QF_IDL | 2026-08-06 | 68/200 | 124/200 | 54.8% | 0 | cvc5 1.3.4 |
| QF_UFLIA | 2026-08-06 | 94/200 | 180/200 | 52.2% | 0 | cvc5 1.3.4 |
| QF_NIA | 2026-08-06 | 34/200 | 89/200 | **38.2%** | 0 | cvc5 1.3.4 |

**967 / 1312 = 73.7%** of what the reference solved, across nine divisions.

The shape matters more than the total. **Bit-vectors and strings are at
parity** (96%, 99%). The deficit is concentrated in **linear arithmetic** —
LRA, IDL, RDL and UFLIA all cluster in 52–68% — and then nonlinear integer
arithmetic at 38%.

### 2.1 The trajectory, and where it stops

The ledger is append-only, so it shows movement, not just level:

```
UF        07-31: 32 → 44 → 54 → 78 → 81 → 85    (of 91)   2.7x in four days
QF_RDL    08-03: 10 → 105                       (of 155)  10x in one day
QF_BV     07-31: 164 → 175 → 184 → 187          (of 194)
QF_SLIA   07-31: 166 → 175 → 187 → 191          (of 193)
QF_NIA    08-03: 21 → 34                        (of 89)
QF_LIA    08-02: 111 → 118 → 117                (of 140)
QF_IDL    08-03: 51 → 66 → 68                   (of 124)
QF_LRA    08-04: 86 → 86                        (of 146)  flat
QF_UFLIA  08-03: 93 → 94                        (of 180)  flat
```

Then it stops. **The last competition measurement of any logic except QF_BV was
2026-08-06 — fifteen days ago** — during the steepest improvement in the
project's history.

The cause is structural, not neglect: **`scripts/parity-run.sh` is invoked by no
gate** — not `just check`, not `scripts/check.sh`, not CI [measured]. The number
this repository's own ledger calls "the only headline" is produced by a script
nothing runs.

### 2.2 Our oracle is 22 months stale

Z3 **4.13.3** (2024-10-11) is our pinned oracle; current Z3 is **5.1.0**
(2026-08-16). Since our pin Z3 has added SLS-modulo-theories, a real
`FiniteSets` theory, a monadic regex solver on by default, shared-search-tree
threading — plus soundness fixes to `intblast`, `str.at`-in-regex and
`elim-term-ite` that our pin does not have.

This cuts both ways and should be said plainly: our differential fuzzing is
against a Z3 that has known-fixed soundness bugs, and our head-to-head figures
flatter us against a two-major-version-old opponent. cvc5 1.3.4 and Bitwuzla
0.9.1 are both current.

---

## 3. The broad regression corpus, against Z3

A different instrument, answering a different question: breadth rather than
competitive depth. 992 files, 24 logics, curated from cvc5 and Bitwuzla
regression suites [artifact]:

- **762 decided (76.8%)**, 674 compared against Z3 4.13.3, **0 disagreements**
- strongest: BV 100%, QF_FP 100%, QF_AX 100%, QF_DT 100%, QF_AUFBV 93%,
  QF_ABV 88%
- weakest: QF_SLIA 50%, QF_UF 54%, QF_SEQ 67%, QF_S 69%

Re-run at HEAD on 2026-08-21, **34 of 35 rows are unchanged** and the one that
moved (+3) moved for an instrument reason, not a capability one. So these
figures are old files but current facts — which is *not* true of the quantified
rows (§8).

---

## 4. Theory and operator coverage

### 4.1 The matrix

`✓` present, `~` present but bounded or partial, `✗` absent. For the reference
solvers, **(exp)** marks a theory the authors themselves label expert or
experimental.

| Theory | axeyum | Z3 4.13.3 | cvc5 1.3.4 | Bitwuzla 0.9.1 |
|---|---|---|---|---|
| Core | ✓ | ✓ | ✓ | ✓ |
| Ints / Reals / mixed | ✓ | ✓ | ✓ | ✗ |
| Bit-vectors | ✓ full operator set, widths to 65536 | ✓ | ✓ | ✓ specialty |
| Arrays | ~ **nested arrays structurally rejected** | ✓ | ✓ (exp for const arrays) | ✓ |
| Floating point | ✓ all 30 ops, all 5 rounding modes incl. symbolic, generic `(_ FloatingPoint eb sb)` | ~ no `fpa2bv` path for `ebits > sbits` arithmetic | ~ **(exp)**, Float32/64 only unless `--fp-exp` | ✓ specialty, non-standard formats need a **build** flag |
| Strings / regex | ~ `sat` strong, `unsat` weak | ✓ | ✓ headline strength | ✗ |
| Sequences | ~ 8-element / 128-bit bound | ✓ | ✓ | ✗ |
| Datatypes | ~ no parametric datatypes | ✓ | ✓ (exp for codatatypes) | ✗ |
| UF | ✓ | ✓ | ✓ (exp for higher-order, cardinality) | ✓ |
| Sets | ~ 128-bit universe | ~ sugar over `(Array T Bool)`; real theory only in 5.0.0 | ✓ **(exp)** | ✗ |
| Bags / Relations / Separation logic | ✗ | ✗ | ✓ **(exp)** | ✗ |
| Finite fields | ~ 16-bit moduli, no `ff.div` | ✗ | ✓ **(exp)** | ✗ |
| **Transcendentals** | **✗** | ~ parse but return `unknown` | ✓ `NRAT` | ✗ |

Two readings worth taking from this. First, **most of what cvc5 has and we do
not, cvc5 itself labels experimental** — which changes "cvc5 has nine theories
we lack" into something much narrower. Second, our finite-field and set support
is real but bounded far below usable scale: 16-bit moduli rules out every
cryptographic field.

### 4.2 Where axeyum is genuinely competitive

- **QF_BV** — the full SMT-LIB operator set plus `bvred*` and all overflow
  predicates, widths to 65536, with DRAT and Alethe proofs. Missing only
  `sbv_to_int` and the `nat2bv` spelling.
- **QF_FP** — all 30 operators, all five `to_fp` variants, all five rounding
  modes *including symbolic ones*, `Float16/32/64/128` and generic formats.
  This is **broader than either specialist reference from a shipped binary**:
  cvc5 needs `--fp-exp` for non-standard formats and Bitwuzla needs a rebuild.
- **Interpolation and reachability** — BMC, k-induction, PDR/IC3, IMC over BV,
  LIA and LRA. Z3 has the analogue (Spacer); Bitwuzla gained interpolation only
  in 0.9.0; cvc5 has interpolants but no CHC engine.

### 4.3 The transcendental hole is the one clean capability zero

`sin`, `cos`, `tan`, `exp`, `sqrt`, `arcsin`, `arctan`, `real.pi` are all parse
errors [measured, probed individually]. On a sampled `QF_UFNRAT` slice axeyum
scored **0 of 4**, and it was the only slice in the sample that scored zero for
a *capability* reason rather than a budget reason.

### 4.4 Strings: the headline number hides the weak half

QF_SLIA at 99% of cvc5 is a decide-rate. The `unsat` direction is much weaker:
`StringGate` refuses to certify most bounded refutations, so QF_S/QF_SLIA
`unsat` coverage is far below what the encoder suggests, and the strings row in
the capability ledger is marked `Experimental`. A 99% headline and an
`Experimental` ledger row describe the same code.

---

## 5. Quantifiers — the correction

**The prior audit's "biggest categorical hole" is not a hole.** Measured today
through the shipped front door:

| corpus | committed artifact says | measured 2026-08-21 |
|---|---|---|
| quantified LIA (cvc5 regressions) | **0/12** | **12/12** |
| quantified UF (cvc5 regressions) | **0/5** | **2/5** |
| quantified BV (cvc5 regressions) | "~70%" | **54/54** |

What exists: a real E-matching loop with congruence closure and Z3-style flood
control (`qinst_egraph.rs`), MBQI, finite model finding, Skolemization, and
Fourier–Motzkin quantifier elimination. On the committed corpus the general
instantiation loop closes only ~8% of decisions — narrow recognizers and finite
expansion close the rest — so both halves of the story are true: the machinery
is real, and it is not yet carrying most of the weight.

The remaining UF failures are specifically **finite-model-finding** benchmarks,
which is a technique gap, not general UF weakness.

**The real quantifier gap vs Z3 is triggers.** `:pattern` is parsed and
*dropped* (`parse.rs:7374`), and `:weight` does not exist. Any Z3 workload whose
quantifier performance rests on hand-written triggers has no path here at all.

---

## 6. Beyond satisfiability

### 6.1 What axeyum has that the prior audits did not credit

Optimization (OMT, MaxSAT, Pareto), interpolation (9 modules, 7 theories),
abduction, quantifier elimination (Fourier–Motzkin + Loos–Weispfenning and
Cooper/Omega model-based projection), and a multi-predicate CHC/Horn solver all
exist. **SyGuS genuinely does not.**

### 6.2 The evidence moat — real, and narrower than we say

This is the project's identity claim, so it deserves the harshest reading.

| | axeyum | Z3 4.13.3 | cvc5 1.3.4 | Bitwuzla 0.9.1 |
|---|---|---|---|---|
| Proof/certificate output | ✓ DRAT, Alethe, Lean kernel terms, per-theory certificates | ~ own format; guide admits some steps "require checking using general purpose SMT solving" | ✓ CPC / Alethe / LFSC / DOT | **✗ none** |
| Independent checker | ✓ `drat-trim` verified with a negative control [measured]; Lean 4.30 kernel | ✗ | ✓ **Ethos** (CPC), **Carcara** (Alethe, in Rust) | — |

**So the moat is real against Z3 and Bitwuzla, and it is not a moat against
cvc5.** cvc5 ships three proof formats and two independent checkers, one of them
a Rust Alethe checker. Any claim that axeyum is uniquely checkable is false as
stated; the defensible claim is *checkable into a foundational kernel with a
measured trusted base*, which is a different and narrower thing.

Two measured numbers that should temper the claim further:

- **CORRECTED 2026-08-21 — 44 of 281 certified `unsat` (15.7%) carry an
  artifact an external checker can read** (30 DRAT + 14 Alethe). This document
  first published "11 of 129 (8.5%)", which was counted from `kind_label`
  strings — and labels are not artifacts.
  `BoundedIntBlastCertificate` had been carrying a full DRAT refutation of its
  bit-blasted CNF in `bv_proof` all along, under the label
  `unsat-bounded-int-blast`; so do `ArithDpllRefutation` and three quantified-BV
  certificates. The metric undercounted the thing it existed to measure, in the
  direction that made the project look worse.
  `Evidence::portable_artifact()` now decides it from the certificate rather than
  from its name, and `every_proof_carrying_variant_is_listed_as_portable` reads
  the source and fails when a certificate gains an `UnsatProof` without an arm —
  because the wildcard in that function undercounts by construction, which is the
  same defect one level down. Still: **84% re-validates only by calling back into
  axeyum's own Rust**, and that is the real number to move.
- **~30 of 34 structural evidence checkers re-run the producer and compare for
  equality** — `producer(arena, assertions).is_some_and(|fresh| fresh == *cert)`.
  That is a determinism check, not a soundness check: if the recognizer is
  wrong, the checker is wrong identically. This covers `unsat-array-axiom`, the
  single highest-volume family (85 of 765 recorded instances).

Against that, what genuinely holds: 269/326 baseline `unsat` satisfy the full
conjunction (certified + independently checked + trust-hole-free +
Lean-reconstructed), 78 crosscheck families are accepted by real Lean 4.30, and
the trusted base is **30 assumptions, all in one legacy axiomatized package no
shipped route reaches** — every constructed carrier measures 0.

### 6.3 Interfaces — the weakest axis

A consumer coming from `z3 file.smt2` hits these immediately [measured]:

1. The text front door is **single-query**: two `check-sat`s → `unknown`.
   `solve_smtlib_incremental` exists; nothing in the shipped CLI reaches it.
2. **`set-option` is inert.** `:produce-models`, `:produce-proofs`,
   `:produce-unsat-cores`, `:timeout` all silently do nothing.
3. **`get-model` / `get-value` / `get-unsat-core` / `get-proof` are CLI no-ops**
   with Rust-API-only counterparts.
4. **`set-logic` is never read** — `(set-logic NONSENSE_XYZ)` and no `set-logic`
   at all both decide normally. There is no conformance checking in either
   direction.
5. `define-fun-rec`, `define-funs-rec`, `reset`, `declare-sort` with arity ≥ 1,
   and parametric datatypes do not exist.
6. Nothing is incremental where a user can drive it: the warm engine is good
   (5.79× fewer clauses measured) but `auto.rs` never reaches it.

---

## 7. Defects found while measuring

An audit that finds nothing has usually measured nothing. This one found five.

**P0, fixed today — a wrong `sat` AND a wrong `unsat`.** SMT-LIB makes `\u{d…}`
an escape only for 1–5 hex digits. `parse.rs` enforced that; `regex.rs` and
`regex_membership.rs` did not. So `"\u{000062}"` was **ten characters** to the
string route and **one character `b`** to the regex route, inside one solver:

```
(str.in_re x (str.to_re "\u{000062}")) ∧ (= x "b")           axeyum sat,   z3 unsat
(str.in_re x (str.to_re "\u{000062}")) ∧ (= (str.len x) 10)  axeyum unsat, z3 sat
```

This was the **second** P0 on that exact boundary, the first being the same
divergence from the opposite direction. Fixed by delegation to the one canonical
decoder rather than a third copy of the rule. This also removed a caught panic
in the regex decoder (stderr noise, an SMT-COMP §7.1.2 violation) and a
code-points-vs-UTF-8-bytes disagreement.

**Why no gate caught it, and it is already written in CLAUDE.md:** string fuzz
generators must cover the full literal grammar including `\u{…}` escapes, and
every generator omitted them — which is exactly how the *first* instance of this
class hid for weeks. A generator that cannot emit the shape is blind on the one
axis where the grammar has a rule.

**Two of the three fixed 2026-08-21, after this audit was written:**

- ~~`TermArena::bv_nego` computes `1u128 << (w - 1)`~~ — fixed, and it was
  **worse than recorded here**. Measured with overflow checks off (release
  semantics), the shipped `SatBvBackend` returned **`sat`** for
  `(bvnego x) ∧ (x = 1)` at 129 bits, which is unsatisfiable: a wrong `sat`
  through the front door, not merely a wrong term. The reachability question
  this section marked UNVERIFIED now has an answer: **no committed corpus file
  reaches it** — `bvnego` occurs in **0 of 1430** tracked `.smt2` files
  (positive control, same command: `bvadd` in 106). It is reachable only from
  the parser on user input, which is why no sweep could have found it.
- ~~`SolverConfig::memory_limit_mb` is set but never read~~ — the field now
  binds on the pure-Rust path (`crates/axeyum-solver/src/memory_budget.rs`): a
  portable pre-allocation clause ceiling at a measured 384 B/clause, plus a
  `/proc` probe at three BV phase boundaries and the two front doors. A
  *faithful* bound still needs a `#[global_allocator]` hook, which is
  ADR-sized and is now an open research question rather than an unspoken gap.
  The default path costs nothing measurable; a configured limit costs ~32 µs
  per check. **The gap that remains** is allocation between two probes, which
  is the 125 GB shape exactly.

**Open, not fixed here:**

- `explain_corpus` diverges from the front door in both directions, and prints
  `unsat-UNCONFIRMED`. Do not use its verdicts for anything quantified or
  string-shaped.

---

## 8. Why our own numbers were wrong — the instrument failures

Three of this document's corrections exist because a measurement instrument
could not fail. This is the part most likely to repeat.

1. **An audit that audits only what the baseline decided.**
   `lia-cvc5-regress-clean-quantified-dominance-audit.json`, re-run 2026-08-21,
   reports `"instances": []` and `audited_decided: 0`. It audits rows the
   *baseline* decided, so a zero baseline propagates a zero forward **forever**.
   That is why "quantified LIA 0/12" survived roughly three months past being
   true, and why the 07-07 audit named it the biggest categorical hole.
2. **Stale baselines quoted as current.** The quantified rows were last measured
   2026-06-24. `SCOREBOARD.md`, `DOMINANCE.md`, the quantified `UF/README.md`
   and the 07-07 gap analysis all still assert the old zeros.
3. **A headline nobody re-runs.** `parity-run.sh` is gated by nothing, so the
   competitive numbers stopped on 2026-08-06 and no gate went red.

The common shape: **a number that can only move when a human chooses to move
it, in a repository where humans move on.** The fix for each is the same one
this repo already applies elsewhere — make the artifact carry its own as-of
date, and make a gate fail when the date goes stale.

---

## 9. Ranked gaps

Ordered by *measured* cost, not by how large the hole feels.

| # | Gap | Evidence | Nature |
|---|---|---|---|
| 1 | **Linear arithmetic depth** — LRA 58.9%, IDL 54.8%, RDL 67.7%, UFLIA 52.2% | §2; **diagnosed 2026-08-21**: [linear-arithmetic-deficit-diagnosis](../research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md) | The largest aggregate deficit. The "one shared cause" clause is **refuted**: the 278 misses split into **three** causes — `dl-online` search timeout (QF_IDL + QF_RDL, the one genuinely shared pair), the LRA route's 1,024-atom refusal plus its slow CDCL(T) (QF_LRA + QF_RDL's tail), and the lazy UF/arith CEGAR (QF_UFLIA, 82/82) — plus 26 QF_UFLIA files lost at the **parser** to `Int` literals beyond `i128`. Highest-leverage fix named and A/B-measured: minimise wide LIA theory cores instead of declining at 5% budget use — **+17 QF_UFLIA files, 0 regressions, 0 disagreements** (94/180 = 52.2% would project to 111/180 = 61.7%; not a parity run). The obvious fix (drop the LRA atom cap's terminality) was built and **refuted**: 0 new decides, 54 of 71 turn into memory aborts |
| 2 | **Re-measure, then gate the measurement** | §2.1, §8 | 15 days dark on the headline; cheap, and everything else is priced off it |
| 3 | **Consumer interface** — single-query CLI, inert `set-option`, no-op `get-*` | §6.3 | Nothing here is research; it is the difference between a library and a solver a stranger can run |
| 4 | **QF_NIA at 38.2%** | §2 | The genuine multi-year catch-up; still correctly last among decision work |
| 5 | **Externally-portable evidence — 15.7%, not the 8.5% first published** | §6.2 | The metric was counted from labels and undercounted by 1.75x; it is now decided from the certificate and guarded by a test that reads the source. The remaining 84% re-validates only inside axeyum, and that is the real target |
| 6 | **~30 checkers that re-run the producer** | §6.2 | A determinism check sold as a soundness check, over the highest-volume family |
| 7 | **User triggers (`:pattern`, `:weight`)** | §5 | The one quantifier gap that is real vs Z3, now that the sat-direction is closed |
| 8 | **Memory bound is inert** | §7 | Operational, and this box has already been OOM-killed once |
| 9 | Transcendentals; nested arrays; parametric datatypes | §4.1, §4.3 | Clean capability zeros, each small and each blocking a whole slice |
| 10 | **CAV-2024 bit-blasting abstraction** | — | Bitwuzla has it on by default since 0.8.0, cvc5 is adding it, in a division where the top three sit within 32 benchmarks of each other |

Deliberately **not** on this list: new theory columns. Most of what cvc5 has and
we lack, cvc5 labels experimental (§4.1). The breadth backlog stays counted, not
built.

---

## 9.1 What the queue has already changed about this document

This file is a specification for the work below it, so where that work refutes
or discharges a row, it is recorded here and not only in the note that found it.

**Refuted.** Row 1's "four divisions share one cause" was a hypothesis and it is
false — see the row itself for the three-cause split. The part that most changes
the framing: the largest single block of losses in the *worst* division is not a
search problem. 48 QF_UFLIA files return `unknown` after a median **1.3 s of a
24 s budget** with `core_src_minimized=0`, because the cores too wide to
minimise are exactly the cores whose width then exhausts retention. A deficit
that read as "we are slower" is substantially "we stop early". And 26 files —
13% of that division — never reach the solver at all, rejected at the parser for
`Int` literals beyond `i128`. No row in §9 named that.

**Discharged.**

- **§8, the audit that could not fail.** `audit_dominance` audited only
  baseline-*decided* instances, so a zero baseline propagated forward forever.
  It now re-probes the undecided set and reports `newly_decided`. On the row that
  motivated this: `NEWLY DECIDED 11/12 the baseline recorded as undecided`, where
  the artifact previously held `"instances": []`.
- **Gap #6.** The array-axiom family — 30.2% of all certified `unsat` — no longer
  rests on re-running its producer and comparing for equality. Two stages decide
  the certificate's own claim, each killed by exactly one adversarial fixture
  over a **satisfiable** query. Two residual shapes (`ReadCongruence`, and the
  BTOR path where the assertion only *entails* the disequality) are named in the
  code rather than implied away.
- **Gap #3.** `examples/axeyum_cli.rs` answers one verdict per `check-sat`,
  matching z3 on `push`/`pop` and on `check-sat-assuming` non-retention. The
  engine could always do this; nothing user-facing reached it.
- **Gap #2's gate**, ahead of its measurement:
  `scripts/check-parity-freshness.py` fails when a division's ledger entry ages
  past 14 days, wired into both gate sets. It reads `FAIL` today, which is the
  honest state.

- **Gap #7, for `:pattern`.** A hand-written trigger is threaded parse → IR →
  the E-matching loop and now *replaces* auto-selection; alternatives are
  unioned and multi-patterns joined, and anything the matcher cannot fire is
  declined whole rather than silently ignored (ADR-0537). `:weight` is
  explicitly refused, not forgotten: it would change the flood-control cost
  function, the one lever measured to decide files in both directions.

  **The measured delta on our own corpora is zero, and that is a fact about the
  corpora.** 0 of 1430 tracked `.smt2` files contain `:pattern`; 0 contain
  `:weight` (positive control, same command: `assert` in 1419, `forall` in 82).
  92 quantified files, before and after: **0 verdict differences**. §5's claim
  that such a workload "has no path here at all" was right, and closing it
  cannot be priced from anything we currently measure.

  One thing worth not assuming, because the obvious check says the opposite of
  the truth: obeying a *useless* trigger did not cost the refutation through the
  front door. z3 4.13.3 with `smt.mbqi=false` goes `unsat` → `unknown` on the
  file that motivated this; we stay `unsat`, because term invention seeds ground
  instances of the trigger itself and reaches the excluded witness anyway. So a
  verdict is a blunt instrument for "was the annotation obeyed" — the direct
  observable is the proposed instance set, and that is what changed.

**Found while discharging, and not in the original document.** The parity ledger
holds **nine** divisions, not the eleven `PROJECT-STATE.md` claimed, and has
never held a QF_ABV entry despite a committed `parity-lists/QF_ABV.txt` — a list
that was never run.

## 10. What this document does not establish

- **The competition figures are 15 days old** (QF_BV 4 days). Nothing since
  should have moved them much — this session's work was evidence and proofs, not
  decision procedures — but that is an argument, not a measurement.
- **Every claim about cvc5 and Bitwuzla is source- or doc-derived**, not
  measured: neither binary is installed on this host. Only Z3 4.13.3 was probed
  directly.
- **Our Z3 is 22 months old** (§2.2), so both the head-to-head and the
  differential fuzzing are against a solver two major versions behind.
- **`bv_nego` reachability is unverified** (§7), and so is the WASM build and
  the Carcara Alethe cross-check — the checker binary is absent from
  `references/`, so that test **skips and passes** here, which is the inert-gate
  shape this repository keeps rediscovering.
- No performance profiling was done beyond decide-rates and PAR-2. Where we
  decide *and* the reference decides, who is faster and by how much is not
  measured here.

---

## Provenance

Measured 2026-08-21 at `fc6c82f52`, on the 16-thread i5-12600K dev host, with
`z3` 4.13.3 at `/usr/bin/z3` and Lean 4.30.0 (`d024af09`) via `~/.elan`. The
underlying censuses — a 251-probe SMT surface census, a reference-solver source
and SMT-COMP-2025 review, and a beyond-satisfiability census — were run as three
parallel audits and are summarised, not reproduced, here.
