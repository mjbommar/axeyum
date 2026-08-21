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

### 4.0 Measured, now that the binaries were found

§10 originally recorded every cvc5 and Bitwuzla claim as source-derived because
a `command -v` said the binaries were absent. They are not (see §10). The
load-bearing cells were re-checked **by running them**, 2026-08-21, at the
versions the parity ledger names:

| claim | was | measured |
|---|---|---|
| Bitwuzla rejects `Int` | source | `[error] unsupported logic 'QF_LIA'` — a parser error, not a weakness |
| Bitwuzla rejects strings | source | `[error] unsupported logic 'QF_S'` |
| Bitwuzla decides BV | source | `sat` |
| cvc5 FP is Float32/64 only without `--fp-exp` | source | `(_ FloatingPoint 5 3)` → `error "…is not supported, only Flo…"`; `Float32` → `sat` |
| cvc5 has no optimization | source | `(maximize x)` → `Parse Error` |
| **cvc5 emits a checkable Alethe proof** | source | **`unsat` followed by real Alethe steps** — `(assume a0 (! (> x 5) :named @p_1))` |
| **Bitwuzla emits no proof** | source | **`unsupported command 'get-proof'`** |
| Bitwuzla gained interpolation in 0.9.0 | source | `--produce-interpolants`, `--interpolants-algo mcmillan` present |

The two in bold are the ones that decide §6.2's framing, and they now rest on
output I read rather than on source I inferred from: **our checkable-evidence
moat is real against Bitwuzla, which cannot emit a proof at all, and is not a
moat against cvc5, which emits Alethe that Carcara reads.**

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

**And that 269 is roughly half attestation, which this document did not say.**
Measured 2026-08-21 by classifying each instance's `lean_fragment` against
`ProofFragment::lean_module_content`:

| of the 269 Lean-reconstructed `unsat` | count | share |
|---|---:|---:|
| carry **theory reasoning** — a term built from the query | **142** | 52.8% |
| **structural attestation** only | **127** | 47.2% |

A structural attestation is a 21-line shim — `axiom P`, `axiom Not P`,
`theorem _ : False := …` — that kernel-checks, is `sorry`-free, and contains
**none** of the reasoning. `reconstruct.rs` is explicit about this ("the checking
that matters happened in Rust"), 29 fragments funnel through one shared emitter
whose output does not depend on the query beyond generated constant names, every
such module carries `STRUCTURAL_ATTESTATION_MARKER`, and
`prove_unsat_to_lean_theory_module` exists precisely to decline them. None of
that is hidden. What was missing is that the **dominance metric does not make
the distinction**, so "269/326 Lean-reconstructed" reads as a much stronger claim
than it is — for 127 of them, Lean confirmed a tautology.

> **Caveat on the counts below, added the same day.** They were computed by
> classifying each instance's `lean_fragment` against
> `ProofFragment::lean_module_content()` — a **table**. The string and regex
> routes are not `ProofFragment` variants, so 13 instances (11 `RegexEmptiness`,
> 2 `StringLength`) fell through as unclassified, and `lean_theory_unsat` read
> 129 where the reasoning half is 142. The undercount is on the **reasoning**
> side, i.e. in the direction that makes the claim look weaker — which is why
> being suspicious of flattering numbers would not have caught it.
>
> `ab11d6fc5` replaces the table lookup with a read of
> `STRUCTURAL_ATTESTATION_MARKER` **out of the emitted module**: only the shared
> structural emitter writes that marker, so the class is now a property of the
> artifact rather than an assumption about the route. That is the same rule that
> made `portable_artifact()` correct, applied in one place and not the other.
>
> The **shape** below is not in doubt — QF_ABV and the string logics near 100%,
> seven logics at exactly 0 — but treat the exact counts as superseded by the
> in-flight refresh, which carries a positive control (QF_S must read
> `11 reason and 0 attest`).

**And "roughly half" is misleading in both directions, because the split is
almost bimodal by logic.** Per-theory, over the same 269:

| logic | reasoning | attestation | reasoning share |
|---|---:|---:|---:|
| QF_S | 11 | 0 | **100%** |
| QF_SLIA | 2 | 0 | **100%** |
| QF_ABV | 81 | 4 | **95%** |
| QF_NRA | 15 | 10 | 60% |
| QF_AUFBV | 11 | 9 | 55% |
| BV | 8 | 11 | 42% |
| QF_UF | 6 | 27 | 18% |
| **QF_NIA, QF_FP, QF_UFLIA, QF_FF, QF_UFFF, QF_DT, QF_BVFP** | **0** | 52 | **0%** |
| *total* | *142* | *127* | *53%* |

**Seven logics have zero reasoning modules.** For QF_NIA (0 of 20), QF_FP (0 of
6) and QF_UFLIA (0 of 6), "Lean-reconstructed" says nothing whatever about the
query — every module is the 21-line shim. Meanwhile QF_ABV is 95% genuine and
the two string logics are 100%.

So the aggregate understates the strong theories and overstates the weak ones by
the maximum possible amount, and a reader taking "about half" to any particular
division will be wrong about it. This table is the number to quote; 53% is an
average over a distribution with almost nothing in the middle.

The largest attestation families are `BoundedIntBlast` (20), `TermLevelEnum`
(12), `BvUfLocal` (10) and `NraEvenPower` (10). Note `BoundedIntBlast` appears
here *and* in the DRAT column above: its Lean module attests, while its
certificate carries a genuinely external DRAT refutation. The two axes are
independent, and neither alone describes an instance.

`scripts/check-lean-gate.sh` already reports and floors this split for the
crosscheck families (38 reasoning against 40 attestation). The dominance
denominator should do the same, and until it does, **142 — not 269 — is the
number to quote for "propositions Lean proved about the query."**

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

0. **The frozen zero was not confined to the quantified rows, and that is worse
   than it was reported.** The fix landed for a row that decided *nothing*
   (quantified LIA, `instances: []`), which framed it as a corner case. Running
   the fixed tool against **QF_ABV** — a row at 169/169, which nobody suspected
   of anything — prints:

   ```
   NEWLY DECIDED 22/24 the baseline recorded as undecided (the baseline is stale)
   ```

   Twenty-two instances in a healthy row that the audit had never re-run,
   because the baseline had recorded them undecided and that verdict was never
   revisited. The committed 35 are therefore understating by an unknown amount
   in an unknown number of rows, and every headline in this document that rests
   on them (269, 281, 326) is a floor rather than a measurement. A full refresh
   is queued; it needs a quiet box, because a contended sweep would replace a
   known-low number with an unreliable one.

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
| 4 | **QF_NIA at 38.2%** | §2; **diagnosed 2026-08-21**: [nia-deficit-diagnosis](../research/05-algorithms/nia-deficit-diagnosis-2026-08-21.md) | **"Multi-year catch-up" CONFIRMED for the search — and the sizing is wrong in three ways.** (a) **cvc5 1.3.4 IS on this host** (`/nas3/data/axeyum/harness/bin/cvc5`, not on `$PATH`), so this was measured against the recorded reference, not a stand-in — and **z3 is not a stand-in for cvc5 here**: same run, z3 **136/200** vs cvc5 **76/200**, 60 files apart, cvc5's decided set a strict SUBSET of z3's. The sibling note's "z3 within 5 files" holds on the linear divisions and does not transfer. So the row means 38.2% of *plain cvc5*; against z3 it is **27.9%**. (b) **58 of our 162 undecided files are decided by neither reference** — a gap sized by "files we miss" rather than "files the reference decides" overstates this division by 36%. (c) **The deficit is one benchmark family.** `20170427-VeryMax/ITS` is 134 of the 200 pinned files and **74 of the 104 misses**; excluding it the same run gives 29/39 = **74.4% of cvc5**, around QF_RDL's rate, and on `20220315-MathProblems` we decide **6/9 where both references decide 0**. Mechanism: every specialised nonlinear-integer route declines and `int-blast-ladder` is decisive on **158/161**; its width ladder admits a rung only if every integer *literal* fits, so a `2^30` Farkas coefficient leaves **1 live rung on 32 files, of which we decide 0**. **No cheap win exists and three were measured to prove it**: lifting the projected-clause ceiling by the measured 9.4x over-approximation → **0 of 49**; admitting `nia-linearize` past the `dpll_lia` pre-SAT envelope (the same constant as gap #1's QF_IDL class) → **+1 of 200**; **4x the wall clock → 0 of 20** `Timeout` files. z3 decides 74 of the 104 misses in under 5 s — this is a different algorithm, not lost time. **Postscript**: the board was re-measured 127 s after this landed and the row now reads **40.7% (33/81)**. Three same-day cvc5 runs give 76 / 76 / 81 against the 89 recorded 15 days earlier, so the 89 is the outlier and every "N files behind" priced off it is a few files too large. Nothing in the diagnosis moves — the classes are per-file properties of our own failures. Residual hypothesis, unpriced: an **eager** small-domain product split (`nia_linearize.rs:750-777` already implements the lemma and its width-4 limit matches the `[-2,2]` boxes these benchmarks declare) reached *without* the lazy refinement loop that fails |
| 5 | **Externally-portable evidence — 15.7%, not the 8.5% first published** | §6.2 | The metric was counted from labels and undercounted by 1.75x; it is now decided from the certificate and guarded by a test that reads the source. The remaining 84% re-validates only inside axeyum, and that is the real target |
| 6 | **~30 checkers that re-run the producer** | §6.2 | A determinism check sold as a soundness check, over the highest-volume family |
| 7 | **User triggers (`:pattern`, `:weight`)** | §5 | The one quantifier gap that is real vs Z3, now that the sat-direction is closed |
| 8 | **Memory bound is inert** | §7 | Operational, and this box has already been OOM-killed once |
| 9 | Transcendentals; nested arrays; parametric datatypes | §4.1, §4.3, sized below | **Sized 2026-08-21 and DEPRIORITISED — "each blocking a whole slice" is not true of anything we measure.** Across 2,200 files in the 11 pinned competition lists: transcendentals **0**, nested arrays **0**, parametric datatypes **0**. Across the 1,101-file committed corpus: 10, 0, 0. These are real capability zeros and they block approximately nothing in the population this document scores. The honest caveat is that the population is a CHOICE — `QF_UFNRAT` has no pinned list, so its 0 is partly "we do not measure that division" |
| 4b | **`Int` is `i128` in the IR, and 13% of QF_UFLIA never reaches the solver** | measured below | 26 of the 200 QF_UFLIA competition files carry integer literals above 2^127 (78 digits — EVM 2^256 words). Axeyum decides **0 of 26**: rejected before any solver work. **The opportunity is 6, not 26 and not the 11 this row first claimed** — measured 2026-08-21 at 20 s, cvc5 (the actual parity reference) decides **6 of 26**, z3 decides 12. Not a parser fix: `Value::Int(i128)` is the IR representation and every arithmetic route is built on it, so it is ADR-sized. `WideUint` already exists as the precedent for wide bit-vectors |
| 10 | **CAV-2024 bit-blasting abstraction** | sized below | **Sized 2026-08-21 and DEPRIORITISED for our position.** Bitwuzla has it on by default since 0.8.0 and cvc5 is adding it, in a division whose top three sit within 32 benchmarks of each other — but that is a contest between leaders, and it is not our contest. We are **187/194 on QF_BV**, so the entire addressable set is **7 files**, and only 4 of those 7 contain `bvmul` at all (1 has `bvudiv`). Against gap #1's measured +17 in a division at 52.2%, this is the wrong thing to build next |

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

**Row 1's fix is landed, and it is better than the experiment.** ADR-0538
(`40a1ab969`): theory-core minimisation is now rationed by **oracle calls**, not
gated on core width. Measured on the pinned 200-file list, three arms with z3 run
adjacent per file:

```
QF_UFLIA   base 92  →  constant-bump A/B 112  →  shipped 114   (+22, −0)
           0 disagreements vs z3 · 0 vs declared :status
QF_IDL     control  66 → 65
```

Verified independently from the per-file data and by re-running six of the
newly-decided files live (6/6 reproduced, agreeing with z3 and the declared
status). It **strictly dominates** the diagnosis's constant bump — every file
that decided, plus two more — while keeping the memory protection the raw bump
traded away: a minimised-but-still-300-wide core costs the SAT solver what an
unminimised one costs, so the old constant survives as a *retention* bound.

The budget unit was chosen on this repository's determinism promise. Wall-clock
would make the learned clause set — and therefore the verdict on a marginal
instance — a function of machine load. One deletion candidate is one oracle
call, so the unit is machine-independent and proportional to the cost rationed.

**The control's single loss is real and reported as one.** All three arms
re-decide `diamonds.12.2.i.a.u` in isolation, but the shipped arm is ~11% slower
on it, which under load pushed a 15-second file past the external kill. The
change costs measurable time on QF_IDL and buys nothing there.

At 114/180 that division moves from 52.2% to roughly **63%** — pending the
re-measurement, which is running from a tree that predates this fix and will
therefore understate it.

**Sized and deprioritised (2).** Row 10 proposed the CAV-2024 bit-blasting
abstraction on the grounds that both specialist references have it and the QF_BV
podium is tight. Both facts are true and neither is about us. Our QF_BV slice:

```
200 files · axeyum solves 187 · bitwuzla solves 194 · neither solves 6
                     addressable set = 7 files
        of which contain bvmul: 4      bvudiv: 1
```

So the ceiling is 7, the abstraction-shaped subset is about 4, and we are at
96.4% in that division. Ranked against gap #1's **measured +17** in QF_UFLIA at
52.2%, this is straightforwardly the wrong next build. It stays on the list
because a technique both references adopted is worth understanding — not because
it closes anything here.

**Sized and deprioritised.** Row 9 called transcendentals, nested arrays and
parametric datatypes "clean capability zeros, each small and each blocking a
whole slice". The first half is right and the second is not, for anything this
document measures. Scanned 2026-08-21 with a positive control in the same
command (`(assert` matched 1,101 of 1,101 corpus files, and all 11 lists were
found):

| feature | 2,200 competition files | 1,101 corpus files |
|---|---:|---:|
| transcendentals | **0** | 10 |
| nested arrays | **0** | 0 |
| parametric datatypes | **0** | 0 |

So building any of them moves no measured number. That does not make them
worthless — an external user hitting `(sin x)` gets a parse error today, and
`QF_UFNRAT` has no pinned list precisely because we do not compete there — but
it does mean they should not be ranked against work that moves a division. The
population a gap is scored against is a choice, and this row was being scored
against one that does not contain it.

**And the sizing itself was wrong, in the same way, one level down.** This row
first read "26 files blocked". I corrected it to "~11" by measuring **z3**,
because I believed cvc5 was not installed. cvc5 is installed, and it decides
**6 of 26** where z3 decides 12 — twice as many. So:

```
as written        26 files
sized with z3     ~11        (a proxy, chosen because the reference was
                              wrongly believed absent)
measured, cvc5      6        (5 sat, 1 unsat, 20 undecided at 20 s)
```

A 4.3x overstatement, and my own correction of it was still 1.8x over. The
lesson is not "z3 is a bad proxy" — it is that **a proxy was used without ever
being validated as one**, and the validation was cheap and available. §9 row 4's
diagnosis measured the same disagreement independently and larger: z3 136/200
against cvc5 76/200 on QF_NIA, with cvc5's decided set a strict subset of z3's.

**Sized before it was chased.** The diagnosis note reports 26 QF_UFLIA files
lost at the parser to oversized `Int` literals and observes that no solver work
touches them — both true, and I verified the 26 independently (78-digit
literals; positive control on the same scan). What neither document said is how
many of those the *reference* solves: **z3 4.13.3 at 20 s decides 11 of the 26**.
So "13% of a division" is a real defect and roughly a **+11** opportunity, not a
+26 one. A gap sized by "files we cannot parse" rather than "files the reference
decides and we do not" would have overstated this by more than double.

**Confirmed, and re-sized (row 4).** QF_NIA's "genuine multi-year catch-up" is
the one framing in §9 that survived being measured against: the three cheapest
levers in the division yield **0**, **+1** and **+3** files, and 4x the wall
clock buys **0 of 20** search timeouts. Ranking it last among decision work is
right. Three things the row got wrong anyway, all of which change what the
number means:

- **cvc5 is on this host** at `/nas3/data/axeyum/harness/bin/cvc5` — it is simply
  not on `$PATH`. The diagnosis note for row 1 states twice that it is absent,
  and this document's own §0 method note says solver probes ran against z3. The
  reference we score against was reachable the whole time.
- **z3 is not interchangeable with cvc5 outside the linear divisions.** Row 1's
  note verified them within 5 files on QF_LRA/IDL/RDL/UFLIA, which is true and
  does not transfer: on QF_NIA, one run gives z3 **136/200** and cvc5 **76/200**,
  with cvc5's decided set a strict **subset** of z3's. "38.2 % of the reference"
  therefore means 38.2 % of *plain cvc5*; against z3 the same axeyum score is
  **27.9 %**. `parity-run.sh`'s header reasons that picking cvc5 makes our ratio
  harder — on this division it does the opposite, and the row named neither.
- **The deficit is one benchmark family**, not a theory. `20170427-VeryMax/ITS`
  is 67 % of the pinned list and **74 of the 104 misses**; drop it and the same
  run reads **74.4 % of cvc5**, around QF_RDL. On `20220315-MathProblems` we
  decide **6 of 9 and both references decide 0**. As with row 9, the population a
  gap is scored against is a choice — and here it is a choice that is producing
  the division's headline number.

The mechanism is worth one line because it is the same shape as row 1's §3.2:
the decisive route on **158 of 161** undecided files is a generic bounded
integer bit-blast whose width ladder admits a rung only if every integer
*literal* fits it, so a `2^30` Farkas coefficient — a coefficient, not a bound —
leaves **one live rung on 32 files, of which we decide zero**. Unreconciled
admission constants again, one division further on.

**Found while discharging, and not in the original document.** The parity ledger
holds **nine** divisions, not the eleven `PROJECT-STATE.md` claimed, and has
never held a QF_ABV entry despite a committed `parity-lists/QF_ABV.txt` — a list
that was never run.

## 10. What this document does not establish

- **The competition figures are 15 days old** (QF_BV 4 days). Nothing since
  should have moved them much — this session's work was evidence and proofs, not
  decision procedures — but that is an argument, not a measurement.
- ~~Every claim about cvc5 and Bitwuzla is source- or doc-derived; neither
  binary is installed on this host.~~ **FALSE, corrected 2026-08-21.** Both are
  installed — `/nas3/data/axeyum/harness/bin/{cvc5,bitwuzla}`, cvc5 1.3.4
  (`git f3b21c4`) and Bitwuzla 0.9.1, the exact versions the parity ledger names.
  They are simply not on `$PATH`, and three separate documents (this one, the
  reference-solver research, and the linear-arithmetic note, twice) recorded
  "not installed" from a bare `command -v`.

  That is the same mistake as `lean`, which this repository already documents:
  `check-lean-gate.sh`'s header exists because `which lean` printed nothing while
  elan had it under `~/.elan`. **An absent binary on `$PATH` is not an absent
  binary**, and it took a fourth lane running `find` to notice.

  The cost was not hypothetical. Claims about cvc5 in §4 were source-derived when
  they could have been measured, and gap 4b was sized with z3 as a *proxy* for
  cvc5 — while §9 row 4's diagnosis measured **z3 136/200 against cvc5 76/200 on
  QF_NIA**, sixty files apart, with cvc5's decided set a strict subset of z3's.
  A proxy that disagrees by 60 files on one division cannot be assumed to agree
  on another.
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
