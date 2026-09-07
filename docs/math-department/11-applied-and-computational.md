# 11 — Applied and computational mathematics

Reviewer: a formal-methods researcher, with a computable-analysis colleague
Verdict, 2026-09-06: **sees the most novel object in the building, and now
sees where its two halves fail to meet**
Last measured: 2026-09-06 at `b40a0f309`

> "Everyone upstairs is asking whether you have their theorems. I am asking
> what produced them, and the answer is the interesting part."

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

> **Retired 2026-09-06 (ADR-1674):** the 430 is not reproducible by its own
> method - three later readings give 599, 620, 721 and 973 on three different
> denominators. The measured, gated figure is **721 of 3,079 registered
> kernel theorem names uncovered**, ratcheted by `gen-ledger-coverage`.

## The persona

Two seats. The formal-methods researcher builds and verifies solvers, cares
about certificates, DRAT proofs, and whether a decision procedure's answer can
be checked independently of the procedure. The computable-analysis colleague
cares about exact real arithmetic, interval methods, and whether a numerical
claim carries an error bound you can trust. Neither of them thinks a theorem
count is the point; both of them think the *pipeline* is.

## What the library has today

**A complete untrusted-search / trusted-checking stack, and it is the part of
the project with the least precedent.**

| layer | what exists |
|---|---|
| SAT | a proof-producing CDCL core (1-UIP conflict analysis, two-watched literals) emitting DRAT, and **it is now the engine on every path**: `rustsat-batsat` is a non-default `batsat-reference` feature used only as a differential oracle (ADR-1703 slice 1, `crates/axeyum-cnf/Cargo.toml:24`). Every native `unsat` derives the empty clause from RUP-learned clauses, so a DRAT proof exists by construction |
| checkers | **three, independent of the search**: `check_drat` (RUP+RAT, ADR-0011); an LRAT hint-following checker plus a DRAT→LRAT elaborator (RUP-only, `crates/axeyum-cnf/src/lrat.rs`, in tree since 2026-06-16); and a self-contained Alethe checker whose resolution steps are decided by the proof-producing core and re-checked by `check_drat` |
| bit-blasting | typed IR → AIG with deterministic structural hashing → Tseitin CNF, with replay maps kept so every `sat` is checkable by evaluating the original term |
| SMT | the full scalar QF_BV operator set, arrays by read-over-write plus Ackermann, floating point over generic `(exp, sig)`, strings, linear and nonlinear arithmetic, quantifier fragments |
| CAS | `axeyum-cas`, 155,687 lines across 102 files (about 81k outside the test modules), whose evidence must reconstruct into kernel terms or be visibly labelled `cas-internal` (ADR-0601) |
| validated numerics | `enclosure.rs` + `enclosure_integral.rs` + `enclosure_special.rs`, 7,759 lines landed 2026-09-05/06: rational interval enclosures with `BigRational` endpoints, one evidence `Step` per expression node, and a `verify` that **re-derives every step from `(head, inputs, order)` and trusts no recorded number**. Newton–Krawczyk for nonlinear systems. No `f64` below that line |
| exact arithmetic | `axeyum-arith`, 5,079 lines: dyadic rationals with directed rounding, certified positional expansions, arbitrary-precision rationals, fraction-free polynomials, modular rings, `p`-adic lifting, algebraic numbers (ADR-1710) |
| producers | **six**: `linarith` (ℕ, ℤ, generic over `Alg.OrderedRing` and `AlgS.OrderedRing`, reaching ℝ), `ring` (ℕ, ℤ, ℚ, and since 2026-09-04 `CReal.commRingS`), `simp` (ℕ, ℤ, List), `decide` (ℕ, ℤ, ℚ), `psatz` (ℚ, sum-of-squares, 2026-09-05), and a `Then`/`First` combinator — each **emitting a kernel proof term, not a verdict** |
| the anchor | every emitted term re-checked by `Kernel::add_declaration`; a corrupted certificate is refused by the *kernel*, demonstrated with the producer's own arithmetic check disabled |
| exact reals | `CReal` as regular sequences with explicit moduli — computable analysis, not floating point |

**Results this side produced.** The ledger holds 2,954 facts, of which 2,678
are `proved` and exactly **two** are still `computed` — the two four-colour
Rado numbers, and nothing else. The rest of this side's output is `proved` on
replay evidence: Smith normal form of a concrete integer matrix; GF(2)
irreducibility and tensor-rank decompositions; sum-of-squares certificates
including a PSD-but-not-SOS witness, a Lyapunov function and a barrier
certificate; Gröbner cofactor refutations of unit ideals; Horowitz rational
integration; partial fractions with coefficient matching; Pratt and CRT
primality certificates; Gosper hypergeometric summation; real-algebraic IVT,
MVT, EVT and Taylor-remainder brackets. **Read `proved` carefully here**: of
the 61 `cas-certificate` facts, 16 carry a kernel term and 45 do not.

**The measured number their field would ask for:** 67 hand-written proofs
(plus 5 in the list prelude) retired and replaced by producer output in a
single week, each re-admitted at a byte-identical type with an empty axiom
footprint. **That number has not moved since 2026-09-03**, and both reasons
are recorded: `ring` at ℝ retired nothing because a producer cannot retire its
own primitives (ADR-1599), and `psatz`'s producer contract was *born retired* —
91 facts match its shape and all 91 were already proved.

**The number beside it, which is new.** `psatz` declared three ℚ inequalities
into the prelude whose proof terms **nobody wrote**, with no hand-written
fallback: if the producer declines, the prelude does not build. That is
production rather than retirement, and it is the first of its kind here.

## Their verdict

**The formal-methods seat.** Proof-producing search feeding a small
independent checker is their discipline's central idea, and they have seen it
implemented in pieces: SAT solvers that emit DRAT, SMT solvers with proof
modes, proof assistants with reflection tactics. What they have not seen is
one project holding *all* of it — a SAT core, an SMT stack, a CAS, and a
Lean-compatible kernel — with the rule that nothing enters the trusted base
except through one function, and a ledger that records the axiom footprint of
what came out. Two things landed since their last visit that they would call
real: the BatSat dependency is gone from the default graph, so "lower-assurance
UNSAT" is not a boundary that moved but one that disappeared; and a **timing**
regression is now red in a gate, which is the first time the pipeline's cost
has been ratcheted rather than only its correctness.

Their sharpest observation, and a warning: **the certificate must carry every
distinction its producer makes.** They would now point at a live instance of
exactly that failure, in this project's own SOS route. Read
`crates/axeyum-solver/src/reconstruct.rs:3251-3297`:
`reconstruct_sos_to_lean_module_raw` tries the real reconstruction, and on
`UnsupportedTerm` — precisely when it *cannot* do the work — falls through to
`reconstruct_sos_certificate_wrapper_to_lean_module`, which mints an opaque
`Prop`, an axiom asserting it and an axiom negating it, and renders the result
under `theorem axeyum_refutation : False`, the **same** name the honest route
uses (`LEAN_MODULE_THEOREM`, line 2114). From the emitted module text the two
populations are indistinguishable. This is not a lane's claim repeated here; it
is what the file says on `main` today.

**The computable-analysis seat.** Their reservation from 09-04 was that nobody
had ever quoted a time. Both halves have now been measured, and the interesting
finding is that they disagree by orders of magnitude.

- **In the kernel**, `CReal` normalization is unusable: trivial constants
  resolve in under 5 ms at any index, but `e` at index 0 — the loosest possible
  request — did not finish in 400 s and π not in 480 s. The series' internal
  recursion is unary regardless of the caller's numeral (ADR-1617).
- **In the CAS**, the enclosure layer answers the question they actually asked.
  π to a width of `2^-500` (about 150 decimal digits) costs 20.3 ms to produce
  and 15.1 ms to *verify*; `Γ(1/3)` to `2^-100` costs 1.49 s / 1.12 s; the
  definite integral `∫₀¹ e^(−x²)` to `2^-30` costs 275 ms / 148 ms. Marked
  ADVISORY by their author — one unpinned run each on a loaded host — which is
  the right label.

They would say the honest reading is that this project has a working exact-real
*numeric* engine and a working exact-real *proof* carrier, and no bridge
between them. Which is the same shape as the other seat's complaint.

**Both seats' shared reservation.** The computed-to-proved gap is nearly
closed: Schur's `R_2(x = y + z) = 5` was proved in-kernel from search in both
halves, and only the two four-colour Rado numbers remain `computed`. Their
reservation has therefore moved one layer out — **the new capability is not in
the ledger at all**. Zero facts cite the enclosure layer; 45 of 61
`cas-certificate` facts carry no kernel term; and 1,019 of the CAS's 1,280
public functions are uncertified against its own trust registry. The gap is no
longer "we searched and did not state it"; it is "we built it and did not
record what it establishes."

## What they would say is missing

- **Kernel statements for the two remaining `computed` results.** Down from
  the whole list to `F:rado-r4-a5-b3` and `F:rado-r4-a5-b4`. The obstruction is
  measured and combinatorial, not a numeral cost: `Arrows 5 3 4 625` needs a
  term over 4⁶²⁵ colourings, and colourings are functions (ADR-1596). See
  [07-combinatorics.md](07-combinatorics.md).
- **A ledger row for the validated-numerics layer.** 7,759 lines with a
  re-deriving verifier and a mutation-checked guard set, and not one fact cites
  it. On this project's own rule, capability the ledger does not record is
  capability nobody can audit.
- **More producers, and over more carriers.** `psatz` closed the nonlinear gap
  over ℚ. `field_simp` and a `polyrith`-style Gröbner producer are absent —
  neither name occurs anywhere in the kernel crate. `decide` **cannot** reach
  ℝ, and the reason is measured rather than assumed: the real relations are
  quantifier-headed and no apartness-witness definition exists. `psatz` on
  `CReal` needs a **setoid ring producer**, which does not exist — the search,
  the certificate and the division step would move unchanged.
- **A bridge from the enclosure layer to `CReal`.** The CAS can bound π to
  about 150 digits in 20 ms with a checkable certificate; the kernel cannot
  normalize π at all. Nothing connects the two, so the certified numeric bound
  never becomes a kernel fact about `CReal.pi`.
- **Interval arithmetic as a first-class kernel carrier.** Measured absent
  against the full 4,765-declaration index: no declaration named `Interval`
  exists; the nearest, `Metric.Interval`, is `fun x => a ≤ x ∧ x ≤ b`, a
  membership predicate rather than an arithmetic carrier. Positive control in
  the same invocation: `CReal.Equiv` FOUND 333.
- **Numerical linear algebra with certificates.** Exact rational rank and
  determinant exist, and the Krawczyk operator now certifies solutions of
  nonlinear systems. Conditioning, iterative methods, and certified eigenvalue
  enclosures do not — `eigenvalues` in the CAS returns symbolic roots with no
  enclosure attached.
- **Independent replay of the CAS half, continued.** The number now exists and
  is falling: 46 of 60 `cas-internal` (76.7%) on 09-04, **45 of 61 (73.8%)**
  today, with the ratchet floor at 16 reconstructed. It should keep falling.

## The blocker

**None of a mathematical kind. Two of an engineering kind, and one of them is
narrower than this file used to claim.**

- **Unary numerals — a cost of *reduction*, not of *statement*.** [Corrected
  2026-09-06.] This file previously said the unary numeral is "why large
  computed constants cannot be stated in-kernel". That was measured false:
  `IsRadoNumber 5 3 4 625` type-checks, because a `Prop` that merely mentions a
  numeral neither reduces it nor pays for it (ADR-1596). What the unary numeral
  does bound is anything that must *compute*: the `CReal` series above, and the
  largest magnitude a reconstruction may form — Pratt reaches prime 251 in
  398 s and does not reach 2⁸⁹−1.
- **Prelude build cost.** The ℝ prelude is **171,157 lines** (`creal.rs`
  11,595 plus 159,562 across 109 files in `creal/`) and its *measured* stack
  requirement is 16,777,216 B in debug and 8,388,608 B in release
  (`artifacts/kernel-stack-envelope.tsv`). Producers that emit into it pay that
  on every iteration.

## Next five, in their priority order

- [ ] **1. Remove the axiom-minting fallback in the SOS reconstruction route,
      or make it name itself.** `reconstruct_sos_certificate_wrapper_to_lean_module`
      is entered exactly when the honest route fails, and renders under the
      honest route's theorem name. Their view: this is the one defect in the
      building that is the *opposite* of the project's thesis, and it is a short
      change away from being a labelled decline instead. (`axeyum-solver` is
      another session's crate; the reading above is a reading, not a patch.)
- [ ] **2. Put the validated-numerics layer in the ledger.** Facts for the
      enclosures that already verify — π, `Γ(1/3)`, `∫₀¹ e^(−x²)` — classified
      honestly as `cas-internal` until something reconstructs them, so the
      residue metric counts the capability that exists rather than ignoring it.
- [ ] **3. A setoid ring producer, which unlocks `psatz` at `CReal`.** The
      blocker is named and small: `CReal`'s equality is the defined relation
      `CReal.Equiv`, and the certificate's identity is the crux of every proof
      `psatz` emits. Everything else in that producer is already
      carrier-agnostic.
- [ ] **4. Keep driving the `cas-internal` residue down from 73.8%.** The
      2026-09-05 follow-on showed the method — measure each family's largest
      formed numeral against the unary budget, and flip the family whose every
      claimed instance the kernel reaches. GF(2), hypergeometric and the SOS
      families are the untouched blocks.
- [ ] **5. Finish the LRAT half of `by axeyum` — and re-scope it first.**
      [Corrected 2026-09-06.] ADR-1666 records "the route needs a conversion"
      from DRAT to LRAT. **That conversion has been in tree since 2026-06-16**
      (`elaborate_drat_to_lrat`, RUP-only, which is exactly what the CDCL core
      emits by construction). What is actually missing is the `BitVec`/`Bool`
      goal fragment, a second sidecar response shape carrying a certificate
      file, and a demonstration that `Std.Tactic.BVDecide` accepts our LRAT
      dialect end to end. None of that is measured yet.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: proof-producing SAT with DRAT checking, full SMT stack, 79k-line CAS, five kernel-emitting producers, 67 hand proofs retired in one week. Rado numbers and SOS/Gröbner results `computed` but not connected to kernel statements. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 2 landed** (roadmap W1-5): `ring::generic` extended with the same `Backend` shape `linarith` used, reaching `Alg.CommRing` and `AlgS.CommRing`; six goal shapes proved at `CReal.commRingS`, with a corrupted-certificate battery in which the **kernel** refuses the emitted term while the producer's own check is disabled. `decide` **cannot** reach ℝ and the reason is measured, not assumed: the real relations are quantifier-headed and no apartness-witness definition exists to give a decidable fragment — that definition is now a named next step. **Zero retirements**, and the reason is the lane's most useful output: wiring the producer into `creal/ring_helpers.rs` produced a genuine `Decline::NotAnIdentity` inside the prelude build, invisible to the unit tests, and the lane reverted rather than ship it. (ADR-1599.) | `a3f4f528c`; `ring::` 74, `decide::` 47 passed |
| 2026-09-04 | **Next Five item 1 landed** (roadmap W1-1): the computed→proved gap is closed on a real result. Schur's `R_2(x = y + z) = 5`, both halves from search, kernel-checked, footprint 0. The lower half is by *reflection* — a `Bool` triple loop the kernel's own conversion check reduces to `true` — which is the untrusted-search/trusted-checking thesis in its sharpest form. The four-colour results stay `computed`, and the obstruction is now named precisely and is combinatorial rather than a numeral cost. | `de0cd02da` |
| 2026-09-04 | **Next Five items 4 and 5 landed** (roadmap W1-12, W1-13), and both numbers confirm this reviewer's reservations rather than answer them. **Exact-real cost**: trivial constants normalize in under 5 ms at any index, but `e` at index 0 did not fully normalize in 400 s and π not in 480 s; the series' internal recursion is unary regardless of the caller's numeral, and the library's own bound theorems never force that reduction, which is why nobody had measured it. **CAS residue**: 46 of 60 certificate facts (76.7%) are `cas-internal` and never reconstruct. Now a registered ratchet with a four-guard control suite. Both published under `artifacts/measurements/`. (ADR-1617.) | `0ba67b82e` |
| 2026-09-04 | **Item 5's "drive it down" half started** (roadmap W1-13 follow-on, ADR-1622): Pratt and CRT certificates reconstruct into kernel terms, with the modular exponentiation done by square-and-multiply reducing at every step so the largest numeral formed is n² rather than aⁿ⁻¹. Residue 46 → 45, reconstructed 14 → 16, the ratchet's floor raised. The measured boundary this reviewer would want: prime 47 in under a second, 101 in 8 s, 251 in 398 s, 509 not attempted. The Mersenne-89 fact correctly did not flip. Kernel refusal of five forged certificates demonstrated with every Rust-side guard disabled. | `f0bc8a692`; `int_prelude::` 100 passed |
| 2026-09-05 | **This reviewer's Lean demand is half answered** ([ADR-1666](../research/09-decisions/adr-1666-by-axeyum-is-a-lean-tactic-and-lean-checks-the-term.md), lane `lean-tactic`, `14-lean-lang.md` Next Ten item 6). `by axeyum` is a real Lean tactic in a Lake package with no Mathlib dependency: it ships the already-elaborated goal to a Rust sidecar and hands the returned proof TERM to Lean's own elaborator and kernel — nothing the sidecar says is believed, and there is no `sorry` or `admit` path. Measured on pinned `v4.34.0-rc1`: 11 of 11 ℕ goals accepted in ordinary Lean-core notation, 11 of 11 mutations rejected, 5 goals axiom-free end to end. Two defects real Lean found that no Rust test could have, including a mutation battery that was VACUOUS on its first run (the tactic read the optional syntax node instead of the string inside it, so every stub fell back to the real sidecar and passed by CLOSING the goal it was meant to fail). **The LRAT half is not done**: `Std.Tactic.BVDecide` consumes LRAT and `axeyum-cnf` emits DRAT, so the route needs a conversion, a `BitVec`/`Bool` goal fragment, and a second response shape carrying a certificate file. ℤ is blocked by a visibility fact, not a mathematical one: `linarith::int::prove` and `ring::int::prove` are `pub(crate)`. | `scripts/check-lean-tactic.sh`: `goals-accepted=11 mutations-rejected=11 shim-rows=13 controls=1`, checker `leanprover--lean4---v4.34.0-rc1/bin/lean` (`3447a668`) |
| 2026-09-05 | **Item 3 landed** (roadmap W2-16, ADR-1649): `psatz`, a sum-of-squares producer over ℚ whose rational LDLᵀ decides positive semidefiniteness, with three prelude theorems declared from certificates and no hand-written proof, the Motzkin polynomial refused as PSD-not-SOS with the dual witness verified, and a producer contract that was born retired because every fact its shape matches is already proved. **Correction to this file**: an SOS certificate already reached the kernel through `ordered_ring_refutation` with footprint 0; the gap was a contract, a positive-goal route, and coverage, not reconstruction. | `c27636688`; `psatz` 29, `tactic::` 25, `rat_prelude_tests` 122 passed in the lane |
| 2026-09-06 | **Whole-file re-measurement.** All five of the previous Next Five had landed, so the list is replaced. Numbers re-derived, not inherited: ledger 2,954 facts / 2,678 `proved` / **2 `computed`** (both four-colour Rado, nothing else); `cas-certificate` residue **45 of 61 = 73.8%** (was 46 of 60 = 76.7%); CAS **155,687 lines in 102 files**, of whose 1,280 `pub fn` 151 are certified and 1,019 are not; producer sweep **472 passed, 1 ignored, 0 failed**; ℝ prelude **171,157 lines**, stack 16 MiB debug / 8 MiB release from the pinned envelope. Four claims corrected. (a) "79k-line CAS" understated it by half. (b) The unary-numeral blocker said large constants "cannot be stated in-kernel"; ADR-1596 measured that false — the cost is reduction, not statement. (c) ADR-1666's "the route needs a DRAT→LRAT conversion" is a stale blocker: `elaborate_drat_to_lrat` has been in `axeyum-cnf` since 2026-06-16, RUP-only, which is what the core emits by construction. (d) The retirement total is unchanged at 67 since 2026-09-03, and the two reasons are recorded rather than glossed. Two things landed that this file had not seen: the **validated-numerics enclosure layer** (7,759 lines, a `verify` that re-derives every step, π to `2^-500` in 20.3 ms produce / 15.1 ms verify, ADVISORY) with **zero ledger facts citing it**, and **ADR-1703** retiring BatSat so the proof-producing core is the engine everywhere. The new item 1 is read directly off `main`: the SOS reconstruction route falls back, on `UnsupportedTerm`, to a wrapper that mints two axioms and renders under the honest route's `axeyum_refutation` name. | `b40a0f309`; `check-cas-internal-residue.py --report` exit 0; `check-cas-trust-registry.py` 151/110/1019; producer sweep from the prebuilt release lib binary built 2026-09-06 06:46 |

## How to re-measure

```sh
# The solver/CAS-side slice of the fact ledger, by fragment.
python3 - <<'PY'
import json, glob, collections
c = collections.Counter()
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f)); fr = (d.get('formal') or {}).get('fragment', '')
    if fr.startswith('QF') or '-' in fr: c[fr] += 1
print(sum(c.values()), 'solver/CAS-side facts'); print(c.most_common(12))
PY

# What is still `computed` rather than proved — the shared reservation's metric.
python3 - <<'PY'
import json, glob, collections
c = collections.Counter()
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f)); c[d.get('epistemic_status')] += 1
    if d.get('epistemic_status') == 'computed': print('computed:', d.get('id'))
print(sum(c.values()), 'facts'); print(sorted(c.items()))
PY

# The honest boundary of the trusted pipeline (exit status depends on the finding).
python3 scripts/check-cas-internal-residue.py --report
python3 scripts/check-cas-trust-registry.py

# The producers. Multiple filters are OR-ed by this libtest; confirm a NONZERO
# count (472 passed, 1 ignored on 2026-09-06) — a green run of zero tests is not
# a gate.
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel --lib \
  -- linarith ring simp decide tactic --test-threads=4

# Absence claims about kernel carriers. --include-constructed is required for the
# CReal/Metric namespaces, and every ABSENT needs a positive control in the same
# invocation.
./target/release/examples/shape_search --const Interval --include-constructed
./target/release/examples/shape_search --const CReal.Equiv --include-constructed
```

## Related

- [07-combinatorics.md](07-combinatorics.md) — the Rado results, from the
  other side
- [10-logic-and-foundations.md](10-logic-and-foundations.md) — the trust
  anchor these producers feed
- [13-computer-algebra.md](13-computer-algebra.md) — the CAS measured as a CAS,
  including the enclosure layer's own roadmap item
- [ADR-0601](../research/09-decisions/adr-0601-three-producers-one-trust-anchor.md),
  [evidence and checker discipline](../contributor-guide/evidence-and-checker-discipline.md)
