# 11 — Applied and computational mathematics

Reviewer: a formal-methods researcher, with a computable-analysis colleague
Verdict, 2026-09-04: **sees the most novel object in the building**
Last measured: 2026-09-04 at `1856cdb3c`

> "Everyone upstairs is asking whether you have their theorems. I am asking
> what produced them, and the answer is the interesting part."

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

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
| SAT | a proof-producing CDCL core (1-UIP conflict analysis, two-watched literals) emitting DRAT, plus an independent DRAT checker doing RUP and RAT (ADR-0011, ADR-0012) |
| bit-blasting | typed IR → AIG with deterministic structural hashing → Tseitin CNF, with replay maps kept so every `sat` is checkable by evaluating the original term |
| SMT | the full scalar QF_BV operator set, arrays by read-over-write plus Ackermann, floating point over generic `(exp, sig)`, strings, linear and nonlinear arithmetic, quantifier fragments |
| CAS | `axeyum-cas`, a 79k-line computer algebra system whose evidence must reconstruct into kernel terms or be visibly labelled `cas-internal` (ADR-0601) |
| producers | `linarith` (ℕ, ℤ, generic over `Alg.OrderedRing` and `AlgS.OrderedRing`, reaching ℝ), `ring` (ℕ, ℤ, ℚ), `simp` (ℕ, ℤ, List), `decide` (ℕ, ℤ, ℚ), and a `Then`/`First` tactic combinator — each **emitting a kernel proof term, not a verdict** |
| the anchor | every emitted term re-checked by `Kernel::add_declaration`; a corrupted certificate is refused by the *kernel*, demonstrated with the producer's own arithmetic check disabled |
| exact reals | `CReal` as regular sequences with explicit moduli — computable analysis, not floating point |

**Results this side produced**, in the ledger as `computed` or with
reconstruction evidence: two four-colour Rado numbers; Smith normal form of a
concrete integer matrix; GF(2) irreducibility and tensor-rank decompositions;
sum-of-squares certificates including a PSD-but-not-SOS witness, a Lyapunov
function and a barrier certificate; Gröbner cofactor refutations of unit
ideals; Horowitz rational integration; partial fractions with coefficient
matching; Pratt primality certificates; Gosper hypergeometric summation;
real-algebraic IVT, MVT, EVT and Taylor-remainder brackets.

**The measured number their field would ask for:** 67 hand-written proofs
retired and replaced by producer output in a single week (2026-09-03), each
re-admitted at a byte-identical type with an empty axiom footprint.

## Their verdict

**The formal-methods seat.** Proof-producing search feeding a small
independent checker is their discipline's central idea, and they have seen it
implemented in pieces: SAT solvers that emit DRAT, SMT solvers with proof
modes, proof assistants with reflection tactics. What they have not seen is
one project holding *all* of it — a SAT core, an SMT stack, a CAS, and a
Lean-compatible kernel — with the rule that nothing enters the trusted base
except through one function, and a ledger that records the axiom footprint of
what came out. The producer-retirement number is the metric they would fasten
on, because it measures the thing that matters: the marginal cost of a theorem
falling toward CPU time.

Their sharpest observation, and a warning: **the certificate must carry every
distinction its producer makes.** The project has already learned this the
hard way — a checker whose exit status did not depend on its finding, an
operation registry that was a dispatch table rather than a producer — and the
discipline that came out of it (delete a guard, require exactly one test to
die) is the right one. They would want it applied to every new producer
without exception.

**The computable-analysis seat.** Exact real arithmetic with explicit moduli,
an IVT proved by bisection that *returns an approximate root*, and integration
with certified error bounds is their subject, and finding it inside a proof
assistant with no floating point anywhere is unusual. Their reservation is
performance: they would immediately ask what it costs to evaluate π to a
thousand digits through this representation, and the honest answer is that
nobody has measured it, because the library's numerals are unary and the
representation was built for provability rather than speed.

**Both seats' shared reservation.** The bridge between the two halves is
incomplete. Several of the strongest computational results — the Rado numbers
above all — sit in the ledger as `computed`, with a certificate but no kernel
statement of *what was computed*. That is the gap between "we searched and
checked the search" and "the library knows this theorem", and closing it is
the project's own stated thesis.

## What they would say is missing

- **Kernel statements for the computed results.** A Rado number with a
  certificate is not yet a theorem about a defined object. See
  [07-combinatorics.md](07-combinatorics.md).
- **More producers, and over more carriers.** `linarith` reaches ℝ; `ring`,
  `simp` and `decide` do not. A `field_simp`, a nonlinear arithmetic producer,
  and a `polyrith`-style Gröbner producer are the obvious next ones.
- **A performance story for exact reals.** Nobody has measured the cost of
  evaluating a transcendental to a given precision, and the unary numeral
  representation makes the answer non-obvious.
- **Interval arithmetic as a first-class carrier**, which is what the
  computable-analysis seat would actually use, and which composes with the
  existing certified error bounds.
- **Numerical linear algebra with certificates.** Exact rational rank and
  determinant exist; conditioning, iterative methods, and certified
  eigenvalue enclosures do not.
- **Independent replay of the CAS half.** ADR-0601 requires CAS evidence to
  reconstruct or be labelled; the labelled residue should be measured and
  shrinking, and that number should be published.

## The blocker

**None of a mathematical kind. Two of an engineering kind.**

- **Unary numerals.** Every `Nat` numeral in the kernel is unary, so cost is
  superlinear in the largest magnitude formed. This is why large computed
  constants cannot be stated in-kernel, and it bounds what the reconstruction
  route can carry.
- **Prelude build cost.** The ℝ prelude is 155k lines with a 16 MiB debug
  stack requirement; producers that emit into it pay that cost on every
  iteration.

## Next five, in their priority order

- [x] **1. Close the computed-to-proved gap on one flagship result.** *Done 2026-09-04: Schur's number.* Define
      Rado numbers in-kernel and have the search discharge a kernel-checkable
      statement. Their view: this is the project's own thesis, demonstrated on
      a research-level result, and it is currently one step short.
- [~] **2. Extend `ring` and `decide` to ℝ** — *`ring` done 2026-09-04; `decide` cannot, measured.*, the way `linarith` was
      generalized over `AlgS.OrderedRing`. Every producer that reaches a new
      carrier retires hand proofs across the whole shelf above it.
- [ ] **3. A nonlinear-arithmetic producer with Positivstellensatz
      certificates**, connecting the existing SOS work to a kernel-emitting
      route. The sum-of-squares results already exist as certificates; nothing
      reconstructs them.
- [x] **4. Measure and publish the exact-real performance envelope.** *Done 2026-09-04; the number is bad and published.* π and
      exp to a stated precision, with the cost model. Their view: you claim
      computable analysis and have never quoted a time.
- [~] **5. Measure the `cas-internal` residue and drive it down.** *Measured 2026-09-04: 76.7%, now a ratchet. Driving it down is unstarted.* The share
      of CAS evidence that does not reconstruct is the honest boundary of the
      trusted pipeline, and it should be a published, falling number.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: proof-producing SAT with DRAT checking, full SMT stack, 79k-line CAS, five kernel-emitting producers, 67 hand proofs retired in one week. Rado numbers and SOS/Gröbner results `computed` but not connected to kernel statements. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 2 landed** (roadmap W1-5): `ring::generic` extended with the same `Backend` shape `linarith` used, reaching `Alg.CommRing` and `AlgS.CommRing`; six goal shapes proved at `CReal.commRingS`, with a corrupted-certificate battery in which the **kernel** refuses the emitted term while the producer's own check is disabled. `decide` **cannot** reach ℝ and the reason is measured, not assumed: the real relations are quantifier-headed and no apartness-witness definition exists to give a decidable fragment — that definition is now a named next step. **Zero retirements**, and the reason is the lane's most useful output: wiring the producer into `creal/ring_helpers.rs` produced a genuine `Decline::NotAnIdentity` inside the prelude build, invisible to the unit tests, and the lane reverted rather than ship it. (ADR-1599.) | `a3f4f528c`; `ring::` 74, `decide::` 47 passed |
| 2026-09-04 | **Next Five item 1 landed** (roadmap W1-1): the computed→proved gap is closed on a real result. Schur's `R_2(x = y + z) = 5`, both halves from search, kernel-checked, footprint 0. The lower half is by *reflection* — a `Bool` triple loop the kernel's own conversion check reduces to `true` — which is the untrusted-search/trusted-checking thesis in its sharpest form. The four-colour results stay `computed`, and the obstruction is now named precisely and is combinatorial rather than a numeral cost. | `de0cd02da` |
| 2026-09-04 | **Next Five items 4 and 5 landed** (roadmap W1-12, W1-13), and both numbers confirm this reviewer's reservations rather than answer them. **Exact-real cost**: trivial constants normalize in under 5 ms at any index, but `e` at index 0 did not fully normalize in 400 s and π not in 480 s; the series' internal recursion is unary regardless of the caller's numeral, and the library's own bound theorems never force that reduction, which is why nobody had measured it. **CAS residue**: 46 of 60 certificate facts (76.7%) are `cas-internal` and never reconstruct. Now a registered ratchet with a four-guard control suite. Both published under `artifacts/measurements/`. (ADR-1617.) | `0ba67b82e` |

## How to re-measure

```sh
python3 - <<'PY'
import json, glob, collections
c = collections.Counter()
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f)); fr = (d.get('formal') or {}).get('fragment', '')
    if fr.startswith('QF') or '-' in fr: c[fr] += 1
print(sum(c.values()), 'solver/CAS-side facts'); print(c.most_common(12))
PY

scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel --lib \
  -- linarith ring simp decide tactic --test-threads=4
```

## Related

- [07-combinatorics.md](07-combinatorics.md) — the Rado results, from the
  other side
- [10-logic-and-foundations.md](10-logic-and-foundations.md) — the trust
  anchor these producers feed
- [ADR-0601](../research/09-decisions/adr-0601-three-producers-one-trust-anchor.md),
  [evidence and checker discipline](../contributor-guide/evidence-and-checker-discipline.md)
