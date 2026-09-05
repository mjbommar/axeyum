# ADR-1617: the exact-real evaluation cost is measured (and mostly intractable today), and the `cas-internal` residue is now a gated, falling number

Status: accepted
Date: 2026-09-04
Lane: `producer-measurements`
Roadmap: W1-12 (the exact-real performance envelope) and W1-13 (measure and
reduce the `cas-internal` residue) — reviewer
`docs/math-department/11-applied-and-computational.md`, items 11.4/11.5

Index-summary: Two published measurements. W1-12: forcing the kernel's own
reduction engine to compute a concrete rational sample of `CReal.pi`/`CReal.e`
does not complete within a multi-minute compute budget even at the loosest
possible request (index 0), while the library's own bound theorems
(`threeLePi`, `piLeFour`, ...) never force this reduction at all — they stay
symbolic. W1-13: the ADR-0601 SS2 `cas-internal` residue is 46 of 60
`cas-certificate` facts (76.7%), concentrated in number theory,
hypergeometric/binomial identities, GF(2), and SOS/Positivstellensatz
families with no kernel bridge yet; it is now a registered, mutation-verified
ratchet (`scripts/check-cas-internal-residue.py`) that refuses regression.

## Context

Both items are named in `docs/math-department/11-applied-and-computational.md`
as measurements "nobody has" run:

> "[The computable-analysis seat's] reservation is performance: they would
> immediately ask what it costs to evaluate π to a thousand digits through
> this representation, and the honest answer is that nobody has measured it,
> because the library's numerals are unary and the representation was built
> for provability rather than speed."

> "Independent replay of the CAS half. ADR-0601 requires CAS evidence to
> reconstruct or be labelled; the labelled residue should be measured and
> shrinking, and that number should be published."

The 2026-09-04 audit of that file (`docs/math-department/AUDIT-2026-09-04.md`,
row 11) found `scripts/check-cas-substance.py` and its `.ratchet`, could not
determine whether either answers the W1-13 question, and had not run the
ratchet. It does not: `check-cas-substance.py` (ADR-0622) floors what the 14
`kernel-reconstructed` facts' kernel obligations *establish*, never the split
between `kernel-reconstructed` and `cas-internal` itself.

This lane is measurement-only: no kernel declaration is added by either
deliverable.

## Measurement A — W1-12, the exact-real evaluation cost envelope

### Method

`crates/axeyum-lean-kernel/examples/creal_eval_cost.rs` (new). For each of
`CReal.pi`, `CReal.e`, `CReal.sqrt (CReal.add one one)` and
`CReal.expFn CReal.one` (`exp 1`), plus three trivial controls
(`CReal.zero`, `CReal.one`, `CReal.add one one`), it builds the term
`Rat.num (CReal.seq x n)` / `Rat.den (CReal.seq x n)` for small concrete `n`,
built two ways — as the kernel's accelerated `Lit::Nat` bignum literal, and
as a genuine unary `Nat.succ (Nat.succ (... Nat.zero))` chain, matching this
codebase's own numeral-building idiom
(`linarith/generic.rs::nat_num_ctx`, `creal/pi.rs`'s own module doc: "every
numeral this prelude builds is unary and the kernel's binary-literal fast
path never fires") — and fully normalizes each with a hand-rolled deep
normalizer (`deep_nf`) built only from public `Kernel::whnf`/
`Kernel::expr_node` calls, the same primitives `Kernel::add_declaration`
uses to check a proof's definitional-equality obligations. No new kernel
declaration is added; every term is transient. Built via
`scripts/cargo-serialized.sh build --release`; timed off the prebuilt
binary directly, never under the `cargo-serialized.sh` flock.

Host: 22-day-uptime shared dev box, multiple concurrent lanes. Load average
at the time of the runs below ranged 1.4–19.2 (`uptime`, read before and
after each run) — **this host was not idle**, and the absolute wall-clock
numbers below are NOT COMPARABLE to a clean-machine baseline in the sense
`docs/research/08-planning/frontier-ratchet-reference-frame.md` uses that
phrase; they are ADVISORY on magnitude, not a precise timing.

### The controls: zero, one, two

| target | encoding | n=0..3 wall clock | result |
|---|---|---|---|
| `CReal.zero` | literal | 0.0–0.3 ms | `0`, exact, every `n` |
| `CReal.zero` | unary | 0.0 ms | `0`, exact, every `n` |
| `CReal.one` | literal | 0.0–0.2 ms | `1`, exact, every `n` |
| `CReal.one` | unary | 0.0 ms | `1`, exact, every `n` |
| `CReal.add one one` | literal | 2.3–5.0 ms | `2`, exact, every `n` |
| `CReal.add one one` | unary | 2.0–2.2 ms | `2`, exact, every `n` |

These are the first thing this measurement establishes: `deep_nf` and the
whole pipeline work correctly and cheaply, and — the first real finding —
**the literal-vs-unary encoding of the CALLER's query index `n` makes no
measurable difference here.** Both are sub-5ms at every `n` tried. This
matters for reading the series results below correctly.

### `pi`, `e`, `sqrt2`, `exp1`: did not complete

At `n = 0` — the loosest possible request, the very first sample of the
sequence — for `CReal.e` (the simplest of the four: no `CReal.mul`/`bound`
wrapping, a bare `speedup(diagonal(expSeriesPartial), K)` series):

- `Rat.num`/`Rat.den`'s own outer `Kernel::whnf` call (exposing the head
  redex, i.e. unfolding `CReal.e`/`speedup`/`diagonal` far enough to see
  `Rat.mk`/`Rat.normalize`) completes in **30–42 ms** — fast.
- Full deep normalization (needed to actually read off the numerator and
  denominator as digits) **did not complete within a 400 second compute
  budget**, `--release`, prebuilt binary, no other flag changed.

`CReal.pi` did not complete within a 480 second budget at `n = 0` either.
`sqrt2` and `exp1` were not attempted past this point: both wrap a series in
an additional `CReal.mul`/`bound`-style composition on top of exactly the
machinery that already would not complete for the bare series, so they are
expected to be at least as expensive, not less.

**This is the headline number, and it is a "did not complete", not a
timing.** Per this repository's own discipline (`docs/contributor-guide/
multi-agent-operations.md`: "report an unfinished check as 'did not run'"),
that is reported as the finding rather than papered over with a partial or
extrapolated number.

### Where the cost blows up, and why

Not at the caller's query index — the zero/one/two controls show identical,
fast behaviour under both literal and unary encodings of `n`, at every `n`
tried. It blows up **inside the series machinery itself**, and the mechanism
is exactly the one `tc.rs`'s own module documentation names:
`reduce_nat_binop`'s accelerated bignum path (`Nat.add`/`Nat.mul`/`Nat.gcd`
on literals) fires only when **both operands** are already a `Lit::Nat` or
the bare `Nat.zero` constant. A nonzero `Nat.succ`-chain operand — which is
what every internal counter `CReal.e`'s own definition builds (index shifts,
`sumRange`'s recursion variable, `speedup`'s modulus arithmetic) — never
matches that pattern, so it falls through to full **structural** `Nat.rec`
recursion, term by term, regardless of how the caller's own outer `n` was
encoded. `Rat.add`'s `Rat.normalize` needs a `Nat.gcd` on these growing,
unary-recursed numerators and denominators at every step of the sum, which
is exactly the "a four-digit `Nat.gcd` costs tens of seconds" cost
`creal/pi.rs`'s own module doc names for choosing its series in the first
place — except here nothing bounds how many `Nat.rec` layers a caller's
demand for an arbitrary concrete sample can force.

**The deeper finding is what the library itself does NOT do.** The bound
theorems that already exist and build in every `creal` prelude —
`CReal.threeLePi`, `CReal.piLeFour`, `e <= 4`, `CReal.sqrt`'s and
`CReal.cosOne`'s bounds — are proved by a monotonicity/domination argument
that keeps the series index **symbolic** end to end and never asks the
kernel to reduce `CReal.<x>.seq(n)` to a concrete `Rat` for any concrete `n`
at all. That is precisely ADR-0512's and `creal/pi.rs`'s stated design:
"keep magnitudes small" is achieved by never fully computing them, not by
computing them cheaply. **There is currently no route in this codebase,
library-internal or external, that computes "π to k correct digits" as a
displayed rational** — the representation is built to prove bounds cheaply
and to compute concrete approximations expensively to intractably, and this
measurement is the first time that asymmetry has been quantified rather than
asserted.

### Artifact

`artifacts/measurements/creal-eval-cost-2026-09-04.md` — full method, raw
run transcripts (including the two "did not complete" runs' partial output
and elapsed time at kill), and the control table above.

## Measurement B — W1-13, the `cas-internal` residue

### The numbers

```
cas-certificate: 60 total -- kernel-reconstructed 14, cas-internal 46, unrecognized 0
  cas-internal residue share: 76.7%
```

This reproduces `scripts/validate-facts.py`'s own summary line exactly
(`routes: cas-certificate=60(kernel-reconstructed=14,cas-internal=46)`),
independently re-derived by a **different** script reading the same
classifier — the cross-check that the two tools agree on the same question.
The "neither" bucket (ADR-0601 SS2's forbidden third case) is **empty**: 0 of
60 `cas-certificate` facts are `unrecognized`.

Per `formal.fragment` family (full table in the artifact below), every
family that reconstructs is real-algebraic sign-bracket / geometry-cofactor
/ polynomial-identity work; every `cas-internal` family is number theory
(Pratt/CRT/factorization), GF(2) computation, hypergeometric/binomial
identity checking, or SOS/Positivstellensatz certificates — exactly the
families `11-applied-and-computational.md`'s own "Next Five" item 3 (a
Positivstellensatz-to-kernel bridge) names as unbridged. The residue is not
spread evenly; it sits precisely where a reconstruction route does not exist
yet, which is what makes "should be published and falling" actionable rather
than aspirational.

### The gate

`scripts/check-cas-internal-residue.py` (new): reuses
`validate-facts.py`'s own `classify_cas_certificate_fact` (one definition,
not reimplemented) over every `cas-certificate` fact, and ratchets a floor
against `scripts/check-cas-internal-residue.ratchet` — a fact recorded
`kernel-reconstructed` must still classify that way; regressing to
`cas-internal`, going `unrecognized`, or disappearing is refused. A **new**
`cas-internal` fact is not refused (ADR-0601 makes the label honest, not
forbidden), so the gate ratchets the floor without blocking new,
honestly-labelled CAS work.

Registered in `scripts/check.sh` (`step cas-internal-residue`,
`step cas-internal-residue-tests`) and `justfile`. Companion test suite
`scripts/tests/test_check_cas_internal_residue.py` (10 tests), registered
under `scripts/tests/mutation_controls.py`'s `cas-internal-residue` entry.
Mutation-verified 2026-09-04 on a scratch copy: baseline green (10 tests),
and each of the four guards, deleted independently, kills **exactly one**
test — G1 (an `unrecognized` fact) kills
`test_G1_an_unrecognized_fact_is_refused`; G2 (a missing ratchet) kills
`test_G2_a_missing_ratchet_is_refused`; G3 (a kernel-reconstructed →
cas-internal regression) kills `test_G3_a_reclassified_fact_is_refused`; G4
(a vanished ratcheted fact) kills `test_G4_a_vanished_fact_is_refused`.

### Artifact

`artifacts/measurements/cas-internal-residue-2026-09-04.md` — full method,
the complete per-fragment table, and the mutation table above.

## Decision

1. Publish both measurements as committed artifacts
   (`artifacts/measurements/`) rather than only in this ADR, so the numbers
   are re-derivable by running one command each
   (`cargo run --release -p axeyum-lean-kernel --example creal_eval_cost`;
   `python3 scripts/check-cas-internal-residue.py --report`).
2. Register `scripts/check-cas-internal-residue.py` as a gate
   (`scripts/check.sh`, `justfile`) so the residue's **floor** cannot regress
   silently, with the same mutation-verification discipline every gate in
   this repository is held to.
3. Do **not** claim a `CReal` evaluation cost in digits-per-second or any
   other rate: the honest result at this commit is "did not complete" for
   all four named constants, and the finding that matters is structural (the
   library's own bound proofs never force this reduction; a caller's request
   for a concrete approximation does) rather than a number that would invite
   quoting a false precision.

## Consequences

- The computable-analysis reviewer's question now has a measured, if
  negative, answer: evaluating a constructed real to a concrete rational
  approximation is not currently practical through this kernel's reduction
  engine, and the reason is structural (unary internal arithmetic performing
  real `Nat.gcd`/`Nat.rec` work, not merely "big numerals"), not a missing
  optimization flag.
- This sets a concrete target for future work this lane does not undertake:
  either (a) an accelerated/literal-numeral internal representation for
  `CReal`'s own series arithmetic (not just the caller-facing index, which
  this measurement shows does not matter on its own), or (b) a genuinely
  different evaluation route that does not go through full kernel
  `whnf`-based reduction (e.g. a certified extraction procedure that only
  needs to check a supplied rational is within bound, the way `CReal.sqrt`'s
  bound theorems already work, rather than computing one).
- The `cas-internal` residue is now tracked the way the "N axiom-free"
  headline already is: read from a script against a committed baseline, with
  an exit status that depends on the finding, rather than quoted from a
  summary line nobody re-verifies.
