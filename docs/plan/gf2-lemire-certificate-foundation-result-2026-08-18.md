# GF(2) Lemire certificate foundation result

Date: 2026-08-18
Branch: `agent/gf2/lemire-proof`
Scope: CAS/evidence foundation, not a universal proof

## Verdict on the starting machinery

Axeyum had enough general finite-field arithmetic to test a candidate, but not
enough machinery to make this research trustworthy or scalable.

- `axeyum-cas::gfp` represented every binary coefficient as `i128`, repeated
  general modular arithmetic, had no operation budget, and took about 6.45 s in
  release to test the known degree-400 candidate.
- Its public result was a Boolean/`Option`, not irreducibility evidence. Factor
  re-multiplication does not prove the emitted factors irreducible.
- Invalid-modulus behavior contradicted the module's no-panic claim, and some
  empty results conflate no solutions with unsupported/failure.
- No IR sort, SMT reader/writer, solver route, model lift, evidence envelope,
  kernel term, ledger fact, or script consumed `gfp` irreducibility.
- Bit-vector multiplication is not a substitute: it has carries, whereas
  `GF(2)[x]` multiplication is carryless. Existing XOR Gaussian elimination
  covers linear parity, not modular polynomial multiplication, GCD, or Rabin's
  nonlinear criterion.

The correct first extension was therefore a CAS-local evidence boundary, not a
premature finite-field SMT surface.

## Landed foundation

Commit `81321fc65` adds normalized little-endian bit-packed polynomials,
carryless arithmetic, explicit input/intermediate/Frobenius/work ceilings, and
typed declines. Its untrusted producer emits a Rabin certificate containing:

- every identity `r_(i-1)^2 = q_i f + r_i` through `r_n = x`; and
- a Bezout identity for `gcd(f, r_(n/p)+x)=1` for every distinct prime divisor
  `p` of `n`.

The primary checker derives the complete prime-divisor set and checks every
identity without calling the producer's irreducibility verdict.

Commit `98f2d953f` adds a second checker with a different arithmetic
implementation: dense byte coefficients and direct schoolbook operations. It
does not reuse the packed add, square, multiply, divide, GCD, or producer path.
The same commit adds canonical JSON with strict format/statement identities,
lowercase fixed-width coefficient words, byte and algebraic limits, unknown
field rejection, byte-for-byte canonical re-rendering, exact half-degree shape
checking, and the standalone `axeyum-gf2-check` dual checker.

Commit `b678ec7e6` adds a fail-closed explicit-polynomial producer. It requires
strictly increasing canonical exponents, refuses reducible or out-of-shape
candidates, writes through a same-directory temporary file, and refuses to
overwrite an existing artifact.

Commit `3718aab11` commits and gates the known witness

```text
x^400 + x^5 + x^3 + x^2 + 1.
```

The canonical artifact is 188,458 bytes with SHA-256
`30ae3f3377e9c66c6c2ecf00af6e4fade262b80ecd0e6a8fe4d7f597042383d5`.
Both `just check` and the shell fallback run the standalone dual checker.

## Assurance actually run

- Every monic polynomial through degree 10 agrees among the new producer, the
  old general-field Rabin test, and an independent test-only `u128`
  trial-division oracle.
- Cross-word arithmetic and division reconstruction tests pass.
- Mutated quotient, remainder, prime-divisor population, and Bezout data are
  rejected. A mutation of the committed degree-400 serialized artifact is also
  rejected by an algebraic identity failure.
- Noncanonical JSON, unknown fields, degree drift, theorem-shape drift,
  noncanonical hex, invalid provenance labels, and resource exhaustion fail
  closed.
- The standalone producer composes with the standalone checker and rejects an
  overwrite attempt.
- The warmed release producer-plus-primary-checker degree-400 regression is
  below the test harness's 10 ms resolution; the initial generic release path
  was about 6.45 s.
- Complete CAS validation after the artifact layer: 657 library tests pass, two
  are intentionally ignored, every integration/doctest group passes, all-target
  Clippy passes with warnings denied, formatting passes, and links pass.
- The first topic-branch push additionally passed the repository-native
  979-second pre-push gate: compile, format, corpus status, workspace and full
  solver unit sweeps, kernel suites, capability frontier, and selected
  integrations.

These checks establish a bounded witness infrastructure and one checked degree.
They do not establish the conjecture through degree 400 unless every degree has
its own admitted artifact, and they do not establish the universal theorem.

## Exact theorem program

The paper's target is the non-strict statement

```text
for every n >= 1, exists irreducible f in GF(2)[x]
with deg(f)=n and deg(f-x^n) <= floor(n/2).
```

The strict social-post wording is false at degree 2. Reciprocity converts the
target exactly into existence of a degree-`n` irreducible congruent to 1 modulo
`x^ceil(n/2)`. This is the first lemma of the planned short paper.

The remaining mathematical obligation is positivity in that identity ray class
at the fixed-field half-degree boundary. General large-field short-interval
theorems and crude absolute Hayes-class error bounds do not supply it. The next
theoretical target is an exact recurrence or cancellation argument from Gao's
Hayes-class/group-algebra formula at degrees `2 ell` and `2 ell+1`.

## Next execution boundary

1. Add deterministic half-degree candidate enumeration and sharded range
   manifests whose output is accepted only after canonical dual checking.
2. Run bounded, thermally conservative shards on s1, s4, s5, s6, and s7; retain
   explicit missing/failed degrees rather than completion credit.
3. Use the counts and character data to test proposed exact recurrences, not as
   a substitute for proof.
4. Formalize reciprocity and the eventual positivity lemma through the Lean
   kernel route; only then create a universal established fact in the ledger.
5. Add a finite-field SMT surface only if a real query consumer justifies its
   total semantics, model lifting, replay, and proof evidence.
