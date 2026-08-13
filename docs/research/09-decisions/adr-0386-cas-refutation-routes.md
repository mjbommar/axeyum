# ADR-0386: Two CAS-backed refutation routes in the auto dispatch, certified by an independent expander

Status: proposed
Date: 2026-08-12

## Context

`crates/axeyum-cas` has existed since ADR-0301 (a proof-carrying CAS that
"lowers to the decidable core to certify") and had grown to ~47 000 lines across
27 modules — exact multivariate polynomials (`MvPoly`), Gröbner bases, Sturm
sequences, number theory — **with no dependents anywhere in the workspace**.
Nothing in the solver used it.

Meanwhile the solver's own identity reasoning was `src/term_identity.rs`, 161
lines, self-described as "deliberately narrow": a reflexive match and an `ite`
constant-condition simplification. Nonlinear integer goals went to
`nia-linearize` / `nia-bounded-blast` / `int-blast-ladder`, and the ladder's
answer on a symbolic-divisor question is a bounded-width `unknown`.

Four measurements taken on this branch before any change (transcripts in
`docs/plan/proof-approaches-2026-08-12/route-b/`, re-measured 2026-08-12 at 15 s
and 20 s budgets):

| query | verdict before | route that declined |
|---|---|---|
| `a ≥ 2 ∧ a·p = 1` | `unknown(Timeout)` 15.00 s | `int-blast-ladder`: "no model within the bounded integer width 32" |
| `a ≤ −2 ∧ a·p = 1` | `unknown(Timeout)` 15.00 s | same |
| `a ≥ 2 ∧ b ≥ 2 ∧ a·b·q = 1` | `unknown(Timeout)` 15.00 s | same |
| `(a+b)² ≠ a²+2ab+b²`, beside a `div` conjunct | `unknown(Timeout)` 15.00 s | same |
| `(a + b/2)² ≠ a² + ab + b²/4` over ℝ | `unknown(Timeout)` 15.44 s | `nra-real-root: not-applicable`, then the lazy NRA budget |

The first three are the "units" question — *no integer of absolute value ≥ 2
divides 1* — which a first-year student closes in one line. The workaround found
during that session was to restate the goal in the "witness direction", i.e. a
user working around a tool gap.

The honest counter-measurement matters too: a **standalone** polynomial-identity
disequality was already decided, fast, by `int-real-relax` (integer queries) or
`nra-real-root` (real queries) — `(a+b+c+d)²`, `(a+b)⁵`, Sophie Germain, and a
degree-9 three-variable identity all landed `unsat` in 1–5 ms. The gap is not
"identities"; it is identities that sit *beside* something the real relaxation
will not take (an underspecified `div`, a rational division), plus the whole
units/divisibility family.

## Decision

**Wire `axeyum-cas` into `axeyum-solver` as a `full`-gated dependency and add two
CAS-backed refutation routes to the auto dispatch, each of which emits a
certificate that a checker with no CAS dependency re-derives from the original
assertions before the verdict is returned.**

1. **`crates/axeyum-solver/src/cas_poly.rs` — untrusted fast search.**
   Abstracts every subterm outside the `+ − × ÷ᶜ` fragment into an opaque atom
   keyed by `TermId`, normalizes what remains with `MvPoly` over exact ℚ, and
   reads a refutation off the normal form.

   * `cas-identity-refuter`: an asserted `not (= lhs rhs)` over `Int`/`Real`
     whose two sides have the *same* polynomial normal form is unsatisfiable.
   * `cas-int-units`: an asserted `Int` equation whose normal form is `k·m = c`
     for a single monomial `m` is refuted by one of three exact facts —
     `k ∤ c` (the left side only hits multiples of `k`); `c ≠ 0` and an asserted
     bound puts a factor of `m` outside `[−|c/k|, |c/k|]` (each factor of a
     nonzero integer divides it, so `1 ≤ |factor| ≤ |c/k|`); or `c = 0` and every
     factor is bounded away from zero.

2. **`crates/axeyum-solver/src/cas_certificate.rs` — trusted small checking.**
   Imports `axeyum_ir` and the certificate types, and nothing else. It re-scans
   the top-level conjuncts, re-expands the arithmetic with its own flat
   sort-and-merge expander (monomials keyed by `TermId`, its own atom
   abstraction, no shared code with `MvPoly`), and re-reads every cited integer
   bound off the conjunct that is claimed to assert it. A refutation whose
   certificate does not re-check is **discarded** — reported as
   `CasOutcome::VerifierRejected`, never returned as `unsat`.

   `MvPoly` is therefore a search engine in this dispatch, not an oracle. This is
   ADR-0301's "reduce-to-decide" with the decidable core being the exact monomial
   normal form itself, which is what ADR-0301's Phase C0 already names as the
   certifier ("the normal form *is* the witness").

3. **Placement.** Both routes run immediately after `term-identity-refuter`, at
   the top of `check_auto_with_recorder`, gated on `has_int || has_real`. They
   are exact, deterministic, and bounded by node/monomial/atom/depth ceilings
   rather than a clock, so they cost microseconds and cannot consume a budget.
   The existing route ordering is otherwise untouched.

4. **Decline recording.** A route that had a candidate shape and could not close
   it records a decline with a reason (`cas-int-units: declined (incomplete:
   normalized to k·m = c, but no asserted bound puts a factor of m outside the
   divisors of c/k)`). A route with **no** candidate records nothing, so the
   traces of unrelated queries are byte-identical to before. This keeps the
   diagnosability rule that `record_nia_decline` exists to enforce, without
   appending two entries to every trace in the system.

5. **`unknown` stays first-class.** Every decline path returns "no decision" and
   lets the existing engines run; no CAS path can raise an error or a verdict it
   did not check.

## Evidence

Before/after, same queries, same 15 s budget, `check_auto_explained`:

| query | before | after |
|---|---|---|
| `a ≥ 2 ∧ a·p = 1` | `unknown(Timeout)` 15.00 s | `unsat` 79 µs, `cas-int-units` |
| `a ≤ −2 ∧ a·p = 1` | `unknown(Timeout)` 15.00 s | `unsat` 79 µs, `cas-int-units` |
| `a ≥ 2 ∧ b ≥ 2 ∧ a·b·q = 1` | `unknown(Timeout)` 15.00 s | `unsat` 97 µs, `cas-int-units` |
| identity beside a `div` conjunct | `unknown(Timeout)` 15.00 s | `unsat` 155 µs, `cas-identity-refuter` |
| rational-coefficient identity over ℝ | `unknown(Timeout)` 15.44 s | `unsat` 139 µs, `cas-identity-refuter` |

Previously-decided cases are not regressed and mostly get faster (the identity
route runs ahead of the relaxation): mixed array+identity 7.91 ms → 192 µs,
UF-atom identity 3.53 ms → 136 µs, degree-9 three-variable identity 5.05 ms →
7.34 ms.

Negative controls (each must decline; verbatim outcomes recorded in
`crates/axeyum-solver/tests/cas_bridge_routes.rs`): a near-miss identity
(`3ab` for `2ab`) stays `sat`; `div x y ≠ div y x` stays `sat` (distinct
subterms must not collapse onto one atom); `(a/b)·b ≠ a` with `b = 0` stays
`sat` (a variable divisor is never folded); `a ≥ 1 ∧ a·p = 1` stays `sat` (the
bound is *at* the divisor limit, not past it); `a ≥ 12 ∧ a·s = 12` stays `sat`
(one off the limit — this pins the `>` where an off-by-one would produce a wrong
`unsat`); `2ab = 4` stays `sat`; a zero product with a possibly-zero factor stays
`sat`; a bound on an unrelated symbol is not read as a bound on a factor. Four
tamper tests confirm the checker rejects a truncated normal form, a foreign
assertion, an inflated bound, a misattributed bound source, and a relabelled
refutation kind.

Gates at the time of the decision: `--lib --features full` 1121 passed;
`corpus_regression` 1 passed; `progress_frontier` 9 tests, 8 passed with
`frontier_bv_reduction` failing — reproduced identically with the CAS dispatch
hook compiled out (`if false && …`), so pre-existing/environmental on a shared,
loaded box, and `bv_reduction` is a pure QF_BV instance the routes never see.

## Alternatives

- **Put the routes in the nonlinear-integer tail, before `int-blast-ladder`.**
  Rejected: it closes the units cases but leaves the real-arithmetic identity gap
  (`nra` path) open, and it makes a microsecond-scale exact check wait behind
  routes that spend the budget.

- **Reuse `MvPoly` in the checker.** Rejected: then a `MvPoly` canonicalization or
  overflow bug is a wrong-`unsat` bug. The whole value of the second expander is
  that it is a different algorithm written against the same specification.

- **Trust the CAS and skip certificates.** Rejected outright; this is exactly the
  "oracle laundering" ADR-0301 alternative (D) forbids, applied internally.

- **Give `cas-*` a wall-clock budget.** Rejected: determinism is a public API
  promise. The ceilings are node, monomial, atom and depth counts, so the same
  query always gets the same answer.

- **Record a decline unconditionally.** Rejected: it would append two entries to
  every arithmetic trace in the system and churn the trace-asserting suites,
  for no diagnostic gain on queries the routes never looked at.

## Consequences

- `axeyum-cas` has its first dependent. The CAS is now on a path where each new
  capability (multivariate GCD, factorization, Gröbner cofactors) has a solver
  route waiting for it, rather than accumulating unused surface.
- The certificate format is the polynomial normal form over `TermId`-keyed
  monomials (`AtomPoly`), which is checkable by ~250 lines that need only the
  arena. A Gröbner-cofactor certificate for ideal-membership refutations is the
  natural next artifact under the same discipline, and it re-checks the same way
  (multiply the cofactors back out and expand).
- `term_identity.rs` is *not* removed: its `ite`-simplification class is not
  polynomial, and it still runs first. The reflexive class over arithmetic sorts
  is now also covered by the CAS route, which is a deliberate overlap, not a
  duplicate.
- The abstraction is conservative in exactly one direction (over-abstraction
  makes a refutation fail to fire, never fire wrongly); the unsound direction —
  collapsing two different subterms onto one atom — is prevented structurally by
  hash-consing and is pinned by a negative-control test.
- Revisit when: an identity refutation is wanted for a *non-polynomial* fragment
  (transcendental heads live only in `axeyum-cas` per ADR-0301, and lowering them
  needs a separate ADR), or when the units route wants factorization to handle
  `(a+1)·p = 1`, which the current single-monomial restriction declines.
