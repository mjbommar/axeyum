# ADR-0472: ℂ is a pair setoid over `CReal`, and its missing order is refuted rather than omitted

Status: accepted
Date: 2026-08-18
Index-summary: ℂ as a pair of constructed reals under a componentwise defined equality costs **zero** trusted declarations and satisfies 9 of the `Real` package's 22 laws; the other 13 are not deferred but **jointly refutable**, and `Complex.no_compatible_order` proves it — so "ℂ is not ordered" is a result of the module rather than a scoping note

## Context

[ADR-0468](adr-0468-real-is-constructed-as-a-setoid-over-the-rationals.md) built
ℝ as a Bishop setoid of regular ℚ-sequences at zero trusted declarations, and
explicitly **scoped ℂ out**, with a finding: nothing in the solver needed it, and
the only shipped complex arithmetic is exact ℚ(i) in
`axeyum-cas/src/geometry_certify.rs`, which wants a ring over ℚ rather than over
ℝ — so "ℚ(i) before ℂ, if either"
(`docs/plan/status/reals-design.md`).

That deferral is about *demand*, not about feasibility, and it leaves the
foundational tower — integers, reals, complex — with its top floor missing.
Re-measured 2026-08-18 before starting: ℕ, ℤ, ℚ, `logic` and `string` all report
a trusted surface of 0, `CReal` likewise, and no `Complex` declaration existed in
the kernel.

Two questions had to be closed before writing a line:

1. **What carries the equality?** `CReal`'s whole point is that `Eq CReal` is not
   equality of reals — `CReal.Equiv` is, and it is a `Prop`-valued *definition*,
   chosen because a Cauchy quotient needs `Quot.sound` and Dedekind cuts need
   `propext` + `funext`, none of which this kernel has. Anything built over
   `CReal` inherits that constraint whether it wants to or not.
2. **What does "ℂ is not ordered" mean, precisely, in a file?** The
   `ArithPrelude` `Real` package is an *ordered* commutative ring — 22 laws — and
   simply declaring nine of them and stopping is indistinguishable from a
   development that ran out of time.

## Decision

**ℂ is `Complex.mk : CReal → CReal → Complex`, a one-constructor inductive, with
equality the *defined* relation**

```text
Complex.Equiv z w := CReal.Equiv (re z) (re w) ∧ CReal.Equiv (im z) (im w)
```

**and it satisfies exactly the nine equality-only laws of the `Real` package. The
other thirteen are refuted, in-kernel, by `Complex.no_compatible_order`.**

Three sub-decisions follow from that sentence.

### 1. A pair, not a quotient and not a polynomial ring

`Complex` is the product carrier written directly. The alternatives were priced
and rejected in **Alternatives** below; the decisive point is that a pair
inherits `CReal`'s escape from `Quot.sound` for free, because the quotient is
never taken at either level. `Complex.re` and `Complex.im` are large-elimination
projections out of a `Type 0` inductive, so `re (mul z w)` δι-reduces to its
component formula and every law can be *stated* about `Complex` while being
*proved* about `CReal`. That reduction is what makes the whole module cheap.

### 2. Five congruence obligations, and no order to congruence over

Every operation owes an `Equiv`-congruence, exactly as ADR-0468 counted for ℝ:
`add_congr`, `neg_congr`, `mul_congr`, `conj_congr`. `Complex.Equiv`'s own
`refl`/`symm`/`trans` come componentwise from `CReal`'s and cost nothing.

There is deliberately **no** `le_congr`/`lt_congr` here, because there is no `le`
and no `lt` — see 3.

### 3. The absent order is a theorem, not a gap

```text
Complex.no_compatible_order :
  ∀ (le lt : Complex → Complex → Prop),
    (∀ x, le x x) →
    (∀ x, Not (lt x x)) →
    (∀ x y z, le x y → lt y z → lt x z) →
    (∀ x x' y y', le x x' → le y y' → le (add x y) (add x' y')) →
    (∀ a b c e, Equiv a b → Equiv c e → le a c → le b e) →
    (∀ x, le zero (mul x x)) →
    lt zero one →
    False
```

Seven hypotheses, all of them shapes the `Real` package (or, for `le_congr`, the
setoid's equality slot) already states. The proof is four steps and one witness:
`sq_nonneg I` gives `0 ≤ I·I`; `Complex.I_sq` rewrites that to `0 ≤ −1`;
`add_le_add` with `le_refl 1` gives `1 + 0 ≤ 1 + (−1)`, i.e. `1 ≤ 0` after
`add_zero`/`add_neg`; and `lt_of_le_of_lt` with `0 < 1` gives `1 < 1`, which
`lt_irrefl` refuses.

**No classical reasoning is involved.** The term is direct; `¬¬P → P` does not
exist in this logic prelude and is not needed. Quantifying over the two relations
is what makes it a statement about ℂ rather than about the particular order this
module might have picked.

The companion check is in `complex_ring_witness`: `Complex.le` and `Complex.lt`
must **not** be declared, and the witness fails if either is — the theorem and a
declared order cannot both stand.

## Evidence

Measured 2026-08-18 on this host, `cargo run -q -p axeyum-lean-kernel --example
complex_ring_witness`:

- **39 named declarations**, every one a checked `Definition`/`Theorem`/
  inductive with an **empty** `Kernel::axiom_footprint`;
- **trusted surface of the whole environment = 0** (`Axiom` + `Opaque` +
  `Quotient`, not `Axiom` alone — `Opaque` has no proof body and `Quotient`
  admits `Quot.sound`). ℂ over ℝ over ℚ over ℤ assumes nothing;
- **9 of 9** ring laws proved, the count read out of the kernel through
  `ComplexPrelude::ring_laws` and nowhere else;
- carrier inhabited (`ofReal`), `Equiv` discriminating on **both** components
  (`not_zero_one`, `not_zero_I`), `mul` pinned on the embedded ℝ (`ofReal_mul`)
  and at `I` (`I_sq`), order refuted (`no_compatible_order`), no order declared.

Mutation evidence — the checks are load-bearing, not decoration:

| mutation | result |
|---|---|
| `Complex.mul`'s real part loses its `neg` (i.e. `ac + be`) | build **fails**; the ring calculus refuses `I_sq` |
| cancellation pass removed from the normalizer | build **fails**; `add_neg` and `mul_conj` refuse |
| `Complex.le` declared | `complex_ring_witness` exits **1** and all seven fact rows exit non-zero; **exactly one** test dies (`no_order_relation_is_declared_on_complex`) |
| the normal-form comparison in `ring_proof` deleted | **exactly one** test dies (`the_ring_calculus_refuses_a_false_identity`) |
| `mul_congr`'s inner `neg_congr` given its arguments in the wrong order | the run is killed by the cgroup memory ceiling — see below |

Two of those mutations are caught, but **badly**. Swapping two arguments of a
`CReal` congruence, or dropping the `neg` from `Complex.mul`'s real part, leaves
a proof whose type differs from the goal only *inside* the arguments of
`CReal.mul`/`CReal.add` — and `def_eq` responds by δ-unfolding both into their
representative sequences. Measured: **12 GB RSS and >15 minutes of CPU** before
the run was killed, against 45 seconds for the healthy build. The rejection is
correct and the mutation is detected either way, but the *shape* of the failure
is a resource exhaustion rather than a type error, and on this fleet that is a
box-killer rather than a red test. It is a property of the kernel's `def_eq` on
setoid carriers, not of ℂ, and it will bite every future development over
`CReal` the same way. Recording it here because the obvious workaround —
`scripts/cargo-serialized.sh`'s `MemoryMax` — is what turned it into a clean
non-zero exit rather than a crashed host.

### The ring calculus is the reusable part

Every ℂ law reduces to two `CReal.Equiv` obligations that are *algebraic* — the
real parts of `(z·w)·v` and `z·(w·v)` are the same four monomials in a different
order — so they are decided rather than hand-derived.
`crates/axeyum-lean-kernel/src/complex/ring.rs` normalizes a `CReal` expression
to a **sorted multiset of signed monomials with opposite pairs cancelled** (the
free commutative ring on the atoms, ℤ coefficients, written additively) and emits
the `Equiv` proof; two expressions are `Equiv` iff their normal forms agree.

It **declares nothing** — every function returns a proof term, in the style of
`shifted_bound_le` and `rsum_perm` — so the `CReal` namespace is untouched and
the trusted surface is unchanged by construction. `add` and `mul` are the same
commutative monoid, so the reassociation machinery is written once against an
`Op` tag; it is `rsum_perm`/`iprod_perm` transcribed one level up and over a
*defined* equality, which is the transcription ADR-0468 predicted would be
needed. Like them, it **panics** on a non-identity rather than handing the kernel
a term it will reject a thousand nodes deep.

## Alternatives

- **`CReal[X]/(X²+1)` as a quotient of a polynomial ring** — the textbook
  algebraic construction, and closed here for ADR-0456's reason: the quotient
  needs `Quot.sound`. A pair is the same object with the quotient never taken.
- **ℚ(i) first, per ADR-0468's deferral.** Still the right thing for
  `geometry_certify`, and untouched by this ADR — but it is a *different* object
  (a ring over ℚ, not over ℝ) and it does not supply ℂ. The deferral's reasoning
  was about which consumer was waiting, and consumer demand is not the metric
  this tower is built against.
- **Defining `Complex.le` as the lexicographic or the real-part order.** Both
  satisfy `le_refl`, `le_trans` and `add_le_add`, and neither satisfies
  `sq_nonneg` — so declaring one would put a relation in the kernel that
  `no_compatible_order` refutes as an *ordered ring* order while quietly reading
  as one. Rejected: an order that is not compatible with the ring structure is
  worse than no order, because every consumer will assume it is.
- **Stating "ℂ is not ordered" in prose.** Rejected on this repository's standing
  evidence: an omission and a refutation look identical from outside, and the
  witness's exit status must depend on what it found.
- **Hand-deriving each ring law from the `CReal` laws.** Tried in outline for
  `mul_assoc` — eight monomials across two nestings — and abandoned. This is the
  class of proof that goes wrong silently, and a decision procedure removes the
  class rather than the instance.
- **Collecting coefficients in the normal form** (so `x + x` becomes `2·x`).
  Rejected: nothing here needs it, and it drags ℕ-arithmetic into a ring proof.
  Opposite pairs *are* cancelled, which is what `mul_conj`'s imaginary part
  needs.

## Consequences

**Easier.** The foundational tower ℤ → ℚ → ℝ → ℂ is complete and axiom-free end
to end. The ring calculus is reusable for any future `CReal`-valued algebraic
identity, and is the obvious basis for a ℚ(i) or a matrix development. `normSq`
lands in `CReal`'s existing nonneg cone, so metric statements about ℂ have a home
without inventing an order.

**Harder / not attempted.** No inverse, no division, no `√`, no completeness, no
algebraic closure, and no `Complex.abs` — `abs` needs a square root, which needs
completeness, which is its own ADR. None of these is one of the nine.

**Revisited when** a consumer needs ℂ *inside* a reconstruction: ADR-0457's
ordered-ring telescope is parameterised over an **ordered** ring, and ℂ is not
one, so a ℂ-valued reconstruction needs a plain-commutative-ring telescope. That
is a real piece of work and it is not started; `no_compatible_order` is the
precise statement of why the existing telescope cannot simply be instantiated.
