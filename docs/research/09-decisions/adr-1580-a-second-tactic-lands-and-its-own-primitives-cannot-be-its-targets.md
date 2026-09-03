# ADR-1580: a second tactic lands, and a producer cannot retire its own primitives

Date: 2026-09-03
Status: Accepted
Lane: `ring-tactic-1`

Index-summary: `crate::ring` is the second tactic-layer producer in ADR-0601's
sense, beside `crate::linarith` (ADR-1576): a normalizer over ℕ (`+`, `*`,
`succ`, numerals) that parses both sides of a goal `t₁ = t₂` into a canonical
sum of monomials and, when they agree, **emits a kernel proof term** built
only from `add_assoc`/`add_comm`/`mul_assoc`/`mul_comm`/`left_distrib`/
`right_distrib` — lemmas already in `NatPrelude`. It retired **ten**
hand-written ring-rearrangement proofs in `nat_prelude` on the day it landed:
one declared theorem (`add_right_comm`) and nine private proof-construction
helpers — `nat_prelude/bezout.rs`'s `expand_scaled_right`, standing in for
`right_distrib` (see below), plus eight
independent hand-written copies of one duplicated four-term identity,
`(a+b)+(c+d) = (a+c)+(b+d)`, across `binomial.rs`, `div_mod_lemmas.rs`,
`finite_set.rs`, `fibonacci.rs`, `subset_sum.rs`, `rec_agreement.rs`,
`count_range_reversal.rs` and `eisenstein_lemma.rs`. Measured `--release`,
`--example ring_cost`, 200 emissions per shape: **0.7–2.4 ms per term end to
end**, kernel recheck included — the same order of magnitude as `linarith`'s
own datum, beside `ring_law_proof` in the cost model. This ADR records three
things the build forced, the first of which is new relative to `linarith`.
**(1) A producer's own primitives cannot be its retirement targets.**
`right_distrib` was the first target attempted; it is used by `ring`'s own
`Problem::distribute` to break a multi-summand sum across a product, so
routing its declaration through the producer tries to prove `right_distrib`
from itself and the kernel refuses with `UnknownConst` (the name does not
exist yet at that point in prelude construction). `add_right_comm` hit the
same trap in a subtler form — the emitter's own sort used it as a
convenience — and the fix there was different: derive the swap inline from
`add_assoc`/`add_comm` instead of depending on the lemma, which resolved the
circularity and made the emitter strictly more general. **(2) A retirement
target's arguments must be proved GENERICALLY, over fresh variables, and then
applied to the caller's actual (possibly non-ring) terms** — three of the
eight duplicated-identity call sites substitute `Nat.div`/`Nat.mod`
expressions for the identity's free variables, and normalizing those
literal substituted terms correctly declines `NonRing`; `prove_eq_at`
proves the identity over fresh `fvar`s (which the normalizer always sees as
opaque, in-fragment atoms) and instantiates the result by ordinary
application, which is sound for any argument regardless of what it is built
from. **(3) As with `linarith`, this producer scores zero on the
producer-contract system** (`ring-identity-v1.json`, born retired, ADR-1510
rule 1): the ring axioms and their consequences are among the parts of this
development finished first, by hand.

Index-status: Accepted

## Context

ADR-1576 landed `linarith` and put a `--tactic-layer producer--` pattern in
place: untrusted search (or, here, a deterministic normal-form computation —
the fragment has no ambiguity to search over), trusted checking through
`Kernel::add_declaration`. That ADR named the ring-rearrangement chain — the
second most common hand-proof shape in this library after order reasoning —
as the obvious next target, and estimated its scope: rearranging
`a·(b+c) + d = a·b + (a·c + d)` by `add_assoc`/`add_comm`/`mul_comm`/
`left_distrib` chains over ℕ, ℤ, ℚ.

Step 0 (grepping `nat_prelude` for three-or-more consecutive applications of
`add_assoc`/`add_comm`/`mul_comm`/`left_distrib`) found a strong, self-evident
signal for the retirement story: `nat_prelude/count_range_reversal.rs`'s
private helper `add_add_add_comm`, a 20–30-line hand-built chain proving
`(a+b)+(c+d) = (a+c)+(b+d)`, carried a doc comment naming FOUR other files
with "local copies" of the exact same identity — `div_mod_lemmas.rs`,
`binomial.rs`, `rec_agreement.rs`, `finite_set.rs`. A further search found
three more: `fibonacci.rs` and `subset_sum.rs` (named `add_regroup_four`) and
`eisenstein_lemma.rs` (`regroup_four`, `pub(super)` and already shared with a
second file). Eight verbatim-duplicated proofs of one identity, none of them
findable by name (`add_add_add_comm` and `add_regroup_four` are two different
spellings of the same convention, and every copy is a per-file-private `fn`
with no declaration a name search reaches) — exactly the "hiding place a name
search cannot find" pattern `finding-existing-lemmas.md` describes.

## Decision

### 1. A producer cannot retire its own primitives

The design's first candidate for the multiplication-distribution half of the
fragment was `nat_prelude/algebra.rs::declare_multiplicative_theorems`'s
`right_distrib` theorem — a 29-line chain (`mul_comm`/`left_distrib`/
`mul_comm`/`mul_comm`) that is exactly the shape ring exists to retire.
Routing it through `ring::nat::declare` built successfully and every unit
test passed — because every test builds against the **finished** prelude,
where `right_distrib` already exists. Retiring the actual declaration site
broke `build_nat_prelude` itself: `ring`'s own `Problem::distribute` calls
`d.lemma(self.prelude.right_distrib, ...)` to break a multi-summand
left-hand sum across a product, and at the moment `right_distrib`'s hand
proof is replaced by a call into the producer, that name does not exist in
the kernel's environment yet. The kernel correctly refused with
`UnknownConst`.

This is not a bug to patch around; `left_distrib`/`right_distrib` are
axiomatic to what `ring` computes, not consequences of it, so they cannot be
retirement targets for this producer under any implementation. The fix was
to find a **downstream consequence** of them instead:
`nat_prelude/bezout.rs`'s private `expand_scaled_right`
(`g·(a·mp+b·np) = (g·a)·mp + (g·b)·np`, 47 lines, `left_distrib`/
`mul_assoc`) stands in as the multiplication-distribution retirement target,
and it is declared well after `algebra.rs`'s block, so there is no
circularity.

`add_right_comm` hit a subtler version of the same trap: it is not one of
`ring`'s AXIOMS, but the emitter's own `sort_items` used it as a
**convenience** for every non-head adjacent transposition. The fix there was
different — and better — than finding a substitute target: derive the swap
inline from `add_assoc`/`add_comm`/`symm`(`add_assoc`) on the spot, exactly
mirroring the three-step algebraic derivation `add_right_comm`'s own hand
proof already used. `add_right_comm` itself then retires cleanly, and the
emitter is strictly more general as a side effect — it no longer assumes
`Nat.add_right_comm` exists at all, which matters for a future carrier whose
prelude might not have it.

**The general rule, worth carrying to the next tactic-layer producer:** a
producer's own dependency list is not just documentation, it is a
constraint on what that same producer can retire, and the constraint bites
in exactly the place a test suite built against the finished prelude cannot
see it — the retirement SITE, mid-build, not the retirement's behavior once
everything exists.

### 2. A retirement target's arguments must go through the generic route

Three of the eight duplicated-`add_add_add_comm` call sites are inside
`nat_prelude/div_mod_lemmas.rs`, and its own callers substitute
`Nat.div`/`Nat.mod` expressions for the identity's `a`/`b`/`c` parameters —
this file is *about* division and remainder, so that is exactly what its own
call sites look like. `ring::nat::prove_eq(d, p, start, target)` on the
literal substituted terms correctly declines `NonRing`: the normalizer
recurses into `add`/`mul` structure looking for the fragment's operators, and
a `div`/`mod` subterm anywhere in that structure genuinely is outside what it
can see. That is sound, not a bug — but it makes the naive retirement
(normalize the caller's actual arguments) fail exactly at the one call site
whose arguments are compound.

The fix is `ring::nat::prove_eq_at`: prove the identity **generically**, over
fresh `fvar`s the normalizer always treats as opaque in-fragment atoms
(never inspecting their own structure), then wrap the generic proof in
`arity` lambdas and apply it to the caller's actual arguments via ordinary
Pi-application. The kernel's application typing does not need to inspect
`div`/`mod` at all — a Pi-typed function applied to any `Nat`-typed argument
type-checks regardless of what that argument is built from. This is the same
"prove once, generically, apply everywhere" shape `theorem`/`declare` already
use for a target's own universal quantifiers; `prove_eq_at` is that same
move made available to an ordinary term-construction helper whose caller
supplies the instantiation.

All eight duplicated-identity retirement sites, plus `expand_scaled_right`,
route through `prove_eq_at` uniformly rather than only the three that are
currently known to need it — a future caller passing a compound argument at
any of them should not silently reintroduce this failure mode.

### 3. This producer also scores zero on the producer-contract system

As with `linarith` (ADR-1576 §3), `artifacts/autogenesis/producer-contracts/
ring-identity-v1.json` is written, validated, and **born retired** under
ADR-1510 rule 1. Its live population is zero: reading all 245 open
`Mathlib v4.30 source proposition` titles, the 169 `Nat.*`-titled facts are
almost entirely about `sqrt`, `gcd`, primality, `testBit`, `findGreatest`,
`nth`, and order (`le`/`lt`) — not one is a bare `+`/`*` rearrangement. The
ring axioms and their immediate consequences are among the parts of this
development finished first, by hand, exactly like linear arithmetic was.
The contract sizes dispatch and cannot see the ten retired proofs; that gap
is the same one ADR-1576 recorded, now confirmed to recur on a second
producer rather than being an artifact of linear arithmetic specifically.

## The cost datum, beside `linarith` and `ring_law_proof`

Measured `--release`, `cargo run --release -p axeyum-lean-kernel --example
ring_cost`, 200 emissions per shape, prelude built once per shape:

| goal shape | search + emit | + kernel recheck |
| --- | ---: | ---: |
| `Nat  (x+y)+z = (x+z)+y` | 0.722 ms | 1.092 ms |
| `Nat  (a+b)+(c+d) = (a+c)+(b+d)` | 1.315 ms | 2.121 ms |
| `Nat  (a+b)*c = a*c+b*c` | 0.754 ms | 1.079 ms |
| `Nat  g*(a*mp+b*np) = (g*a)*mp+(g*b)*np` | 1.534 ms | 2.383 ms |

A single unpinned run on a shared box, same caveat as `linarith`'s own
datum: order-of-magnitude, not a ratchet baseline. The shape is the same
too — the multiplication-distribution shapes cost roughly double the
pure-addition ones, tracking `ring`'s own two-machinery split (the `+`
normalizer reuses `linarith`'s bubble-sort pattern almost verbatim; `*`
needs the additional `distribute`/`distribute_single`/`combine_items`
recursion).

**Tokens against lines retired, for this lane.** The ten retirement sites
total roughly 350 hand-written lines (two theorems at 19 and 47 lines, eight
duplicated-identity copies averaging ~40 lines each including their
doc comments), replaced by a shared ~700-line producer plus a few lines per
call site. As with `linarith`, the honest framing is a break-even, not a
tokens-per-theorem win on this session alone: the producer is capex, the ten
retirements are the first instalment, and the return compounds only on the
next hand-written ring chain somebody would otherwise write by hand.

## Consequences

- `ring::nat::Decline` has no `NoCertificate`/`SearchBudget` analog: within
  the fragment (no intra-monomial factor reordering — see below) the
  normalizer is a complete decision procedure, so a false goal gets the
  positive `NotAnIdentity` rather than "search exhausted". `NonRing`
  (`div`/`mod`/ℕ's truncated `sub`) and `CoefficientTooLarge` (a repeated-`+`
  count, or a numeral product, above `MAX_COEFF = 4`) are the other two
  declines.
- **A sound, documented incompleteness: no intra-monomial commutativity.**
  Two monomials compare equal only when their factor lists are literally the
  same sequence in the same order; `x*y` and `y*x` normalize to different
  keys and the procedure declines `NotAnIdentity` rather than proving them
  equal. None of the ten retirement targets need it — every product in this
  batch pairs a fixed left-side factor against a fixed right-side factor in
  one consistent construction order, never two independently-built products
  needing to be reconciled — but it is a real edge, pinned by
  `commuting_two_products_is_a_sized_negative` rather than left as an
  unstated gap. Adding it needs the same three-step
  `mul_assoc`/`mul_comm`/`symm(mul_assoc)` swap `sort_items` already derives
  for `add`, applied to a monomial's own factor list; not built here because
  none of the ten targets need it and a speculative capability with no test
  demonstrating it is exercised is exactly the shape this repository asks
  contributors to avoid.
- **Every proof-construction step leans on raw `ι`-reduction wherever
  possible, exactly as `linarith`'s ℕ fragment does.** `Nat.mul`/`Nat.add`
  both recurse on their second argument, so `mul it (numeral k)` fully
  reduces to a nested-`add` chain regardless of what `it` is (even a
  compound monomial term) — `Problem::scale_item` bridges this with `d.refl`
  rather than a lemma. What this does *not* give for free: `add zero it` for
  symbolic `it` is stuck, so the growing accumulator inside `scale_item`
  still needs an explicit `reassoc` proof at every step.
- ℤ and ℚ are not built. The design brief scoped them as a further slice
  (`neg`/`sub` as `add(neg)` over ℤ, five more retirements each); this lane's
  ten ℕ targets, their tests, the two circularity findings above, and the
  cost/contract instruments consumed the available session. Building ℤ means
  re-deriving the same normalizer over `IntDev`/`IntPrelude` — the shape is
  established, not the code.

## Alternatives considered

- **A single normalizer shared between the outer sum and a monomial's own
  factor list**, parameterized over the operation (`+`/`*`). Rejected after
  writing both `reassoc`/`reassoc_mul` almost verbatim: the two differ in
  exactly one place that matters — `sort_items` (the outer sum) needs to
  derive its non-head swap WITHOUT `add_right_comm` (§1 above), while a
  hypothetical `sort_factors` for `*` would need the same derivation without
  a `mul_right_comm` this prelude does not have at all. Abstracting the
  shared skeleton would have hidden that both are independently reproducing
  the same three-step trick for a different reason, which is worth keeping
  visible.
- **Building `sort_factors` (intra-monomial commutativity) preemptively**,
  since it costs little more than `sort_items` once written. Deliberately
  not done: no test would exercise it honestly (none of the ten targets need
  it), and an unexercised capability is a liability, not a feature, per this
  repository's own standing rule about mutation testing measuring only the
  guards a suite has.

## Cross-references

- [ADR-1576](adr-1576-a-tactic-is-a-producer-and-its-return-is-measured-in-retired-proofs.md)
  — the first tactic-layer producer (`linarith`), the template this ADR
  follows and the two findings above extend.
- [ADR-0601](adr-0601-three-producers-one-trust-anchor.md) — producers behind
  one trust anchor. `ring` is the fifth producer and the second on the tactic
  layer.
- [ADR-1510](adr-1510-a-contract-is-sized-by-the-frontier-and-a-decline-dies-with-its-fact.md)
  — a contract is sized by the frontier and retires when the population
  empties. `ring-identity-v1` is the second contract born retired.
- [07-the-cost-model-and-pareto-position.md](../../formalized-math-2026-08/07-the-cost-model-and-pareto-position.md)
  §3 — `ring_law_proof` and `linarith`'s own datum are what this one sits
  beside.
