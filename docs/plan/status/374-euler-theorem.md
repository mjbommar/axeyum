# 374 — Euler's theorem (a^phi(n) = 1 mod n)

<!-- plan-section: lane-status -->

Status: PARTIAL — the largest verified piece landed, precise handoff below.
The full theorem is NOT closed.

## The ask

Prove `a^phi(n) = 1 (mod n)` for `gcd(a, n) = 1`. ADR-0716 named it the
second-highest-yield remaining number-theory target on the grounds that
"both residue-permutation ingredients are already landed":
`Int.euler_unit_coprime` and `Int.euler_unit_injective`.

## ADR-0716's claim, verified against the kernel and the tree

Both named theorems exist, are correctly stated, and are axiom-free
(confirmed via `theorem_dependency_inventory` and `nat_axiom_inventory
--require-axiom-free integer`, both re-run for this lane's own additions
below). **But that is not the same as the theorem being within reach**, and
the file that landed them says so in its own module doc, in detail, which
ADR-0716 did not carry forward:

`int_prelude/euler_totient.rs`'s own doc records that Euler's theorem does
NOT land there, because two things are missing:

1. A product over a **predicate-defined subset** of `[0,n)` (Euler's proof
   folds a product over `{k < n : gcd(k,n)=1}`, not the full range).
2. A proof that such a restricted product is invariant under a
   predicate-preserving permutation.

At the time that file was written, neither existed anywhere in the kernel.
Since then, `nat_prelude/subset_product.rs` landed `Nat.prodRangeIf`
(definition + defining equations + `congr_lt`) — but **that file's own doc
says permutation invariance is STILL missing**, and sizes porting the
missing induction (an adjacent-transposition swap, the mechanism
`Int.prodRange_swap`/`Int.prodRange_permute` use in `prod.rs`) at roughly
650 lines, "same order of magnitude" as the whole file — because **no such
lemma exists for `Nat.prodRange` at all**, only for `Int.prodRange`.

So the honest state before this lane: the two named ingredients are real,
but they are inputs to a step (subset-product permutation invariance) that
had not been built in EITHER prelude, for two different reasons (Nat: no
predicate-restricted product API at all, until subset_product.rs; Int: the
API exists via a different route but the swap induction was never ported
there either). One lane closed a target with zero new lemmas against a
two-or-three-lemma estimate this session; this is not that case — real
work remained, and it is a good deal more than "wire it up".

## Carrier decision: ℤ, not ℕ — and why

Detail moved to [`../notes/374-euler-theorem.md`](../notes/374-euler-theorem.md).

