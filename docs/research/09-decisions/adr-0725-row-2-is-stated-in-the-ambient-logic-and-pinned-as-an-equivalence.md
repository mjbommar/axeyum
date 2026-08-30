# ADR-0725: Row 2 is stated in the ambient logic, and pinned as an equivalence

Status: accepted
Date: 2026-08-30
Index-summary: Executing ADR-0716's number-theory row 2 forced two choices it did not make — the extracted principle is stated in the kernel's own logic (`∀ P : Prop, Or P (Not P)`) rather than in `ipc_soundness.rs`'s encoded `Formula`/`Provable` object language, because the encoded principle is not the one any prelude theorem is stated with; and the row carries its CONVERSE, so the price is pinned as an equivalence (`L → E` and `E → L` over the same two `ExprId`s) rather than as a lower bound.
Index-status: accepted

## Context

[ADR-0716](adr-0716-row-two-of-a-decidable-subject.md)
measured that ADR-0603's row 2 is provably empty for ℕ, ℤ and ℚ — the decision
principle every analysis row 2 extracts is `le_total`, and that is a landed
axiom-free theorem over all three carriers — and named the one boundary that
survives: the **unrestricted least-number principle**, which reduces to full
excluded middle rather than to the LLPO the analysis rows reach. It even gave
the predicate: `P n := (n = 0 ∧ A) ∨ (n = 1)`.

That is a complete specification of *what* to prove. Building it
(`crates/axeyum-lean-kernel/src/nat_prelude/least_number.rs`,
`F:nat-lnp-unrestricted-implies-em`) forced two questions ADR-0716 did not
have to answer, and both generalize to every future row 2 over a discrete
carrier.

## Decision

### 1. The extracted principle is stated in the AMBIENT logic, not in an encoded object language

`ipc_soundness.rs` closes `F:excluded-middle-not-intuitionistic`: the *encoded*
formula `or_ (var 0) (imp (var 0) bot)` has no `Provable` derivation from the
empty context, by soundness against a 3-element Gödel/Łukasiewicz Heyting
chain. It is the natural thing to reach for when a row 2 must talk about
excluded middle, and it is the wrong thing to reach for here.

**A row 2 must say what a hypothesis of the kernel's own logic buys you in the
kernel's own logic.** Stating the least-number principle over `Formula` and
deriving the encoded excluded middle would prove something about the encoding.
The encoded principle is not the one any theorem in any prelude is stated with,
so the reduction would not touch the object the dominance claim is about.

So the conclusion is the ambient

```text
∀ (P : Prop), Or P (Not P)
```

quantified over every proposition the kernel can form, including every
statement in every prelude.

The two results are complementary and the pairing is worth stating explicitly,
because each is easily mistaken for the other's evidence: `ipc_soundness.rs`
establishes that excluded middle is **not free** in an intuitionistic setting;
`least_number.rs` establishes that the unrestricted least-number principle
**buys it**. Neither is evidence for the other's subject.

### 2. A row 2 carries its CONVERSE where the converse is available

ADR-0603 Amendment 2 asks for `classical statement ⟹ a decision principle this
kernel lacks`. That is a lower bound: it says the classical form costs *at
least* the principle. Where the converse is also provable, the row must carry
it, and the family then states the price **exactly**:

- `Nat.lnp_unrestricted_implies_em : L → E`
- `Nat.em_implies_lnp : E → L`

The converse is one line — excluded middle supplies
`Nat.lnp_of_pointwise_decision`'s hypothesis at `fun n => em (Q n)` — so the
cost of this rule is close to zero where it applies, and it removes a real
reading: without it, "the unrestricted LNP implies EM" is compatible with the
LNP being *strictly stronger* than EM, which would be a different and much less
interesting claim.

It also gives the row a mechanical pin that prose cannot fake.
`nat_prelude_tests::the_unrestricted_lnp_and_excluded_middle_are_pinned_as_an_exact_equivalence`
builds `L` and `E` once and requires the two declared types to be **literally**
`L → E` and `E → L` for the same two `ExprId`s — structural equality, not
`def_eq`, not a doc comment.

### 3. Non-vacuity is discharged by the SAME statement one hypothesis stronger

Amendment 2 requires a non-vacuity control. The one that works here, and that
should be the default for any row 2 of this shape, is to prove the identical
statement with the missing decision supplied as an explicit hypothesis:

```text
Nat.lnp_of_pointwise_decision :
  ∀ Q, (∀ n, Or (Q n) (Not (Q n))) → (∃ n, Q n) → ∃ m, And (Q m) (∀ k, Lt k m → Not (Q k))
```

The two rendered types then differ by exactly one argument, and a reader can
see that the boundary is the decidability hypothesis rather than a missing
proof. `Nat.lnp_decidable` (`F:nat-lnp-decidable`) instantiates it at a
`Bool`-valued predicate, and `Nat.least_divisor_search` — the same shape
specialised to divisibility, which `minFac`'s minimality has run on for a long
time — is the independent, older witness that the machinery works.

The test suite adds a second, environment-derived control: **no declaration
anywhere in the environment has type `L` or type `E`**, with the positive
control being the identical scan finding `Nat.lnp_unrestricted_implies_em` by
its own type. A scan that has stopped matching anything fails rather than
reporting a clean zero.

## Consequences

- Any future row 2 over a discrete carrier states its extracted principle in
  the ambient logic. The `ipc_*` object language stays where it belongs —
  proving things *about* derivability, not standing in for the real statement.
- A row 2 whose converse is provable and omitted is incomplete, and reviewers
  should ask for it.
- ADR-0716's minimality clause is written `∀ k, P k → m ≤ k`; the landed form
  is `∀ k, Lt k m → Not (P k)`, which is what a bounded search naturally
  produces. The two are interderivable over this prelude through
  `Nat.lt_or_ge` (landed, axiom-free) — **but that bridge is NOT a declaration
  in the tree**, so the equivalence of the two phrasings is an argument here,
  not a checked theorem. Anyone quoting ADR-0716's phrasing against the landed
  one should either build the bridge or quote the landed form.
- The residue ADR-0716 names as row 2′ (unique factorization's multiset
  uniqueness) is untouched by this ADR and remains open.

## Alternatives considered

**State row 2 over `Formula`/`Provable` and reuse `ipc_soundness`.** Rejected
for the reason in §1: it proves a statement about an encoding, and this
project's dominance claim is about the statements its preludes actually carry.

**Ship the implication alone.** Rejected: cheap to strengthen, and the
unstrengthened form leaves "strictly stronger than EM" on the table as a
reading nobody intends.

**Define `LNP` as a `Definition` in `Prop` and state the theorem against it.**
Rejected. The hypothesis is spelled out inline so that the rendered type a
referee reads is the whole claim; an abbreviation is one more place a
distinction could hide.
