# ADR-1576: a tactic is a producer, and its return is measured in retired proofs

Date: 2026-09-03
Status: Accepted
Lane: `omega-1`

Index-summary: Every proof in this kernel was a hand-built term, and the
coordinator measured **4,737 order-lemma call sites** across `nat_prelude`
(1,546), `int_prelude` (378), `rat_prelude` (601) and `creal` (2,212), with no
`omega`/`linarith`/Farkas-shaped procedure anywhere in tree. `crate::linarith`
is the first *tactic-layer* producer in ADR-0601's sense: a quantifier-free
linear-arithmetic decision procedure over ℕ and ℤ that returns a **kernel proof
term**, not a verdict — untrusted search (a bounded Farkas certificate),
trusted checking (`Kernel::add_declaration`). It retired **fifteen**
hand-written proofs on the day it landed (ten `nat_prelude`, five
`int_prelude`, 184 source lines deleted), each re-admitted at a type
`kernel_declaration_projection` shows byte-identical over all 15,887 rows and
each still measuring axiom footprint 0. Measured cost, `--release`: **0.5 to
15 ms per emitted term end to end**, kernel recheck included — against the
cost doc's `ring_law_proof` datum, this is the second encoded strategy whose
marginal price is CPU rather than tokens, and the first on the tactic layer.
This ADR decides three things the build forced. **(1) A tactic belongs behind
the same trust anchor as every other producer**, with no new trusted surface:
`linarith` declares nothing of its own and emits only lemmas the prelude
already had. **(2) A corrupted certificate must be refused by the KERNEL, and
the test must run with the procedure's own check disabled** — a corruption
caught only by our own bookkeeping proves nothing about the trust anchor.
**(3) A producer whose return is retirement scores ZERO on the producer-contract
system**, which sizes dispatch: `linear-arithmetic-v1` is born retired against
an empty live population, because linear arithmetic is the part of this
development that was finished first, by hand.
Index-status: Accepted

## Context

The flywheel's promise is that a result the system establishes with nobody
writing the proof is worth more than one a lane hand-assembles. Until now that
promise has been kept only on the *solver* side: `reconstruct/arithmetic`
turns an LRA/LIA unsat into a kernel term, `ring_law_proof` emits ring
identities. The *library* side — the 1,850-declaration constructed prelude —
was written a term at a time, and the order fragment is where that shows most.
Coordinator's count, 2026-09-03: 4,737 call sites of `le_trans`,
`add_le_add`, `lt_of_lt_of_le`, `le_add_right`, `le_antisymm`, `lt_irrefl` and
their siblings. `examples/shape_search --name-like omega` returned ABSENT.

Those 4,737 sites are not 4,737 theorems; most are steps inside larger proofs.
But the *shape* they share is exactly what a decision procedure decides, and
nobody had asked what it would cost to stop writing them.

## Decision

### 1. A tactic is a producer, behind the same anchor, with no new trusted surface

`crate::linarith` searches and emits; it never admits. Its entry points return
an `ExprId` that the caller pushes through `Kernel::add_declaration` (or
`Kernel::infer`), exactly as a hand-written proof is pushed. Two consequences
were treated as requirements rather than preferences:

- **Every lemma the emitter uses already existed.** Step 0 confirmed the whole
  list in the prelude before a line was written: over ℕ `le.refl`, `le_trans`,
  `le_add_right`, `add_le_add_left`, `add_le_add_right`,
  `le_of_add_le_add_right`, `le_succ_succ`, `lt_irrefl`, `le_antisymm`,
  `add_comm`, `add_assoc`, `add_right_comm`, `mul_comm`; over ℤ `le_refl`,
  `le_trans`, `add_le_add`, `add_le_add_left`, `add_le_add_right`,
  `add_le_add_iff_right`, `le_ofNat_add`, `lt_ofNat_add`, `lt_of_lt_of_le`,
  `le_of_lt`, `lt_irrefl`, `le_antisymm`, `add_comm`, `add_assoc`, `add_zero`,
  `add_neg`, plus `Iff.mp`. The only thing missing on either side was
  `add_le_add` over ℕ (two-sided) and `Int.add_right_comm`, both of which the
  emitter *derives* from the pair it has rather than declaring.
- **The declaration surface does not move.** `kernel_declaration_projection`,
  15,887 rows, before and after: prelude / kind / name / axiom-footprint-size /
  type-constants / rendered type byte-identical on every row. Exactly fifteen
  theorems changed, and only in their proof-dependency columns.

### 2. A corrupted certificate must be refused by the kernel, with our own check off

This is the guard that decides whether any of it is worth anything. A test in
which the *procedure* rejects a bad certificate measures the procedure's
bookkeeping; the claim being made is about the trust anchor. So
`emit_le_from_certificate` takes an explicit `verify` flag, the corruption
tests pass `false`, and each requires a `KernelError`:

| corruption | over ℕ | over ℤ |
| --- | --- | --- |
| multiplier off by one (2 where 1 is right) | kernel refuses | kernel refuses |
| residual off by one | kernel refuses | kernel refuses |
| hypothesis slot carrying a proof of a *different true* proposition | kernel refuses | kernel refuses |
| uncorrupted certificate (the positive control) | admitted | admitted |

The positive control is not decoration: without it every row above could be
"rejected" for a reason unrelated to the corruption. A separate test keeps the
procedure's own check honest by requiring it to decline the same corruption
with `verify = true` — both answers are useful, and running only one leaves the
trust story circular.

### 3. A producer whose return is retirement scores zero on the contract system

`artifacts/autogenesis/producer-contracts/linear-arithmetic-v1.json` is written,
validated, and **born retired** under ADR-1510 rule 1. Its live population is
zero, and the shape is not what makes it zero: reading all 245 open
`Mathlib v4.30 source proposition` names, not one predicate, finds no
quantifier-free linear-arithmetic proposition among them. The two closest,
`Int.add_one_le_of_not_le` and `Int.le_sub_one_of_not_le`, take a *negated*
order fact as a hypothesis, which this fragment handles as a goal and never as
an assumption.

That is not a defect in the contract, the shape, or the ledger. It is a
property of the ordering of the work: **linear arithmetic over ℕ and ℤ is the
part of this development that was finished first**, so a procedure for it
arrives to an empty dispatch queue and a full retirement queue. The contract
system sizes dispatch. It cannot see fifteen retired proofs, and that gap is
worth recording, because the next tactic-layer producer will hit it too.

## The cost datum, beside `ring_law_proof`

`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md` §3
prices the naive model at ~100k tokens per kernel-verified declaration and
names `ring_law_proof` as the first encoded strategy that drops a family to
CPU. This is the second, and the first on the tactic layer.

Measured `--release` on s4, `cargo run --release -p axeyum-lean-kernel
--example linarith_cost`, 200 emissions per shape, prelude built once per
shape (so the prelude build — paid once per process, not once per theorem — is
outside the loop):

| goal shape | search + emit | + kernel recheck |
| --- | ---: | ---: |
| `Nat  n ≤ n` | 0.455 ms | 0.517 ms |
| `Nat  n ≤ m ⊢ succ n ≤ succ m` | 0.805 ms | 1.033 ms |
| `Nat  a≤b≤c≤d ⊢ a ≤ d` | 1.555 ms | 2.297 ms |
| `Nat  n ≤ m ⊢ n+n ≤ m+m` | 1.205 ms | 1.483 ms |
| `Int  a + (b+c) = b + (a+c)` | 1.749 ms | 2.300 ms |
| `Int  3 hyps ⊢ (a+b)+c ≤ (d+e)+f` | 11.015 ms | 14.659 ms |
| `Int  b ≤ c−a ⊢ a+b ≤ c` | 4.464 ms | 5.447 ms |

Two things to read carefully before quoting these.

**They are a single unpinned run on a shared box.** This lane did not calibrate
the machine before and after the way the frontier ratchet does, and s4 carries
other lanes' builds; treat them as order-of-magnitude ("milliseconds, not
seconds, and not microseconds") rather than as a baseline anything should
ratchet against. The shape of the curve is the robust part: ℤ costs 3–7x ℕ,
and the hypothesis count moves it more than the term size does.

**The kernel recheck is a minority of the cost, not a majority** — 10% to 45%
depending on shape. The expensive half is the emitter's own normalizer, which
is where the ℤ/ℕ gap lives: `Int.add` case-splits on **both** arguments, so
nothing reduces and every step the ℕ normalizer got free from ι-reduction is a
lemma application over ℤ.

**Tokens against lines retired, for this lane.** 184 source lines of
hand-written proof deleted across fifteen declarations, plus a ~2,600-line
producer that will retire more without further token spend. The producer is
capex; the fifteen are the first instalment of the return. What the lane
*cannot* honestly claim is a tokens-per-theorem improvement on this session:
building the producer cost far more than hand-writing fifteen small order
proofs would have. The bet is entirely on reuse, and the honest way to state it
is as a break-even: at ~0.5–15 ms and 0 tokens per subsequent term, the
producer pays for itself the first time somebody would otherwise have
hand-written the sixteenth.

## Consequences

- Two `Decline` variants are load-bearing public API: `NoCertificate` (the
  search did not reach the goal — never a claim the goal is false) and
  `NonLinear` (a product of two non-constant terms in a ℕ goal, refused rather
  than silently abstracted). `unknown` is a first-class result here too.
- **The search is deliberately incomplete, and the bound is the honest
  statement of how incomplete.** Every numeral in this kernel is unary, so a
  certificate with coefficient 40 is a term forming `succ⁴⁰ zero`. The search
  enumerates multiplier vectors in order of increasing weight and declines
  above `MAX_MULTIPLIER = 4` rather than growing one. Fourier–Motzkin was
  considered and rejected for exactly this reason: it computes a projection,
  and recovering the emitter's multipliers from an FM refutation requires
  dividing by the negated goal's own multiplier, which is rational and
  reintroduces the large numerals the emitter must avoid.
- **Two measured fragment edges over ℤ, each pinned by its own test rather than
  asserted in prose.** A `<` *hypothesis* contributes only `a ≤ b` via
  `le_of_lt`; its strictness is dropped, because recovering it needs
  `lt a b → le (a+1) b` and `int_prelude` does not have that lemma
  (`lt_dest` gives `∃ i, b = a + ofNat (i+1)`, and turning that into the `+1`
  form is a new lemma, not a rearrangement). And `Int.mul` is not in the
  fragment at all, not even by a literal, where the ℕ side handles a numeral
  multiplier — `Nat.mul x k` ι-reduces to a fold at a literal `k`, `Int.mul x k`
  is stuck at symbolic `x` no matter what `k` is.
- **A doc comment in `int_prelude` is wrong and cost this lane a debugging
  cycle.** `Int.add_le_add_left`'s doc reads
  `∀ (a b : Int), le a b → ∀ (c : Int), le (add c a) (add c b)`, but the
  declaration is `int_theorem(p.add_le_add_left, 3, …)` — all three integers
  bind *before* the hypothesis. Passing the arguments in the documented order
  is a `TypeMismatch` naming two `ExprId`s and nothing else. Same for
  `add_le_add_right`. The declaration is the authority; the doc comment is not.

## Alternatives considered

- **Emit `Nat.mul λ _` plus `mul_le_mul_left` for a certificate multiplier**,
  as the obvious reading of "scale a hypothesis by λ". Rejected: the multiplier
  then sits inside a `Nat.mul` whose right operand has to be distributed back
  out through `left_distrib`/`mul_assoc`, which is more lemmas for a term that
  grows the same way, and `Nat.mul` recurses on its right argument so `mul λ x`
  at symbolic `x` is stuck and needs `mul_comm` before anything reduces.
  Repeated addition through `add_le_add` stays inside four lemmas and keeps the
  unary-numeral cost visible at the search bound where it belongs.
- **One normalizer shared between ℕ and ℤ**, parameterised over the carrier.
  Rejected after writing both: the canonical forms differ in a way that is not
  a parameter. Over ℕ the constant goes **last**, because `X + k` ι-reduces to
  `succ^k X` and every numeral bookkeeping step is then free. Over ℤ the
  constant goes **first**, because nothing reduces and a constant at the head
  guarantees every other summand has a nonempty prefix — which turns every
  transposition into `add_right_comm` and every cancellation into
  `add_assoc`/`add_neg`/`add_zero`, with no head cases at all. Abstracting over
  that would have hidden the one design decision in each file.
- **Building the missing `lt a b → le (a+1) b` bridge over ℤ** to make strict
  hypotheses usable. Deliberately not done: it is a new prelude declaration,
  which means a new `IntPrelude` field — a shared allocation point across lanes
  — for a capability nothing in the ledger currently needs. Recorded as a sized
  negative with a test that fails if the edge ever moves, which is the cheaper
  half of the same information.

## Cross-references

- [ADR-0601](adr-0601-three-producers-one-trust-anchor.md) — producers behind
  one trust anchor. This is the fourth producer and the first on the tactic
  layer.
- [ADR-0602](adr-0602-operations-are-receipts-dispatch-needs-producer-contracts.md)
  — the prospective/retrospective split this contract lives in.
- [ADR-1510](adr-1510-a-contract-is-sized-by-the-frontier-and-a-decline-dies-with-its-fact.md)
  — a contract is sized by the frontier and retires when the population
  empties. `linear-arithmetic-v1` is the first contract born retired.
- [07-the-cost-model-and-pareto-position.md](../../formalized-math-2026-08/07-the-cost-model-and-pareto-position.md)
  §3 — `ring_law_proof` is the datum this one sits beside.
