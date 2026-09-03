# ADR-1586: a third producer decides rewrite chains, and confluence is the boundary

Date: 2026-09-03
Status: Accepted
Lane: `simp-1`

Index-summary: `crate::simp` is the third tactic-layer producer in ADR-0601's
sense, beside `crate::linarith` (ADR-1576) and `crate::ring` (ADR-1580,
ADR-1582): an oriented rewrite set (identity/annihilator/defining laws with
no side condition, plus caller-supplied extras) matched first-order,
outermost-first, against a goal's own `ExprId` graph, and applied to a
`MAX_STEPS = 32` fixed point per side — no kernel `Pi`-type introspection
needed; a rule's pattern is a stateless `build` closure over fresh pattern
variables, exactly `ring::nat::prove_eq_at`'s "prove generically, apply
concretely" convention already establishes. It retired **thirteen**
hand-written rewrite chains: ten in `nat_prelude` (two duplicated pairs —
`one_add_eq_succ` and `two_mul_eq_add`/`mul_two_eq_add_self`, each proved
independently at two call sites) and three in `int_prelude`
(`add_left_neg`, `zero_mul_eq_zero`, `zero_add`). Measured `--release`,
`--example simp_cost`, 200 emissions per shape: **0.21–0.53 ms per term
search+emit, 0.28–0.63 ms with the kernel recheck** — the same order of
magnitude as `linarith`'s and `ring`'s own data.

This ADR records four things the build forced, three of them genuinely new
relative to `linarith`/`ring`. **(1) A blind outermost-first rewrite engine
is CONFLUENT AND TERMINATING only for a rule set whose every pattern
requires a specific literal subterm the rule's own output never
reintroduces** — every default rule here has that shape (an identity,
annihilator, or a `succ`/`neg`-consuming defining equation), and a bare
commutativity law (`add_comm`, `mul_comm`) categorically does not: its LHS
pattern `op a b` matches *any* application of `op`, including its own
output, so once such a rule is in the set the first `add`/`mul` node
anywhere in the term is rewritten back and forth forever. `add_comm`/
`mul_comm`/`add_assoc`/`mul_assoc` are therefore never in a default set;
a caller may still supply one as an extra and gets `Decline::BudgetExceeded`
at the cap, not a hang — tested for both carriers. **(2) The bug this design
choice was FOUND from, not merely anticipated**: the first version of the
traversal did a blind generic `App`-spine descent, and five of the ten ℕ
retirement-target tests failed kernel `TypeMismatch` on the first run,
because `NatOps::congr` (like `IntDev::icongr`) is hardcoded to `Eq Nat _ _`
(it calls `self.nat_ty()` internally), so lifting congruence through a bare
`App` node's function slot — a *partial application*, type `Nat -> Nat`, not
`Nat` — is ill-typed. The fix dispatches on the operator at a node's spine
head and recurses only into that operator's own carrier-typed argument
slots, exactly `ring::nat::Problem::flatten_add`'s established pattern.
**(3) Over ℤ, the confluence boundary from (1) is sharper than it first
looks**: `IntPrelude` has no `zero_add`/`zero_mul` (only the `_zero`-suffixed
forms), so a goal needing the reversed argument order MUST route through
`add_comm`/`mul_comm` as an extra — but that is only safe when the goal's
*post-annihilation fixed point* has no `add`/`mul` structure left for comm
to keep re-swapping. `Eq (add (neg a) a) zero` (comm then `add_neg` collapses
to a bare `zero`, no further `App` structure) is safe; `Eq (mul (neg a) b)
(neg (mul a b))` (`neg_mul`-shaped; comm then `mul_neg` leaves a bare
`mul a b`/`mul b a` residue with nothing to annihilate it) is not — tried,
and confirmed `Decline::BudgetExceeded` by actually running it, not by
inspection, and pinned as a test
(`a_neg_mul_shaped_goal_is_not_a_safe_retirement_target`) rather than left as
a doc-comment claim. A wide, criteria-driven search of `int_prelude` under
this constraint found exactly **three** usable retirement sites, not the
five the design brief hoped for — a sized negative, not an oversight (§3).
**(4) `List` was scoped but not built, and the reason is not merely time**
(§4): a systematic search of every downstream consumer found **zero**
existing call sites citing any of `List`'s four unconditional laws outside
their own declaration, so there is currently no retirement population for a
`simp::list` engine to point at, and the carrier is a genuinely different
design task (explicit type/level threading, a hand-numbered free-variable
convention list_prelude uses instead of a `fresh_fvar` counter) rather than
a mechanical port of the ℕ/ℤ engine.

Index-status: Accepted

## Context

ADR-1576 and ADR-1580/ADR-1582 landed the first two tactic-layer producers
and left the rewrite-chain shape as the obvious third: "apply `add_zero`,
`mul_one`, `zero_add`, `mul_zero`, `succ_pred`, `sub_self`, a defining
equation … or a user-supplied equation at some position, repeatedly, until
both sides coincide" — Lean's `simp`, scoped to an oriented rewrite set with
a step budget rather than a full simp-set search. The design brief fixed:
outermost-first traversal, first-order matching with fvars as pattern
variables, `MAX_STEPS = 32`, and `Decline::{NoProgress, BudgetExceeded,
SidesDiffer}`.

Step 0 (`just brief` was not run against a specific target — this is a new
producer, not a single-fact dispatch — so step 0 here is the retrieval
question `finding-existing-lemmas.md` frames for any new capability: does
anything like this already exist?) confirmed no `simp`-shaped module existed
(`ls crates/axeyum-lean-kernel/src/*simp*` — nothing) and that
`NatOps`/`IntDev` already carry every primitive combinator this producer
needs (`kernel()`, `fresh_fvar()`, `refl`/`symm`/`trans`/`congr`/`chain`,
`lemma(name, args)`, `lam_fv`/`pi_fv`/`apply`, `declare_theorem`) — no new
kernel-facing infrastructure, only a new module composing what already
exists, exactly `ring::nat::prove_eq_at` (`crates/axeyum-lean-kernel/src/
ring/nat.rs:809-822`) already establishes as the "prove generically, apply
concretely" idiom this producer's `Rule::build` closures reuse directly.

## Decision

### 1. The rewrite set, matching, and emission — as specified, with one addition the brief did not anticipate

A `Rule<D>` (ℕ, generic over `D: NatOps`) / `Rule` (ℤ, concrete over
`IntDev<'_>` — `IntDev`'s `Int`-typed combinators are inherent methods, not
a trait, mirroring `ring::int`'s own non-generic choice) pairs a declared
lemma's `NameId` with a stateless `build: fn(&mut D, &[ExprId]) -> (ExprId,
ExprId)` returning the lemma's `(lhs, rhs)` over `arity` args, plus an
[`Orientation`]. Matching instantiates `build` with fresh pattern-variable
`FVar`s, then walks the resulting pattern against a candidate subterm
structurally: an `FVar` that is one of *this rule's own* pattern variables
binds on first occurrence and must repeat the SAME matched `ExprId` on every
later occurrence (`Nat.sub_self`'s `n`, used twice, is exactly this case,
and its test is the only place the consistency check is exercised rather
than merely present). No higher-order unification, and — the addition the
brief's own examples did not need but the traversal fix in §2 makes
necessary — no delta-unfolding of a `Definition` head: a goal built from a
compound operation (`Nat.dist`, `Nat.lcm`) is out of reach exactly as
`div`/`mod`/`sub` are out of `ring`'s fragment.

Emission reuses `d.lemma(rule.name, matched_args)` (`d.symm`'d for
`Backward`), lifted to its position, and `chain`'d into one `Eq.trans` spine
per side; the two sides join at their shared fixed point with one final
`trans`/`symm`. The procedure's own "did both sides converge to the same
term" check is not trusted — `prove_eq_unverified` skips it, and the
corrupted-chain tests confirm the KERNEL, not the procedure, is what refuses
a forced mismatch, exactly `ring::nat::prove_eq_unverified`'s framing.

### 2. Confluence is not free, and the first implementation found this by breaking

The design brief specified "outermost-first traversal of the goal's LHS and
RHS" without specifying HOW to descend past a node with no match. The
obvious implementation — peel `e` as a generic `App(f, a)` and recurse into
`f` — is unsound for this kernel's specific `NatOps`/`IntDev` combinators:
`congr`/`eq`/`refl`/`symm`/`trans` are each hardcoded to one carrier (`Eq
Nat _ _`, `Eq Int _ _`), because they bake in `self.nat_ty()`/`self.int_ty()`
rather than inferring a type. A bare `App(add_const, u)` node — `Nat.add`
partially applied to its first argument — has type `Nat -> Nat`, not `Nat`,
so congr-ing over it builds an ill-typed `Eq`. This was not caught by
inspection: the first working version of `rewrite_step` passed 14 of the 19
ℕ tests and failed the other five (`double_eq`, `two_mul_eq_add`,
`mul_two_eq_add_self`, `bezout`, `distrib_one_plus` — every target whose
rewrite site sits at least one level of nesting deep) with kernel
`TypeMismatch { expected: ExprId(3), got: ExprId(5776) }`, a message that
names neither the operator nor the position. The fix dispatches on the
`spine`/`head_const` of a node (`add`/`mul`/`sub`/`succ`/`pred` for ℕ;
`add`/`mul`/`neg` for ℤ — the only shapes any `Rule::build` closure ever
produces) and recurses only into that operator's own carrier-typed argument
slots, using a congr context closure that reconstructs the full application
— the exact pattern `ring::nat::Problem::flatten_add`/`flatten_mul` already
use, for the identical reason, discovered independently by running tests
rather than by reading that file first.

A second, subtler consequence of the same fact governs which rules can EVER
appear in a rule set at all, default or extra: **the fixed point is
confluent and terminating only when every rule's pattern requires a
specific literal subterm (a numeral, a constructor head) that the rule's
own output never reintroduces.** Every default law here (an identity,
annihilator, or `succ`/`neg`-consuming defining equation) has that shape and
strictly reduces a term's `succ`-depth or removes an annihilated operand, so
a default-only run always halts. A bare commutativity law's LHS pattern
`op a b` matches *any* application of `op` — including the very term it just
produced — so once it is in the set, the first `add`/`mul` node anywhere
left in the term oscillates forever. This is why `add_comm`/`mul_comm`/
`add_assoc`/`mul_assoc` are excluded from every default set by construction,
not by oversight, and why the looping-rule-set test
(`add_comm_alone_declines_budget_exceeded_not_a_hang`, both carriers) exists:
a caller who supplies one anyway gets `Decline::BudgetExceeded` at the cap,
never a hang.

### 3. ℤ: the confluence boundary is sharper than ℕ's, and the retirement count is a sized negative

`IntPrelude` carries only the `_zero`-suffixed identities (`add_zero`,
`mul_zero`) — there is no `zero_add`/`zero_mul` — so any goal needing the
reversed argument order must route through `add_comm`/`mul_comm` as a
caller-supplied extra. Per §2, that is safe only when the rule set's OTHER
rules can fully consume whatever `comm` produces, landing on a term with no
further `add`/`mul` structure. `Eq (add (neg a) a) zero`
(`add_left_neg`'s statement) fits: `add_comm` swaps to `add a (neg a)`,
`add_neg` immediately fires and collapses the whole term to a bare `zero`
— an atom with no `App` structure left for `add_comm` to exploit again, so
the run halts (2 steps, verified). `Eq (mul (neg a) b) (neg (mul a b))`
(`neg_mul`'s statement) looks identical in shape but is NOT reachable: after
`mul_comm` then `mul_neg` fire, the residual `mul a b`/`mul b a` under the
outer `neg` is still a bare product of two symbolic atoms, and `mul_comm`
matches it forever. This was tried, run, and confirmed
`Decline::BudgetExceeded` — not inferred from the shape alone — and is
pinned as `simp::int_tests::a_neg_mul_shaped_goal_is_not_a_safe_retirement_
target` specifically so the finding cannot silently rot into a stale claim.

Under this constraint, a systematic scan of `int_prelude` for
hypothesis-free, induction-free, closed `Eq lhs rhs` goals citing only the
ten unconditional laws (plus `add_comm`/`mul_comm` in the safe shape) found
exactly **three** usable sites: `add_basics.rs::declare_add_left_neg`
(`Int.add_left_neg`'s own declaration — not circular, since `add_left_neg`
is not itself one of this producer's primitives), `sign_product.rs::
zero_mul_eq_zero`, and `fibonacci.rs::zero_add`. Several other
plausible-looking candidates (`neg_mul`, `neg_mul_neg`, both duplicated
across `fibonacci.rs`/`bezout_witnesses.rs`/`sign_product.rs`) were examined
and excluded on the finding in the previous paragraph; a few more
(`add_neg_cancel_left`'s hand chain, `add_left_cancel`, `product_zero_of_
*_zero`) were excluded because they take an ambient hypothesis or prove a
non-`Eq` conclusion (an implication, or a conclusion derived from a
transported equality) — outside this producer's "prove a closed equality
from nothing" shape by design, not a gap in the search. **Three retirements,
not the five the design brief hoped for, is recorded here as a sized
negative**, per this repository's own standing rule that a precisely-stated
negative is a complete deliverable — not a shortfall to paper over with a
weaker or untested claim.

### 4. `List` was scoped, researched, and NOT built — and the reason is not merely session length

Two findings, independently sufficient to defer this carrier:

**(a) The design is not a port.** `list_prelude` has no `NatOps`/`IntDev`-
style trait or dev struct; its `ops.rs` exposes free functions
(`eq_of`/`refl_of`/`symm_of`/`trans_of`/`congr_of`) that take EXPLICIT
`level`/`ty` arguments at every call (`congr_of` takes a *pair* —
`level_a`/`ty_a` for the argument, `level_b`/`ty_b` for the result —
because `List.length : List α → Nat` changes carrier), because `List.{u}
(α : Type u)` is genuinely type-polymorphic and every theorem statement
carries `α` as a real argument, not a fixed carrier a trait method can bake
in. `list_prelude` also does not use a `fresh_fvar()` counter at all: every
call site hand-assigns a literal `u64` free-variable id from a manually
reserved numeric block (`91_000`, `91_100`, `91_200`, …), a convention this
producer's own fresh-pattern-variable minting would need to route around
with an out-of-band counter of its own, rather than reuse `NatState`'s
`fresh_fvar`. Neither of these is a large obstacle individually, but
together they mean a `simp::list` engine is a genuinely separate design
(a `Ctx { alpha, level, list, append, reverse, nil }` threaded everywhere,
not a `D: SomeListOps` generic parameter), not a mechanical retype of
`simp::nat`.

**(b) There is currently nothing to retire.** `List`'s four unconditional
laws (`append_nil`, `append_assoc`, `reverse_append`, `reverse_reverse`) are
cited exactly once each, at their own declaration in `list_prelude/
theorems.rs` — `grep -rn "append_nil\|append_assoc\|reverse_append\|
reverse_reverse" list_prelude/bridge.rs list_prelude/perm.rs list_prelude/
bridge/*.rs list_prelude/perm/*.rs` returns ZERO matches. `reverse_append`'s
own proof cites `append_nil` and `append_assoc`, but by induction over a
list argument (case-splitting via `List.rec`, building per-branch
"singleton"/"tail" terms) — the shape ADR-1580 §1 already excludes
(a producer's own primitives, and here also induction, which this producer
does not attempt). Building the engine before any downstream consumer needs
the rewrite-chain shape would be exactly the unexercised-capability
liability ADR-1580's own Alternatives section already declined for
`sort_factors`: "no test would exercise it honestly … an unexercised
capability is a liability, not a feature." Deferred, not abandoned — the
design sketch above is the starting point for a lane whose brief can point
at a real call site.

## The cost datum, beside `linarith`/`ring_law_proof`

Measured `--release`, `cargo run --release -p axeyum-lean-kernel --example
simp_cost`, 200 emissions per shape, prelude built once per shape (ℕ only —
`simp::int`'s three targets did not warrant a separate cost harness this
session):

| goal shape | search + emit | + kernel recheck |
| --- | ---: | ---: |
| `Nat  1+x = succ x` | 0.210 ms | 0.277 ms |
| `Nat  2*x = x+x` | 0.251 ms | 0.320 ms |
| `Nat  2+x = succ(succ x)` | 0.395 ms | 0.484 ms |
| `Nat  (n+0*0)+n*0 = 0*0+n*1` | 0.533 ms | 0.628 ms |

A single unpinned run on a shared box — order-of-magnitude, not a ratchet
baseline, same caveat `linarith`/`ring`'s own data carry. The costs track
step count (the four-step `bezout`-shaped goal costs roughly 2.5x the
single-step `1+x = succ x`), not carrier or structural depth alone.

## Consequences

- `simp::Decline` has four variants shared across every carrier submodule
  (mirroring `ring::Decline`/`linarith::Decline`'s crate-root sharing):
  `GoalNotAtomic`, `NoProgress` (neither side moved), `BudgetExceeded` (one
  side did not reach a fixed point within `MAX_STEPS`), and `SidesDiffer`
  (both sides converged, to different terms — a positive decline, like
  `ring::Decline::NotAnIdentity`, but weaker: it is relative to THIS rule
  set, not a completeness claim over the whole fragment the way `ring`'s
  normal-form comparison is).
- **This producer scores zero on the producer-contract system**, exactly as
  `linarith`/`ring` did — `artifacts/autogenesis/producer-contracts/
  simp-rewrite-v1.json` is written, validated, and born retired under
  ADR-1510 rule 1. It is the THIRD contract born retired, and the third
  datum making the same point from a different angle: the contract system
  sizes *dispatch* against the open fact ledger and structurally cannot see
  a *retirement* — thirteen hand proofs replaced, none of it visible to a
  shape predicate over open facts.
- **`neg_mul`/`neg_mul_neg`-shaped ℤ identities remain hand-written.** This
  producer cannot reach them (§3); a future `ring::int`-style normal-form
  route (already exists, per ADR-1582) is the correct tool for that shape,
  not a wider `simp` rule set — widening the rule set to cover them would
  reintroduce the exact non-termination this ADR's central finding rules
  out.
- **`List` is scoped but not started.** §4's design sketch (a `Ctx` struct
  threading `alpha`/`level`/`list`/`append`/`reverse`/`nil`, an out-of-band
  fvar counter clear of `list_prelude`'s `9x_xxx` hand-numbered ranges) is
  the next lane's starting point, gated on a real call site existing to
  retire — building it speculatively first would be exactly the
  unexercised-capability risk ADR-1580 already declined once.

## Alternatives considered

- **Delta-unfolding a `Definition` head during traversal** (so a goal built
  from `Nat.dist`/`Nat.lcm` could still be reached by first unfolding to
  `add`/`sub`/`div` structure). Rejected: this is a strictly different,
  strictly more powerful capability than "rewrite by named equations", it
  has no test target in the ten/three retirements actually needed, and it
  would blur the boundary this producer and `ring` currently keep clean (a
  goal outside the fragment declines, rather than getting unfolded into
  something that might silently be).
- **A single fvar-counter convention shared with `list_prelude`'s hand-
  numbered scheme**, considered briefly while scoping §4 and dropped before
  any code: reusing the SAME numeric ranges risks a silent collision that
  the kernel's own type-checker would not necessarily catch (two distinct
  logical variables sharing one `u64` id inside one open term is a scoping
  bug, not a type error, if it happens not to produce an ill-typed term by
  accident) — an out-of-band counter is the safer design and costs nothing.

## Cross-references

- [ADR-1576](adr-1576-a-tactic-is-a-producer-and-its-return-is-measured-in-retired-proofs.md)
  — the first tactic-layer producer (`linarith`).
- [ADR-1580](adr-1580-a-second-tactic-lands-and-its-own-primitives-cannot-be-its-targets.md) /
  [ADR-1582](adr-1582-the-ring-producer-over-int-and-rat-and-what-each-carrier-costs-it.md)
  — the second (`ring`); `ring::nat::prove_eq_at` and
  `ring::nat::Problem::flatten_add`/`flatten_mul` are the two established
  idioms this producer reuses directly (§1, §2).
- [ADR-0601](adr-0601-three-producers-one-trust-anchor.md) — producers
  behind one trust anchor. `simp` is the third tactic-layer producer.
- [ADR-1510](adr-1510-a-contract-is-sized-by-the-frontier-and-a-decline-dies-with-its-fact.md)
  — a contract is sized by the frontier and retires when the population
  empties. `simp-rewrite-v1` is the third contract born retired.
- [07-the-cost-model-and-pareto-position.md](../../formalized-math-2026-08/07-the-cost-model-and-pareto-position.md)
  §3 — `linarith`/`ring_law_proof`'s own data are what this one sits beside.
