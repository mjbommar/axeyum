# ADR-1545: `Nat.testBit`'s codomain is the outermost link of a chain, and the `Bool` view it would add is already built

Status: accepted
Date: 2026-09-02
Index-summary: The `shape-census` lane named the `Nat.testBit` codomain as
the single highest-leverage decision on the ready frontier: six `ml430`
mirrors blocked, one construction question, no producer able to take it.
Measured against the pinned Lean/Mathlib source and this kernel, that
framing is wrong in both directions. Option (a) — a `Bool`-valued `testBit`
beside the `Nat`-valued one, with an agreement theorem — is already built,
axiom-free, and shipped (`Axeyum.Autogenesis.testBitBool` in
`examples/nat_testbit_bool_bridge.rs`, exported as a committed capsule and
run from the justfile), and it flipped nothing. Option (b), changing
`Nat.testBit`'s codomain, touches 23 declarations (measured twice by
independent routes, agreeing on the set) — three of which do arithmetic on
the result and have no `Bool`-typed restatement — and still would not match
Mathlib's `def`, which is `1 &&& (m >>> n) != 0` over a `Nat.shiftRight`
this kernel does not have and a `Nat.land := bitwise and` whose imported
closure was already measured to carry `propext`. Three of the six mirrors
additionally name a SECOND divergent construction (`Nat.land`/`Nat.lor`/
`Nat.ldiff`, hand-rolled here as fuel recursions where Mathlib specializes
`bitwise`), and a fourth needs `List Bool` and `Inhabited`, neither of which
exists. Decision: (c), leave all six blocked, and correct the two artifacts
that told the census otherwise so the next lane is not sent here again.
Index-status: accepted

## Context

`docs/research/11-design-review/2026-09-02-what-the-frontier-is-shaped-like.md`
(lane `shape-census`, `2dfa70297`) measured the dependency-ready open
frontier and found its largest raw bucket is nine `Nat` equations with no
hypotheses, of which **zero** are targetable: three are mutation controls
and six are divergence-blocked on `Nat.testBit`. Its recommendation, ranked
second of three:

> **Decide the `Nat.testBit` codomain question.** Six ready facts and an
> unknown number of held-out ones hang on one construction decision: does
> `Nat.testBit` return `Nat` or `Bool` here? … it is a one-time construction
> change rather than a proof, and today it silently blocks the largest
> uniform family on the frontier.

That recommendation is sound *as a request to decide*. What it inherits, and
what this ADR tests, is the premise underneath it: that the codomain is the
binding constraint.

The six facts, all `partition: development` in `nursery-v1.json`, family
`natural-bitwise` — all 19 members of that family are `development`, so **no
held-out row is in scope for anything decided here**:

| fact id | `formal.statement` |
| --- | --- |
| `F:ml430-nat-testbit-land-dfef7ca4` | `∀ (m n k : ℕ), (m &&& n).testBit k = (m.testBit k && n.testBit k)` |
| `F:ml430-nat-testbit-lor-7644e067` | `∀ (m n k : ℕ), (m ||| n).testBit k = (m.testBit k \|\| n.testBit k)` |
| `F:ml430-nat-testbit-ldiff-16f94162` | `∀ (m n k : ℕ), (m.ldiff n).testBit k = (m.testBit k && !n.testBit k)` |
| `F:ml430-nat-testbit-eq-inth-ffa07392` | `∀ (n i : ℕ), n.testBit i = n.bits.getI i` |
| `F:ml430-nat-zero-of-testbit-eq-false-e244c9a1` | `∀ {n : ℕ}, (∀ (i : ℕ), n.testBit i = false) → n = 0` |
| `F:ml430-nat-lt-of-testbit-72f64ab8` | `∀ {n m : ℕ} (i : ℕ), n.testBit i = false → m.testBit i = true → (∀ (j : ℕ), i < j → n.testBit j = m.testBit j) → n < m` |

The standard a flip must meet is not this lane's to invent. It is the
mirror-flip criterion
([kernel-proof-engineering.md](../../contributor-guide/kernel-proof-engineering.md),
"When is flipping an `ml430` mirror honest?") as generalized by
[ADR-0840](adr-0840-a-flip-needs-every-constituent-construction-to-match-not-just-the-outermost-one.md):

> A flip requires **every constituent construction in the statement's
> dependency chain** to match Mathlib's `def`, not merely the outermost
> combinator.

## What was measured

All Mathlib/Lean readings are at the pinned commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f` (v4.30.0), from the checkout at
`/data0/axeyum/lean-import-toolchain/mathlib4` and the matching
`leanprover--lean4---v4.30.0` toolchain source — not from prose about them.

### 1. Mathlib's `Nat.testBit` is not a `Bool`-returning version of ours

`Init/Data/Nat/Bitwise/Basic.lean:147`:

```lean
@[expose] def testBit (m n : Nat) : Bool :=
  1 &&& (m >>> n) != 0
```

That is `Nat.land 1 (Nat.shiftRight m n) != 0` once the notation is
expanded. Ours (`nat_prelude/binary.rs`) is a **fuel recursion on the bit
INDEX** — `testBitAux 0 n ≡ n % 2`, `testBitAux (succ i) n ≡ testBitAux i
(n / 2)`, `testBit n i := testBitAux i n` — chosen precisely because
recursing on `n / 2` is not structural and the well-founded route was
declined.

So the two differ on **three** axes, not one: the codomain (`Bool` vs
`Nat`), the recursion (a shift-and-mask closed form vs an index recursion),
and the constants the body names. `Nat.shiftRight` **does not exist in this
kernel** (no `shiftRight`/`shift_right` anywhere in `nat_prelude.rs`), and
`Nat.land` diverges — see (3).

This is not new information in the tree.
[`docs/autogenesis/279-bitwise-semantic-law-reconstruction-gap.md`](../../autogenesis/279-bitwise-semantic-law-reconstruction-gap.md)
already measured the imported side:

> Both `Nat.testBit` and `Nat.bitwise` carry `propext` through their concrete
> implementation closures. For `testBit`, the 13 direct dependencies expose
> the typeclass-expanded `HAnd`/`HShiftRight`/`BEq` route… **This rules out
> a cheap exact-definition graft as the clean bridge.**

Axiom-freedom per prelude is this project's headline metric. A route that
reaches Mathlib's `testBit` by matching its body reaches `propext` with it.

### 2. Option (a) is already built, axiom-free, and it flipped nothing

The brief's option (a) — "add `Nat.testBitB : ℕ → ℕ → Bool` beside the
`Nat`-valued one with an agreement theorem" — exists.
`crates/axeyum-lean-kernel/examples/nat_testbit_bool_bridge.rs` (2,104
lines) declares

```text
Axeyum.Autogenesis.bitToBool  : AxNat → Bool          -- 0 ↦ false, succ _ ↦ true
Axeyum.Autogenesis.testBitBool n i := bitToBool (Nat.testBit n i)
```

and proves — run in this worktree, every line reporting `axioms=0`:

```text
testBitBool_zero         : ∀ x0, testBitBool 0 x0 = Bool.false
testBitBool_succ         : ∀ x0 x1, testBitBool x0 (succ x1) = testBitBool (x0 / 2) x1
bitToBool_boolToBit      : ∀ (b : Bool), bitToBool (boolToBit b) = b
boolToBit_roundtrip_zero : ∀ (b : Bool), testBitBool (boolToBit b) 0 = b
testBitBool_beyond_bound, bitwiseObservation_apply, reifyBits_zero/_succ,
testBitBool_bitwiseAnd / _bitwiseOr / _bitwiseDifference, …
```

The agreement direction the brief asked for (`testBitB n i = true ↔
testBit n i = 1`) is stronger here and free: the `Bool` view is *defined* as
`bitToBool` of the numeric one, so the bridge is definitional rather than an
`Iff` to be proved. The family is exported as a committed capsule
(`artifacts/autogenesis/bitwise-clean-family-capsule-v1.json`) and is run
from the `justfile`.

**It has been in the tree since 2026-08-26 and not one of the six mirrors
moved.** Doc 279 says why, in its own words, and this is the sentence the
census's framing needed and did not have:

> This proves the result-sort adaptation itself is available; **equivalence
> with the exact imported `Nat.testBit` definition remains missing** and is
> still denied credit in the artifact.

So option (a) is not a decision awaiting a lane. It is a completed
experiment whose result is already in: **the codomain seam is bridgeable,
constructively and axiom-free, and bridging it flips nothing.**

### 3. Three of the six name a SECOND divergent construction

`testbit_land`, `testbit_lor` and `testbit_ldiff` name `&&&`, `|||` and
`ldiff`. At the pinned source these are:

```lean
-- Init/Data/Nat/Bitwise/Basic.lean:27, 50, 58
def bitwise (f : Bool → Bool → Bool) (n m : Nat) : Nat := …
  decreasing_by apply bitwise_rec_lemma; assumption   -- WELL-FOUNDED
def land : @& Nat → @& Nat → Nat := bitwise and
def lor  : @& Nat → @& Nat → Nat := bitwise or
-- Mathlib/Data/Nat/Bits.lean:147
def ldiff : ℕ → ℕ → ℕ := bitwise fun a b => a && not b
```

Ours are three independent hand-rolled **structural fuel recursions**,
landed deliberately instead of the general combinator.
`nat_prelude/land.rs`'s own module doc states the reason and the divergence
in one paragraph:

> Mathlib v4.30 … defines `Nat.land` via the general two-argument
> `Nat.bitwise` … which recurses on neither argument structurally … and
> needs well-founded recursion — through the equation compiler,
> `Quot.sound`/`propext`, fatal to this project's axiom-freedom metric …
> **This lane lands `Nat.land` directly rather than the general
> `Nat.bitwise`.**

This kernel does now also carry a general `Nat.bitwise`
(`nat_prelude/bitwise.rs`), but as `bitwiseAux f m m n` — fuel-structural
again, not Mathlib's well-founded recursion — and `land`/`lor`/`ldiff` are
not defined through it. By exactly the standard the divergence registry
already applies to `Nat.minFac` ("ours is a fuel-structural linear search;
Mathlib's is well-founded on `sqrt n` skipping evens. Same values, different
construction, so the pinned statement is about a different function"), each
of these three is an **independent** divergence stacked on `testBit`'s.

### 4. The sixth needs two types this kernel does not have

`n.testBit i = n.bits.getI i` names `Nat.bits : ℕ → List Bool`
(`Mathlib/Data/Nat/Bits.lean:141`, `binaryRec [] fun b _ IH => b :: IH`) and
`List.getI [Inhabited α]` (`Mathlib/Data/List/Defs.lean:38`). This kernel
has no `List` inductive and no `Inhabited` class — and, per the registry's
own `Nat.findGreatest` row, no instance implicits at all, so `getI`'s type
is not even expressible. This was already classified `not-removable`; it
stays.

### 5. Option (b)'s cost, measured twice by independent routes

Declarations whose **type or checked value** names `Nat.testBit` or
`Nat.testBitAux`:

| route | count |
| --- | --- |
| `shape_search --const Nat.testBit` (type occurrence) | 15 |
| `shape_search --value-const Nat.testBit --index-values` | 6 |
| `shape_search --value-const Nat.testBitAux --index-values` | 1 (`Nat.testBit` itself) |
| **union of the above** | **22** |
| `kernel_declaration_projection`, independently re-derived over 15,005 rows | **22 — identical set, not merely the same count** |
| plus `Nat.testBitAux`, whose own codomain must change | **23** |

The 23:

```
Nat.testBit  Nat.testBitAux  Nat.testBit_zero  Nat.testBit_succ
Nat.testBit_of_zero  Nat.testBit_le_one  Nat.testBit_eq_zero_of_lt
Nat.testBit_land  Nat.testBit_lor  Nat.testBit_xor  Nat.lt_of_testBit
Nat.eq_of_testBit_eq  Nat.zero_of_testBit_eq_zero  Nat.sum_testBit_eq
Nat.sum_testBit_lt  Nat.exists_most_significant_bit  Nat.msb_exists_of_le_fuel
Nat.and_or_distrib_left  Nat.and_or_distrib_right  Nat.xor_assoc
Nat.xor_ne_zero_iff  Nat.xor_trichotomy  Nat.xor_xor_cancel_left
```

**A codomain change is not a rename here.** Three of those do arithmetic on
the result and have no `Bool`-typed restatement at all:

- `Nat.testBit_le_one : ∀ n i, Nat.le (testBit n i) 1` — the proposition
  *is* the `{0,1}` bound. Under a `Bool` codomain it is not restated, it is
  deleted, and every consumer of the bound loses its lemma.
- `Nat.sum_testBit_eq` / `Nat.sum_testBit_lt` — `consts=[…, Nat.mul,
  Nat.pow, Nat.sumRange, Nat.testBit, …]`; `testBit` appears as a numeric
  digit inside `sumRange (fun i => testBit n i * 2^i)`. Each use needs a
  `boolToBit` wrapper inserted, which changes the statements the rest of the
  binary-decomposition development is proved against.

And after paying all 23, the result still is not Mathlib's `testBit`: it
would be a `Bool`-valued fuel index recursion, not `1 &&& (m >>> n) != 0`.
**Flips bought: zero.**

## The options, costed

| | (a) add `Nat.testBitB` beside it | (b) change `Nat.testBit`'s codomain | (c) leave blocked, correct the record |
| --- | --- | --- | --- |
| existing declarations touched | 0 (purely additive) | **23** | 0 |
| declarations added | ~10 minimal; **already done**, 40+ in the example | 0 | 0 |
| statements with no restatement | — | 3 (`testBit_le_one`, `sum_testBit_eq`, `sum_testBit_lt`) | — |
| reaches Mathlib's `def`? | no | no (`Nat.shiftRight` absent, `Nat.land` divergent, closure carries `propext`) | n/a |
| mirrors flipped | **0 — measured, not predicted: it is already built** | **0** | 0 |
| held-out rows moved | **0** (all 19 `natural-bitwise` rows are `development`) | **0** | **0** |

## Decision

**Option (c).** All six mirrors stay `open`. No fact file is edited, no
`Nat.testBit` codomain is changed, and no second `Nat.testBitB` is added to
the prelude — the `Bool` view already exists as
`Axeyum.Autogenesis.testBitBool`, and promoting it from example to prelude
would buy convenience, not a flip, so it is not part of this decision.

Because "record why" is worthless if the record is not the one a lane
actually reads, (c) is implemented as two corrections to the two artifacts
that told the census the opposite:

1. **`scripts/gen-obstruction-producers.py:classify_testbit`.** Its
   `nat-testbit-bool-codomain` row is classified `removability:
   new-construction` and its `reason` asserts, of the `Bool`-valued view and
   its bridge theorem, that "**neither is built**". Both halves are false in
   this tree: the construction is built and axiom-free (§2), and building it
   does not remove the obstruction (§1, §3, §4). Reclassified
   `not-removable`, with the measured chain in the reason and three primary
   sources in `evidence`.

2. **`artifacts/autogenesis/mirror-divergence-registry.json`, the
   `Nat.testBit` row.** Its `class` stays `codomain` — that is the axis the
   gate re-derives for itself from the pinned statements via
   `codomain_witness_regex`, and it must keep re-deriving it. Its `why` now
   records that the codomain is the **outermost link of a chain**, names the
   other links, and points at the already-built bridge, so the next census
   reads the whole obstruction rather than the visible half.

### The generated artifact could not be refreshed, for an unrelated reason

`artifacts/obstruction-producers/obstructions.json` is **not** regenerated by
this ADR, because `gen-obstruction-producers.py` cannot write it on `main`:

```
$ python3 scripts/gen-obstruction-producers.py --check
ERROR: P2 target F:ml430-nat-and-or-distrib-left-fe131f64 is missing or not
open; hypothesis is stale
```

`compile_pointwise_bit_extensionality` hardcodes two targets and `die()`s
before `render()` reaches its write. Both targets are now `epistemic_status:
proved` (`845fc8823`), so the producer's prospective hypothesis is spent and
the generator refuses. `check-obstruction-producers.py` reports the same
thing plus two `G7 non-open-target` failures.

**This is red on `main`, not caused by this ADR.** Verified by running both
scripts from a pristine `scripts/lane-snapshot.sh main` extraction: byte-for
byte the same three failures, with none of this lane's edits present. The
source correction in (1) is therefore committed as the authority and will
reach the artifact on the first successful regeneration after the P2
hypothesis is re-pointed or retired — a producer-policy decision belonging
to that producer's owner, not to this lane.

The corrected classification itself was verified by calling
`build_obstructions_doc()` directly on the real ledger: `nat-testbit-bool-
codomain` computes as `not-removable` / `definitional-non-equivalence` over
its 5 facts, and all five of its path-shaped `evidence` entries resolve to
files that exist, which is what G9 requires of a `not-removable` claim.

## What this ADR does NOT claim

- **It does not claim the six are unprovable content.** Their extensional
  content is largely already proved here as local facts —
  `F:nat-testbit-land`, `F:nat-testbit-lor`, `F:nat-testbit-xor`,
  `F:nat-lt-of-testbit`, `F:nat-zero-of-testbit-eq-zero` — which is exactly
  the honest outcome the registry's own `why` prescribes. What is blocked is
  the *mirror*, because the mirror is a proposition about Mathlib's
  constructions.
- **It does not decide the `Nat.land`/`Nat.lor`/`Nat.ldiff` registry gap**,
  and that gap is now measured and should be decided deliberately. §3 shows
  those three diverge from Mathlib by the same standard the registry applies
  to `Nat.minFac`, and the registry has no row for any of them.
  `gen-obstruction-producers.py`'s own docstring leans on their absence —
  "`Nat.land`/`lor`/`ldiff`/`xor` are **not registered as diverging**" — as
  the precondition licensing the `extensional-duplicate-close` producer,
  which today claims three targets (`F:ml430-nat-and-comm-7525d05a`,
  `F:ml430-nat-and-assoc-273b60d8`, `F:ml430-nat-and-le-left-6d04acb7`; all
  three verified `development`, none held-out). Adding those rows would
  retire that producer's whole population. That is a producer-policy
  decision with its own blast radius, not a corollary of the codomain
  question, and this lane deliberately did not take it. **It is a named next
  action, with the measurement above as its input.**
- **It does not rewrite `docs/plan/status/l3-d4-obstruction-producer.md`**,
  which records `nat-testbit-bool-codomain` as "(new-construction, 5
  facts)". That is another lane's status file. Its prose — and PLAN.md's
  generated copy of it — is stale as of this ADR; the artifact is the
  authority and it now disagrees with them.

## Consequences

- The frontier's largest raw bucket is confirmed, on primary sources rather
  than on a class label, to hold zero closable facts. A lane pointed at it
  by size ranking is being pointed at nothing, and the corrected obstruction
  row now says so at `removability`, which is the field a selector reads.
- One measured claim is retired: "six ready facts hang on one construction
  decision." They hang on between two and five constructions, depending on
  the fact, and the one that was named is already made.
- The `natural-bitwise` family's 19 `development` rows are unchanged; the
  blind evaluation population is untouched by everything above.
