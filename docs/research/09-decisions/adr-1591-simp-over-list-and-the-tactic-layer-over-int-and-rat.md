# ADR-1591: `simp` over `List`, and the tactic layer over ℤ and ℚ

Date: 2026-09-03
Status: Accepted
Lane: `tactic-list-int`

Index-summary: Amends ADR-1586 and ADR-1589, closing the two cuts each left
open. `simp::list` (ADR-1586 §4's design sketch, not built) lands as a
fourth carrier for the rewrite-chain producer: no `NatOps`-style hardcoded
carrier (`ListDev` threads `alpha`/`beta` as explicit fields, corrected per
node during traversal via `set_ambient_carrier`, since `length (map f l)`'s
own carrier differs from `map f l`'s), congruence through
`list_prelude::ops::congr_of`'s existing carrier-generic `Eq.rec` layer, and
two rule-set tiers matching `list_prelude`'s own two-phase build
(`list_only_rules` needs only `LogicPrelude` + the four theorem `NameId`s
directly, since `list_prelude::theorems` runs before `ListPrelude` itself
exists; `default_rules`/`default_rules_with_perm` add the two `Nat`-crossing
rules). Five base-case proofs in `list_prelude/theorems.rs`
(`append_assoc`, `append_nil`, `reverse_append`, `reverse_reverse`,
`length_map`) that were pure rewrite chains now route through it, projection
byte-identical. `decide` (ADR-1589) extends to ℤ (`Int.le`/`Int.lt` are
four-case `Definition`s over `Nat.le`/`Nat.lt`, not a second inductive
relation, so this reuses `decide`'s own ℕ peeling machinery directly via
`IntDev: NatOps`) and ℚ (`decide::rat` reuses `decide::int` rather than
re-deriving anything: `Rat.le`/`Rat.lt` cross-multiply into `Int.le`/
`Int.lt`, `Eq Rat` is decided separately by peeling `(num, den)`). The
`Tactic` combinator extends to both carriers: `tactic::int` mirrors
ADR-1589's ℕ design exactly (same `Then`/`First` algebra, `IntDev`'s own
inherent `Eq.rec` combinators standing in for the `NatOps` trait methods);
`tactic::rat` has NO `Simp` variant (`crate::simp` has no `rat` module —
`Rat`'s own ring normalization already lives inside `ring::rat`, and the
default `simp::int`-style rewrite-set engine is not the missing piece there)
and `Linarith` is `linarith::generic` at `Rat.orderedRing` rather than a
`linarith::rat` (which does not exist), so `Then` for ℚ is unconditionally
the sequential-fallback regime.

Index-status: Accepted

## Context

ADR-1586 §4 recorded `simp::list` as scoped, researched, and NOT built,
citing two findings: the design is not a mechanical port (`List` has no
`NatOps`/`IntDev`-style dev trait; `list_prelude` hand-numbers free-variable
ids rather than using a counter), and there was nothing to retire (every
citation of `List`'s unconditional laws outside their own declaration was
zero). ADR-1589 closed `decide` and a `Then`/`First` combinator over ℕ,
recording ℤ/ℚ as an explicit, deliberate scope cut: `linarith::int`/
`ring::int`/`ring::rat`/`simp::int` all exist and could in principle be
wired the same way, left for whichever lane needed a retirement badly
enough to justify it. This lane's brief named both gaps directly.

## Decision

### 1. `simp::list` — the fourth `simp` carrier

`crates/axeyum-lean-kernel/src/simp/list.rs`. Same outermost-first,
first-order-matching, `MAX_STEPS`-bounded design as `simp::nat`/`simp::int`,
forced into the shape ADR-1586 §4 predicted:

- **`ListDev` threads `alpha`/`beta` as explicit, per-node-corrected
  fields**, not a fixed carrier a trait method bakes in. A first
  implementation set them once per dispatch branch, matching the recursive
  DESCENT path only — and broke on `length (map f l)`, where `length`'s own
  carrier (`beta`, the map's output element type) differs from `map f l`'s
  own head (`alpha`, the map's input element type): the goal's own top-level
  match attempt ran BEFORE the traversal corrected `alpha`/`beta` for that
  specific node, so a rule that should have matched did not, and the
  `length_map` retirement (below) failed `SidesDiffer` — poisoning every
  other test in the crate, since `list_prelude`'s own build panics on any
  declaration failure. Fixed by extracting `set_ambient_carrier` and running
  it unconditionally at the top of `rewrite_step`, before matching, not only
  before descending — found by running the retirement, not by inspecting
  the traversal function.
- **A NAMED lemma over `List` needs its own IMPLICIT type argument(s)
  prepended** before the matched pattern args when cited
  (`List.append_nil alpha l`, not `append_nil l`) — `Rule` gained a
  `type_args` field after every carrier-polymorphic citation failed kernel
  type-checking identically on the first attempt.
- **A rule's result carrier cannot be recovered via `Kernel::infer`** on its
  reconstructed term: a symbolic goal's free variables are not yet
  universally quantified at proof-search time (quantification happens once,
  after the whole proof is built), and `infer` routinely fails on them
  mid-search. `Rule` carries a static `Carrier` enum instead.
- **Two rule-set tiers**, matching `list_prelude`'s own two-phase build:
  `list_only_rules` (`append_nil`, `nil_append`/`reverse_nil`/`length_nil`/
  `map_nil`/`map_cons`/`foldr_nil` as refl — defining equations the
  recursor's own base/step case gives for free — `append_assoc`,
  `reverse_reverse`, `length_map`) takes the four theorem `NameId`s
  directly, not a whole `ListPrelude` (which does not exist yet at the
  point `list_prelude::theorems` needs to call it — its own four theorems
  are local variables there, not struct fields); `default_rules`/
  `default_rules_with_perm` add `length_append`/`count_append`, which need
  `ListNatBridge`/`ListPerm`.
- **`append_assoc`'s termination is a DIFFERENT argument** than the
  "specific literal subterm" criterion ADR-1586 established for ℕ/ℤ: it
  terminates by strictly decreasing left-nested-`append` depth, not by
  consuming an annihilator. A BACKWARD copy alongside the (already-default)
  forward direction does NOT share this property and oscillates forever —
  pinned by a test that runs it and confirms `Decline::BudgetExceeded`, the
  same discipline ADR-1586's own `add_comm_alone` control uses.

Tests (`crates/axeyum-lean-kernel/src/simp/list/tests.rs`, 15 total): eight
goals (concrete and symbolic) proved and kernel-checked, one per named
default rule; three `NoProgress` goals needing induction this producer does
not attempt; two corrupted chains (`List`-carrier and `Nat`-carrier)
rejected by the KERNEL with the procedure's own convergence check disabled;
one looping rule set declining `BudgetExceeded`, not hanging; one control
that `prove()`'s goal-parsing matches `prove_eq` directly.

Land the congruence-layer gap first, as its own commit
(`crates/axeyum-lean-kernel/src/list_prelude/ops.rs`): `list_prelude::ops`'s
carrier-generic `Eq`/congruence layer (`eq_of`/`refl_of`/`congr_of`/
`symm_of`/`trans_of`) was `pub(crate)` inside a module declared `mod ops;`
(private to `list_prelude`, unreachable from `crate::simp`) — bumped to
`pub(crate) mod ops;`, a visibility fix rather than new trust surface — plus
the per-operator term builders (`nil_of`/`cons_of`/`append_of`/
`reverse_of`/`length_of`/`map_of`/`foldr_of`/`count_of`/`nat_add_of`/
`nat_succ_of`) `simp::list`'s traversal needs and that did not exist as
reusable functions before (every `declare_*` function built these inline).

### 2. Five retirements in `list_prelude/theorems.rs`

`append_assoc`, `append_nil`, `reverse_append`, `reverse_reverse`, and
`length_map`'s BASE-CASE proofs (the `nil`-case argument to
`list_induct_prop`) were each a pure rewrite chain by hand (`refl_of`/
`symm_of`/`congr_of` composed directly) — each now states the literal
`nil`-case goal and calls `simp::list::prove_eq` with a MINIMAL singleton
rule set built from new `rule_nil_append`/`rule_append_nil`/
`rule_reverse_nil`/`rule_map_nil`/`rule_length_nil` constructors, never the
full `list_only_rules`/`default_rules` (those need theorem `NameId`s that do
not exist yet at this point in the build). Declared theorem TYPES are
unchanged; every existing `list_prelude`/`bridge`/`perm` test passes
unmodified, confirming projection byte-identical — matching ADR-1581's
"citations are necessary, not sufficient" discipline: `reverse_append`'s
retirement needed the traversal to descend into `List.reverse` and cross a
`reverse_nil` refl step BEFORE reaching the already-declared `append_nil`,
not merely cite the same lemmas the hand proof happened to.

### 3. `decide` over ℤ and ℚ

`crates/axeyum-lean-kernel/src/decide/int.rs`. `Int.le`/`Int.lt` are
FOUR-CASE DEFINITIONS over `Nat.le`/`Nat.lt` (`int_prelude::defs`'s own
table), not a second inductive relation the way `Nat.le` is — so this is
"peel both operands to their `(constructor, magnitude)` shape and select
which of the four `Nat`-level facts (or `True`/`False`) the case reduces
to", reusing `decide`'s own `is_closed`/`spine`/`head_const`/`nat_value`/
`le_witness` directly (`IntDev` implements `NatOps` over the SAME embedded
`Nat` prelude `Int` is built on). `Int.lt` needs no separate witness
builder: `Nat.lt a b` IS `Nat.le (succ a) b` definitionally, so it is the
same `le_witness` call with the first magnitude incremented.

`crates/axeyum-lean-kernel/src/decide/rat.rs` reuses `decide::int` rather
than re-deriving anything. `Rat.le`/`Rat.lt` are `Definition`s over
`Int.le`/`Int.lt` by cross-multiplication; `Eq Rat` is NOT (`Rat`'s equality
is ordinary constructor equality of a reduced representative), so it is
decided separately by peeling both sides to `(Rat.num, Rat.den)`.

**One bug found by running this, not by inspection**: the first version of
`decide::rat`'s `Le`/`Lt` case called `Kernel::whnf` on the WHOLE `Rat.le a
b` goal and delegated to `decide::int::run` on the result. `Int.le`/`Int.lt`
are THEMSELVES four-case `Definition`s over `Int.rec`, so `whnf` kept
unfolding past the `Int.le` layer into ITS OWN case split, which got STUCK
on the not-yet-evaluated `Int.mul` cross-product argument and landed on
`Int.rec`'s own head — neither producer's goal parser recognised it, and
every `Rat.le`/`Rat.lt` test failed `GoalNotAtomic` until this was found by
adding a debug `eprintln!` and reading the actual head `NameId`. Fixed by
building the cross-multiplication term explicitly
(`rat_prelude::ops::{num, den_z}` + `IntDev::imul`) rather than relying on
`whnf` to recover it.

Tests: 15 for `decide::int`, 14 for `decide::rat`, the same four-battery
structure `decide.rs`'s own ℕ tests use (closed goals accepted; free
variable declines `NotClosed`; false comparison / fuel-bound-exceeded
decline `Undecidable`; corrupted terms rejected by the KERNEL). `decide::rat`'s
fixtures all have denominator `1` (an integer embedded in `Rat`, built the
same way `rat_prelude::defs`'s own `Rat.zero`/`Rat.one` constants are) — a
disclosed scope choice: it exercises the producer's full logic, and a
genuinely fractional reduced `Rat` value needs a real `gcd`-coprimality
proof this test module does not otherwise need.

### 4. The `Tactic` combinator over ℤ and ℚ

`crates/axeyum-lean-kernel/src/tactic/int.rs` mirrors ADR-1589's ℕ design
exactly: same four producers, same `Then`/`First` algebra, `IntDev`'s own
inherent `Eq.rec` combinators (`ieq_motive`/`itransport`/`isymm`) standing
in for the `NatOps` trait methods the ℕ version uses. `simp::int` gained one
new entry point, `normalize` (mirroring `simp::nat::normalize`'s own
addition in ADR-1589), and `decide::int::parse_goal` was bumped to
`pub(crate)`, shared with `crate::tactic::int` the same way
`crate::decide::parse_goal` is shared with `crate::tactic`.

`crates/axeyum-lean-kernel/src/tactic/rat.rs` has **no `Tactic::Simp`
variant**: `crate::simp` has no `rat` module. `Rat`'s own ring normalization
already lives inside `crate::ring::rat` (it normalizes to a ring normal
form internally, unlike `ring::nat`, which only covers the ring FRAGMENT and
leaves order goals to `linarith`), and building a standalone `simp::rat`
rewrite-chain engine to feed a `Then(Simp, _)` regime was out of scope for
this lane — a disclosed cut, not an oversight. `Tactic::Then` for ℚ is
therefore ALWAYS the sequential-fallback regime ADR-1589 describes for
"first is anything else": try the first tactic, and on decline try the
second on the SAME goal.

`Tactic::Linarith` for ℚ is `crate::linarith::generic::prove` at
`Rat.orderedRing`, not a `linarith::rat` (which does not exist — `Rat` has
no dedicated `IntDev`-shaped linarith the way `Int` does; the generic
producer over an arbitrary `Alg.OrderedRing` instance, ADR-1585, was
already built and unused in production before this lane). Its structure-name
bundle assembles entirely from `RatPrelude`'s own fields
(`algebra_ext.rat_ordered_ring` is the declared `Rat.orderedRing :
Alg.OrderedRing` instance term; `ordered_ring_ext` and `int.nat.structures`
are the two structure-name bundles the emitter cites) — **and its own goal
parser only recognises the `Alg.OrderedRing` record's SELECTOR
applications** (`sel(k, &structures.ordered_ring, LE, ring_instance)`), NOT
`Rat.le`/`Rat.add` directly, even though the two are defeq. A goal built
with `Rat.le` fails `linarith::generic`'s own `GoalNotAtomic` check — found
the same way as the `decide::rat` bug above, by running the first version of
the test and reading the actual decline, not by reading `Problem::new`'s
selector-derivation code first.

Tests: `tactic::int` (5): three `Then(Simp, Linarith)` goals wrapping a
COMPOUND argument in `Int.neg` (`linarith::int`'s own module docs: opaque to
its parser; `simp`'s default `neg_add` rule distributes it, which
`linarith` then parses exactly), `First([Decide, Linarith, Ring])` on a mix,
and a corrupted-glue test mirroring `crate::tactic::tests`'s own. No
`Then(Simp, Ring)` battery: `ring::int` already distributes `neg`/`sub`
fully as part of its own normal form (`ring::int`'s own module docs), so
every shape `simp`'s default rules could expose is already inside
`ring::int`'s own fragment — a genuine "`simp` needed before `ring` can
close it" case does not exist for the default rule set the way it does for
`ring::nat`'s narrower fragment, a measured negative recorded rather than
papered over. `tactic::rat` (5): three `Then` goals where the FIRST tactic
is disqualified by the goal's own SHAPE (`ring::rat` declines outright on
any non-`Eq` goal; `decide::rat` declines `NotClosed` on any goal with a
free variable), `First` aggregating declines, and a mismatched-producer-output
test (the closest analogue to a corrupted-glue test this carrier has, since
there is no glue mechanism to corrupt).

### 5. Zero retirements in `int_prelude`/`rat_prelude`

Searched by the same method ADR-1589 §3 used (grep every hand-proof body for
BOTH a default-simp-rule-shaped rewrite and an order/ring-lemma citation in
the same function, then attempt the retirement and keep only what compiles
and stays green — not inferred from the shape alone). One promising-looking
`int_prelude` hit — `sign.rs::declare_neg_one_mul`, proving the exact
statement `simp::int`'s own `neg_one_mul` default rule cites — turned out to
BE that rule's own base declaration; citing it from a rule set that already
depends on it would be circular, so it is not a retirement target by
construction. No other candidate survived: `ring::int` already distributes
`neg`/`sub` fully over `add`/`mul` as part of its own normal form (§1's
note), so every shape `simp::int`'s default rules could expose to a
`Then(Simp, Ring)` composition is already inside `ring::int`'s own fragment
directly — there is no genuine "`simp` needed first" case in `int_prelude`
for this rule set. Every `rat_prelude` order-goal hand proof states itself
via `Rat.le`/`Rat.lt` directly, not via the `Alg.OrderedRing` record's
selector applications `linarith::generic`'s own parser requires (§4's bug
note) — retiring one through `tactic::rat` would need a conversion step
between the two shapes, not a bare `Then`/`First` call, and no existing hand
proof already pays that conversion cost for free. Both `int_prelude` and
`rat_prelude` keep their full test suites green, unmodified — a measured
negative, not a silent gap.

### 6. Cost, beside `simp`/`decide`/`tactic`'s own ℕ data

Measured `--release`, `cargo run --release -p axeyum-lean-kernel --example
list_int_rat_cost`, 200 emissions per shape, prelude built once per shape,
single unpinned run on a shared box — order-of-magnitude, not a ratchet
baseline, the same caveat every other cost table in this crate carries:

| shape | search+emit | +kernel recheck |
| --- | ---: | ---: |
| `List  append l nil = l` | 0.118 ms | 0.183 ms |
| `List  reverse (reverse l) = l` | 0.125 ms | 0.193 ms |
| `List  append nil (append l nil) = l` | 0.143 ms | 0.210 ms |
| `Nat  length (append a b) = length a + length b` | 0.123 ms | 0.258 ms |
| `decide  Eq Int (ofNat 3) (ofNat 3)` | 0.003 ms | 0.004 ms |
| `decide  Int.le (negSucc 5) (negSucc 2)` | 0.005 ms | 0.017 ms |
| `decide  Int.lt (ofNat 2) (ofNat 5)` | 0.005 ms | 0.018 ms |
| `decide  Eq Rat 2 2` | 0.021 ms | 0.022 ms |
| `decide  Rat.le (-3) 0` | 0.096 ms | 0.110 ms |
| `decide  Rat.lt 2 5` | 0.110 ms | 0.138 ms |
| `Then(Simp,Linarith)  Int  -(x+y) <= -x + -y` | 4.502 ms | 4.969 ms |

`simp::list`'s cost sits in the same order of magnitude as `simp::nat`'s own
table (ADR-1586: 0.21–0.53 ms) despite the extra alpha/beta bookkeeping.
`decide::int`/`decide::rat` are the cheapest producers in the crate by a
wide margin, same as `decide`'s own ℕ data (ADR-1589) — `decide::rat` costs
more than `decide::int` because it delegates through a whole second
`Definition` unfold (`Rat.le`/`Rat.lt` into `Int.le`/`Int.lt`) rather than
deciding directly. `Then(Simp, Linarith)` over ℤ is markedly more expensive
than either alone — consistent with "the combinator's cost is the sum of
what it dispatches to" (ADR-1589), and `linarith::int`'s own certificate
search is the dominant term here, not `simp`'s one rewrite step.

## Consequences

- `simp` is now exercised over four carriers (ℕ, ℤ, ℚ, `List`); `decide` and
  the `Tactic` combinator now cover
  ℕ, ℤ, ℚ. ADR-1589's own scope-cut sentence ("left for whichever lane
  needed a retirement badly enough to justify it") is resolved for ℤ/ℚ;
  ADR-1586 §4's `List` design sketch is resolved and built.
- `simp::rat` remains unbuilt. `Tactic::Then` over ℚ is permanently the
  sequential-fallback regime unless a future lane builds one — a `Rat`-
  specific rewrite-chain engine over the SAME `IntDev` carrier `ring::rat`/
  `decide::rat` already use, following this lane's `simp::list` as the
  worked example of what a new `simp` carrier costs, is the concrete next
  step if one is wanted.
- `linarith::generic`'s goal shape (`Alg.OrderedRing` record selectors, not
  a carrier's own specialized relation) is now a measured, documented
  hazard for any future caller: a hand-stated `Rat.le`/`Rat.add` goal is
  NOT directly usable with it without the `sel`-based reconstruction
  `tactic::rat`'s own tests demonstrate.
- Every leaf producer this ADR adds still bottoms out at
  `Kernel::add_declaration` (ADR-0601) — no new trusted surface anywhere in
  this ADR.

## Alternatives considered

- **A `RatDev` struct mirroring `IntDev`**, considered and rejected: `Rat`
  is already built directly over `IntDev` throughout `rat_prelude` (its own
  module doc: "the development runs on `IntDev` … rather than on a
  development of its own"), so introducing a second wrapper type would be a
  novel design choice this lane's producers would be the only user of,
  against the grain of the existing carrier.
- **Building `simp::rat`** to give `tactic::rat` a `Then(Simp, _)` regime,
  considered and deferred: no existing `rat_prelude` retirement target
  needed it (every candidate this lane found was either a pure ring
  identity `Tactic::Ring` already closes, or an order goal `ring::rat`
  cannot touch at all regardless of a `simp` stage) — building it
  speculatively would repeat the exact unexercised-capability risk
  ADR-1586 §4 already declined once for `List`.

## Cross-references

- [ADR-1586](adr-1586-a-third-producer-decides-rewrite-chains-and-confluence-is-the-boundary.md)
  — `simp`'s design and the `List` scope cut this ADR closes.
- [ADR-1589](adr-1589-decide-and-a-then-first-combinator-close-the-tactic-layer.md)
  — `decide` and the `Tactic` combinator's ℕ design and the ℤ/ℚ scope cut
  this ADR closes.
- [ADR-1582](adr-1582-the-ring-producer-over-int-and-rat-and-what-each-carrier-costs-it.md)
  — `ring::int`/`ring::rat`, both reused directly here.
- [ADR-1585](adr-1585-linarith-generic-over-an-arbitrary-orderedring.md) —
  `linarith::generic`, wired into production (`tactic::rat`) for the first
  time by this ADR.
- [ADR-0601](adr-0601-three-producers-one-trust-anchor.md) — producers
  behind one trust anchor; every carrier this ADR adds still bottoms out at
  `Kernel::add_declaration`.
