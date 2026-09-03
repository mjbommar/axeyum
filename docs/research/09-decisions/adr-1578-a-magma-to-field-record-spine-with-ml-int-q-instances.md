# ADR-1578: A `Magma`→`Field` record spine, with ℕ/ℤ/ℚ instances and a generic `det_one`

Status: accepted
Date: 2026-09-03
Index-summary: ADR-1495 (2026-09-01) proved the kernel *mechanism* — a
one-constructor `Sort 2` record carrying a `Sort 1` carrier admits, selectors
exist by large elimination, and a derived theorem quantifies over the
structure — but built only one throwaway `Field` and one `VecSp`, as probes.
This ADR builds the *library* rung: a ten-record spine
`Magma → Semigroup → Monoid → CommMonoid → Group → CommGroup → Semiring →
Ring → CommRing → Field`, each independent (no inheritance — an instance is a
term you pass), with real ℕ/ℤ/ℚ instances built from already-proved prelude
lemmas, three theorems proved once over a record and instantiated at two
carriers each, and a generic `det_one` over an arbitrary `CommRing`
instantiated at ℚ. The existing `Group`/`Ring`/`CommRing`/`IsGroup*` hits in
this tree (`Nat.IsGroupOn`, `Int.IsCommRing`, `Rat.IsField`, the
`RingSignature`/`RingTelescope` reconstruction machinery) are a *different*
mechanism — a single carrier baked into each declaration, or a fresh
∀-prefixed statement re-derived from a signature's types — and none of them
abstracts over the carrier itself; each one's own module doc says structures
were believed impossible here, which ADR-1495 refuted for the kernel, not yet
for the library.
Index-status: accepted

## Context

`docs/research/09-decisions/adr-1495-abstraction-over-structures-is-already-expressible-the-gap-is-surface.md`
settled that this kernel admits a bundled record whose carrier is a `Sort 1`
*field* (not a parameter), that selectors reach it by large elimination, and
that a theorem can be proved once, quantified over the whole structure, and
instantiated at any term of that structure's type. Its own decision text is
explicit that this is a *mechanism* finding, gated on a first consumer, and
that the "second rung" — a real bundled structure with real instances,
consumed by more than its own tests — is **not yet built**.

This ADR is that rung, scoped to the north star's finite-domain-and-beyond
ladder: an abstract commutative-ring `det` is the concrete test case the
coordinator picked because it is the shape Mathlib expresses through
typeclasses and this repository has never attempted without one.

### What the tree already had, read before designing

Grepping `Group`/`Ring`/`CommRing`/`IsGroup` (as the coordinator's brief
required) turns up exactly one shape, used three times:

| hit | file | shape |
| --- | --- | --- |
| `Nat.IsGroupOn` + 3 lemmas (`group_identity_unique`, `group_inverse_unique`, `group_left_cancel`) | `crates/axeyum-lean-kernel/src/nat_prelude/group.rs` | a `Prop`-valued `Definition` over caller-supplied `op`/`e`/`inv` **bounded on a `Nat` parameter `n`** (the carrier is `{0,…,n-1}` via `Nat` itself, not an abstract `Sort 1`) |
| `Int.IsCommRing` + `Int.int_isCommRing` | `crates/axeyum-lean-kernel/src/int_prelude/ring.rs` | the same shape, **hardcoded to `Int → Int → Int` operations** |
| `Rat.IsField` | `crates/axeyum-lean-kernel/src/rat_prelude.rs` | the same shape again, **hardcoded to `Rat`** |
| `Group` (Rust struct) | `crates/axeyum-lean-kernel/src/cross_prelude_collision_tests.rs` | unrelated tooling — a group of *declarations* for cross-prelude name-collision testing, nothing mathematical |
| `RingSignature` / `RingTelescope::FullInterface` | `crates/axeyum-solver/src/reconstruct/arithmetic/ordered_ring.rs` (ADR-0515) | a **30-binder ∀-prefixed theorem**, generated fresh per signature by `generalize_over_ordered_ring`, not a kernel structure/record at all |

`int_prelude/ring.rs`'s own module doc states the reason directly: *"This
kernel has no typeclasses, no structures and no polymorphism over a bound
carrier type… so `Int.IsCommRing` is a **third** copy of the same shape, one
prefix shorter than `IsField`'s, over `Int`'s own `Eq`/operations."* That
sentence was true when it was written and is now **refuted for the kernel**
by ADR-1495's `bundled_structure_probe`/`module_over_field_probe`, which is
exactly the gap this ADR closes at the library layer: none of the three
existing bundles, and none of the telescope machinery, generalizes over the
carrier. Each is either one hand-duplicated copy per carrier, or a
freshly-generated flat ∀-list with no record type binding the pieces
together as one object that can itself be passed, projected, or reused.

### The tension with ADR-1495's stated gate, made explicit rather than silent

ADR-1495 §Decision item 4 gates the "second rung" — a bundled algebraic
structure with real instances — on item 3 (a carrier-generic congruence/
transport layer) **landing and being consumed by a lane that did not build
it**. Re-checked here: `g4_pilot_generic_congr_probe.rs` (the carrier-generic
`congr_arg` reproducing `NatOps::congr` byte-for-byte) is still only a probe
example; nothing in `nat_prelude`/`int_prelude`/`rat_prelude` has replaced its
carrier-specific `congr`/`congr_nat_to`/`congr_bool_to_nat` helpers with it.
So the letter of ADR-1495's gate is not yet satisfied.

This ADR proceeds anyway, on explicit coordinator instruction, and records
why that is defensible rather than silently overriding a standing decision:
the second-rung structures below do not *need* the generic congruence layer —
every proof term in this ADR builds its own `congr_arg`/`transport` inline
(the same free-function toolkit ADR-1495's own probes use), exactly as the
probes did. ADR-1495's gate was about not letting the **abstraction
mechanism** get ahead of its lowest-level consumer; this ADR is itself that
consumer, self-contained, and does not assume item 3 landed. The gate stays
open and unresolved for its own sake — this ADR is not evidence it is
satisfied.

## Decision

Build a spine of **ten independent one-constructor records**, each a fresh
`add_inductive` call at `Sort 2` (forced — see below), no inheritance, no
coercion, no instance resolution: `Magma → Semigroup → Monoid → CommMonoid →
Group → CommGroup → Semiring → Ring → CommRing → Field`. "Spine" names the
mathematical progression the field lists follow, not a type-level relation —
`CommMonoid` does not embed `Monoid`, it independently restates Monoid's
fields plus `comm`, the same "third copy of the same shape" pattern
`Int.IsCommRing`'s own doc names, except now generalized over `(α : Sort 1)`
instead of hand-duplicated per carrier. **An instance is a term you pass**:
`Nat.commAddMonoid : CommMonoid` is one concrete value of the record type,
built once from already-proved lemma names, nothing more.

### Field lists (mirrors Mathlib's class, minus the class mechanism)

Every record's first field is `carrier : Sort 1`; every operation and law
field is stated purely in terms of earlier fields (the same `close_pi`/
`close_lam` telescope construction ADR-1495's `bundled_structure_probe.rs`
uses). Single-direction identity/inverse laws are used wherever the record
already carries the matching commutativity field (deriving the mirror
direction by one `trans` at each use site, the way `Rat`'s own prelude has no
`one_mul` and derives it from `mul_comm`+`mul_one` where needed); records that
have no commutativity field of their own (`Monoid`, `Group`) carry both
directions as primitive fields, because nothing else can produce the second
one.

| record | new fields beyond the row above | mirrors |
| --- | --- | --- |
| `Magma` | `op : α→α→α` | `Mathlib.Mul` |
| `Semigroup` | `assoc` | `Mathlib.Semigroup` |
| `Monoid` | `e`, `identL`, `identR` | `Mathlib.Monoid` (no `npow` field — unused here) |
| `CommMonoid` | `comm` | `Mathlib.CommMonoid` |
| `Group` | `inv`, `invL`, `invR` | `Mathlib.Group` |
| `CommGroup` | `comm` | `Mathlib.CommGroup` |
| `Semiring` | `zero`, `one`, `add`, `mul`, `addAssoc`, `addComm`, `addZero`, `mulAssoc`, `mulOneL`, `mulOneR`, `distribL`, `distribR` | `Mathlib.Semiring` (no `nsmul`, no order) |
| `Ring` | `neg`, `negAdd` | `Mathlib.Ring` |
| `CommRing` | `mulComm` | `Mathlib.CommRing` |
| `Field` | `inv`, `oneNeZero`, `mulInv` (conditional: `a≠0 → a·a⁻¹=1`) | `Mathlib.Field` |

Deliberately absent, stated so it is not assumed later: **no inheritance or
coercion** (a `CommRing` cannot be passed where a `Ring` is expected; the
caller rebuilds the smaller record from the same lemma names, as the ℚ
`Ring`/`CommRing`/`Field` instances below do independently from the same
underlying `Rat.*` lemmas), **no instance resolution** (every theorem below
takes its structure as an explicit `Π`-bound argument, the caller supplies
the term), **no typeclass search, no generated `Prod`/record sugar** — every
`Pi`, `Lam`, recursor application and selector is hand-built, the same ratio
ADR-1495 measured (1,774 probe lines bought one `Field`, one `VecSp`, 13
selectors, 2 theorems) and reports as the honest cost of this mechanism.

### The universe guard forces `Sort 2`, measured

Every record's constructor carries `carrier : Sort 1` as a genuine field (not
a parameter), so by ADR-1495 Measurement 4/5 — and the guard
`KernelError::ConstructorFieldUniverseTooBig` landed there specifically for
this shape — every one of the ten inductives **must** be declared with result
sort `Sort 2`; declaring any of them at `Sort 1` is refused by the guard that
now runs on every `add_inductive` call. `examples/algebra_spine_probe.rs`
below carries this as a live control per record (not just once for `Field` as
ADR-1495 did): the same field list at `Sort 1` must be refused, and at
`Sort 2` must be accepted. All ten pairs measured — see Evidence.

### Instances: ℕ (add) `CommMonoid`, ℤ `CommRing`, ℚ `Field`

Each instance is `<Record>.mk` applied to already-proved prelude constants —
no new algebra, exactly `Int.int_isCommRing`'s and
`rat_prelude::field::declare_rat_is_field`'s pattern (bare references to
existing theorems, nothing rebuilt):

- `Nat.commAddMonoid : CommMonoid` — `Nat.add`, `Nat.zero`, `Nat.add_assoc`,
  `Nat.zero_add`, `Nat.add_zero`, `Nat.add_comm`.
- `Int.commRing : CommRing` — `Int.add`, `Int.mul`, `Int.neg`, `Int.zero`,
  `Int.one`, `Int.add_assoc`, `Int.add_comm`, `Int.add_zero`, `Int.mul_assoc`,
  `Int.one_mul`, `Int.mul_one`, `Int.left_distrib`, `Int.add_mul`
  (= `distribR`), `Int.add_neg`, `Int.mul_comm`.
- `Rat.field : Field` — the same eleven ring lemmas at `Rat.*` plus
  `Rat.mul_comm`, `Rat.inv`, `Rat.one_ne_zero`,
  `Rat.mul_inv_cancel_of_ne_zero` (already stated `∀ q, q≠0 → q·q⁻¹=1`,
  syntactically the record's `mulInv` field up to unfolding `Not`).

Checked by **reduction**, not merely by the `add_declaration` accept: for
each instance, projecting a law field back out
(`CommRing.mulComm Int.commRing`) is confirmed `def_eq` (iota-reduces
through the recursor to the exact literal proof term, e.g. `Int.mul_comm`)
and its **type** is compared against the source lemma's own rendered type —
the "reduction, not source text" evaluation discipline
`docs/contributor-guide/kernel-proof-engineering.md` requires for any new
`Definition`.

### Three generic theorems, each proved once and instantiated at two carriers

- **`Monoid.identUnique`** — `∀ (M:Monoid) (e':M.carrier), (∀a, M.op a e'=a) →
  e'=M.e`. Proof: `e' =symm(identL M e') = M.op M.e e' =hyp M.e= M.e` — the
  same two-substitution-and-`trans` shape `Nat.group_identity_unique`
  documents, ported to the abstract record. Instantiated at
  `Nat.commAddMonoid` (concrete: `e':=0`, hypothesis `Nat.add_zero`,
  conclusion `0=0`) and at a fresh `Rat.commMulMonoid : CommMonoid` built for
  this purpose (`Rat.mul`/`Rat.one`; `identL` derived from `mul_comm`+
  `mul_one`) — concrete: `e':=1`, hypothesis `Rat.mul_one`.
- **`Group.invUnique`** — `∀ (G:Group) (a b c:G.carrier), G.op b a=G.e →
  G.op a c=G.e → b=c`, the same shape as `Nat.group_inverse_unique`'s
  `b=b·e=b·(a·c)=(b·a)·c=e·c=c`, ported. Instantiated at `Int.addGroup`
  (`Int.add`/`Int.neg`, concrete `a:=2,b:=-2,c:=-2`) and `Rat.addGroup`
  (`Rat.add`/`Rat.neg`, concrete `a:=(1/2),b:=-(1/2),c:=-(1/2)`).
- **`Ring.mulZero`** — `∀ (R:Ring) (a:R.carrier), R.mul a R.zero=R.zero`,
  proved **without ever using a multiplicative identity** — only
  `distribL`, `addZero`, `addComm`, `negAdd`, `addAssoc` — matching the task's
  "from the ring axioms alone". Chain: `x:=mul a zero`; `x = mul a
  (add zero zero) = add x x` (`distribL`); then the additive-group half:
  `zero = add (neg x) x = add (neg x) (add x x) = add (add (neg x) x) x =
  add zero x = x`, so `x=zero`. Instantiated at `Int.ring` and `Rat.ring`
  (both built independently of the `CommRing`/`Field` instances above, from
  the same underlying lemma names — no inheritance).

Each instantiation is checked **both** ways per
`kernel-proof-engineering.md`'s rule: the generic theorem applied to a fully
concrete witness (numerals, a named lemma as the hypothesis) reduces and
type-checks, *and* the generic theorem itself is checked against a genuinely
free structure variable `M`/`G`/`R` (its own statement, before any
instantiation) so a self-consistent but wrong chain cannot hide behind
numerals that happen to agree.

### The payoff: `det_one` over an arbitrary `CommRing`

`Rat.det`'s cofactor recursion (`rat_prelude/matrix_det.rs`) is parameterized
over `CommRing`'s carrier and operations: a generic `sumR`/`altSignR`
(`Nat.rec` into `R.carrier`, the constant-motive twin of `Rat.sumRange`) and
`detR` (`Nat.rec` with a function-typed motive, the same device
`Int.sumMaps`/`Rat.det` use, now over `R.carrier` instead of a fixed carrier).
`CommRing.detOne : ∀ (R:CommRing) (A:Nat→Nat→R.carrier), detR R A 1 =
A 0 0` is proved by one unfold (`detR _ 1` is `sumR` over the singleton
range, collapsing via `addZero`+`mulOneL`/`mulOneR` and the `altSignR`/`detR`
base cases, both `Eq.refl`) — **`det_mul`/multiplicativity is explicitly not
attempted**, matching the task's scope and `matrix_det.rs`'s own stated
boundary (agreement/evaluation only, no multiplicativity).

Instantiated at `Rat.commRing` (a `CommRing` built from the same `Rat.*`
lemmas as `Rat.field`, independent term, no inheritance): `CommRing.detOne
Rat.commRing A` is checked `def_eq`, and its **type**, once
`Rat.commRing`'s `carrier`/`add`/`mul`/… selectors iota-reduce, is compared
against `Rat.det_one : ∀ A, Rat.det A 1 = A 0 0`'s own rendered type — see
Evidence for whether this holds outright or needs an explicit bridge lemma
(`Rat.det`'s own recursion is over the *specific* `Rat.add`/`Rat.mul`/etc., so
the two `detR`/`det` recursions are independently-built `Nat.rec` instances
over the *same* functions reached through different routes — the same
"two independently-built `Nat.rec` instances" boundary
`kernel-proof-engineering.md`'s `Nat.multichoose` entry names, so an exact
syntactic `def_eq` between `detR Rat.commRing` and `Rat.det` is not assumed in
advance).

## Alternatives

**Extend the existing `IsGroupOn`/`IsCommRing`/`IsField` `Prop`-bundle
pattern with a fourth, `CommRing`, carrier-generic version.** Rejected: that
pattern is a `Prop` over caller-supplied *loose* operations, not a record — it
cannot be a value passed around, projected, or itself quantified over by a
later `Sort`. It also cannot express "the identity" or "the carrier" as an
object; every consumer must re-supply the whole operation list. The whole
point of this ADR is that a *record* is a first-class term.

**Route everything through `RingTelescope`-style generated ∀-prefixes
instead of a record.** Rejected for the stated deliverable: a telescope
generalizes a *specific proved refutation*'s dependency list into binders: it
answers "what does this argument need", not "state a theorem about every
commutative ring". It has no notion of an *instance* as a single term, and
composing two telescope-quantified facts needs re-deriving the telescope
each time. It remains the right tool for ADR-0515's job (interface
specification/control) and is untouched here.

**Give the spine real inheritance (`Ring` embeds `CommMonoid` etc.).**
Rejected per the brief and per this kernel's lack of coercion: embedding
would need either a coercion mechanism (none exists) or literally nesting one
record as a field of another (`module_over_field_probe.rs`'s pattern), which
works but means every consumer of `Ring.add` must first project through the
embedded sub-record, and there is no reduction benefit since laws are not
reused across records anyway (no inheritance means no proof reuse either).
Kept flat, matching the explicit instruction and the existing `IsCommRing`
precedent of hand-duplicating rather than composing.

## Evidence

Measured 2026-09-03 on this host.

**The spine.** `nat_prelude::structures::structures_tests`: all ten records
(`Magma` 2 fields, `Semigroup` 3, `Monoid` 6, `CommMonoid` 7, `Group` 9,
`CommGroup` 10, `Semiring` 13, `Ring` 15, `CommRing` 16, `Field` 19) admit at
`Sort 2` with every field's `Sort 1`-refused control firing (the guard
panics the whole suite if it does not, so ten green runs is ten fired
controls, not a sampled subset), every inductive/recursor/selector present
in the environment, and a positive control (an all-`Prop` record IS accepted
at `Sort 1`, so the guard is not blanket-refusing every inductive).

**Instances and theorems.** `rat_prelude::algebra_instances::
algebra_instances_tests`, plus the full `rat_prelude::` suite once
(`rat_prelude_is_axiom_free` and `rat_prelude_builds` both green, confirming
the whole ℚ prelude — including every ADR-1578 declaration — is still
axiom-free): 6/6 passed. `monoid_ident_unique` applied at fully concrete
`(Nat.commAddMonoid, e':=0, Nat.add_zero)` and `(Rat.commMulMonoid, e':=1,
Rat.mul_one)` — the FIRST attempt failed exactly the way it should: applying
the theorem (typed over `Alg.Monoid`) to the `Alg.CommMonoid` instances is a
real `TypeMismatch`, because this spine has no inheritance, and the fix was
building genuine `Alg.Monoid` values from the same underlying lemma
constants. `group_inv_unique` and `ring_mul_zero` each applied at two
independently-built structure instances (`Int.addGroup`/`Rat.addGroup`,
`Int.ring`/`Rat.ring`), closed over symbolic elements.

**The payoff.** `CommRing.detOne` (as `Alg.commRingDetOne`) is declared and
admitted, instantiated at `Rat.commRing` (a `CommRing` built independently of
`Rat.field`, from the same `Rat.*` constants), and type-checks over a
symbolic matrix `A`. The measurement neither this ADR's design section nor
the task brief predicted in advance: **`detR(Rat.commRing, 1, A)` IS
`def_eq` to `Rat.det(A, 1)` at a SYMBOLIC `A`** — `true`, not merely equal at
every concrete instantiation. This is despite `detR` and `Rat.det` being two
independently-built `Nat.rec` recursions (the shape
`docs/contributor-guide/kernel-proof-engineering.md`'s `Nat.multichoose`
entry names as usually NOT `def_eq` even when they agree on every value).
They agree here because everything the `n=1` unfolding touches — `add`,
`mul`, `zero`, `one` — is, through `Rat.commRing`'s own fields, literally
`Rat.add`/`Rat.mul`/`Rat.zero`/`Rat.one`, so both sides reduce (iota + beta,
no law needed for this part) to the identical normal form. This is a
one-`n`-value measurement, not a claim of agreement at general `n` — nothing
here attempts `det_mul` or reasons about the two recursions' minors.

**Fact ledger.** `F:alg-monoid-ident-unique`, `F:alg-group-inv-unique`,
`F:alg-ring-mul-zero`, `F:alg-comm-ring-det-one` — one per generic theorem,
each `epistemic_status: proved`, `axiom_footprint: []`.
`python3 scripts/validate-facts.py`: 2718 facts, 0 errors.
`check-settled-fact-statements.py --write`: 2449 pins, `unpinned=0`.
`gen-py-prelude-fields.py`: `nat=1094+30` (ten `RecordNames`' `ind`/`mk`/
`rec`), `rat=506+16` (`AlgebraNames`' sixteen names) — both exactly the
expected counts; `--check` confirms up to date; `cargo check -p axeyum-py`
clean.

Full detail (field-index tables, the two real bugs the test suite's own
first run caught, and every SHA) is in
`docs/plan/status/453-structures-1.md`.

## Consequences

**Easier.** A later "fourth rung" structure (e.g. an ordered field, a module)
can reuse this ADR's field-list/selector/instance pattern directly; the
generic term-building toolkit (`pi_over`/`lam_over`/`eq_of`/`transport`/
`congr_arg`, ported from ADR-1495's probes into real prelude code) is now
shared rather than re-derived per probe.

**Harder.** Ten new records is ten more names competing for collision with
whatever a future lane names `Group`/`Ring`/`Field` inside a *carrier's own*
namespace (this spine lives under its own root namespace, not `Nat.*`/
`Int.*`/`Rat.*`, specifically to avoid the "a prelude can declare into
another prelude's namespace" hazard `kernel-proof-engineering.md` records).
Every future instance is hand-built with no inheritance, so the "one Rust
function per carrier" duplication `Int.IsCommRing`'s own doc complains about
is not eliminated by this ADR — it is *generalized* (the LAW statements are
now shared and proved once), but each *instance* is still bespoke assembly
of existing lemma names, same as before.

**Revisit when** ADR-1495's item-3 gate (a carrier-generic congruence layer,
landed and consumed by someone else) actually lands — at which point this
ADR's hand-built `congr_arg`/`transport` calls in the three generic theorems
and `det_one` become candidates to route through the shared layer instead of
their own copies, the same substitution `NatOps::congr`/`congr_nat_to` are
named as candidates for in ADR-1495.
