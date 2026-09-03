# ADR-1587: the first checked generic-theorem retirement, and what still blocks the rest (amends ADR-1584)

Status: accepted
Date: 2026-09-03
Lane: `retire-generic-1`

Index-summary: ADR-1584 measured six carrier-specific hand proofs matching a
generic `Alg.*` theorem by type and deleted none, because ADR-1581's
build-position check was never run against them. This lane runs it (plus
the emitter-citation and fact-checker-command checks), widens the candidate
set by two (ADR-1578's own `ringMulZero` against `Int.mul_zero`/
`Rat.mul_zero`, never checked by either prior ADR), and retires the one
candidate that clears all three: `Int.add_left_cancel` now applies
`Alg.mul_left_cancel` at an inline `Alg.Group` value, after moving that one
generic theorem's declaration to the earliest position in the whole build
(`nat_prelude::structures`, right after the record spine itself). The other
seven stay, each for a checked, named reason -- three (`Rat.neg_neg`,
`Int.mul_zero`, `Rat.mul_zero`) are cited directly by the `ring`/`linarith`
producer emitters; the remaining four fail only the build-position check and
were not moved, since moving them is a real cost this lane did not spend
(`Rat.neg_neg`/`Rat.sub_self` sit inside `int_prelude`/`rat_prelude`'s
heavily-cited foundational layer; moving them is future work, not declined
work). This ADR also CORRECTS ADR-1584's own claim that
`Int.mul_le_mul_of_nonneg_left` is blocked by `linarith::int`'s emitter --
grepped directly, it is not.
Index-status: accepted

## Context

ADR-1584 §3 built a retirement measurement (matching a carrier hand proof to
a generic `Alg.*` theorem by `Kernel::infer`+`Kernel::def_eq`) and found six
matches, but did not delete any of them, citing ADR-1581's rule that a type
match is necessary, not sufficient — a candidate can be blocked because its
generic replacement's own prerequisites are not declared early enough at the
retirement site, or because a producer's own automatic proof search cites
the exact theorem being replaced. ADR-1584 recorded this as "blocked-pending-
check" for all six, explicitly not checked. This lane runs that check.

## Decision

### 1. The three checks, run for real

`scripts/generic-retirement-check.py` (committed artifact:
`artifacts/refactor/generic-retirement-check.json`, registered with
`scripts/check-generated-artifact-ownership.py`) runs, per candidate:

- **(i) emitter/instance citation** — does any file under `linarith/`,
  `ring/`, `simp/` (absent today), or `rat_prelude/algebra_instances.rs`'s
  `declare_instances` function body, cite the carrier theorem's bare name as
  a field access (`.name`)? A hit in a per-carrier emitter file (`ring/
  int.rs`, `linarith/int.rs`, ...) is attributed only to that carrier.
- **(ii) build position** — is the generic theorem (plus the instance and
  projection its instantiation needs) declared BEFORE the carrier theorem's
  own build position, in the CURRENT source? `nat_prelude::structures::
  declare_structures_all` (the abstract record spine) runs at the very start
  of the whole build. Everything else in the spine — instances, projections,
  the nine generic theorems — is declared by `algebra_instances::
  declare_algebra_instances_all`/`algebra_ext::declare_algebra_ext_all`,
  confirmed here (not assumed) to be the LITERAL LAST TWO `declare_*`-shaped
  calls in `build_rat_prelude`, immediately after `probability::
  declare_probability` — after every carrier theorem in `int_prelude`/
  `rat_prelude`, all of which build earlier. So every candidate fails this
  check BY DEFAULT; a generic theorem given its own early hook (a
  `declare_<name>_early` function called from `nat_prelude::
  build_nat_prelude_uncached`, right after the structures spine) passes for
  every carrier consumer, since nothing in `int_prelude`/`rat_prelude` can be
  declared before `nat_prelude` finishes.
- **(iii) fact checker_command** — does any fact's `evidence[*].
  checker_command` name the carrier theorem? Not a blocker (facts are
  repointed, never deleted, and the declared name/type stay byte-identical
  across a retirement) — recorded so a retirement commit's message can say
  honestly which facts it touches.

### 2. The six-row table (plus two widened rows, §4)

| generic | carrier | (i) emitter/instance cited | (ii) generic before carrier | (iii) in a fact | retires? |
| --- | --- | --- | --- | --- | --- |
| `Alg.mul_left_cancel` | `Int.add_left_cancel` | no | **no (before this lane)** | yes | **yes — landed, this lane** |
| `Alg.neg_neg` | `Rat.neg_neg` | **yes** (`ring/rat.rs`, 6 sites) | no | yes | no |
| `Alg.sub_self` | `Rat.sub_self` | no | no | yes | no (build-position only) |
| `Alg.mul_le_mul_of_nonneg_left` | `Int.mul_le_mul_of_nonneg_left` | no (see §3) | no | yes | no (build-position only) |
| `Alg.mul_le_mul_of_nonneg_left` | `Rat.mul_le_mul_of_nonneg_left` | no | no | yes | no (build-position only) |
| `Alg.pow_add` (`def_eq`, not just type) | `Rat.pow_add` | no | no | yes | no (build-position only) |

`Alg.mul_left_cancel`'s row shows its state AFTER this lane's fix (§5) — the
census was run once before the fix (confirming build position failed, like
every other row) and once after (confirming it now passes), not merely
asserted; both runs are reproducible from source, and the pre-fix state is
recorded in the git history of `int_prelude/add_basics.rs`.

### 3. A correction to ADR-1584's own claim

ADR-1584 §3 wrote: "`Int.mul_le_mul_of_nonneg_left` in particular is named
in `linarith`'s own `int.rs` emitter vocabulary (`sign_product.rs` cites it
directly)". Grepped directly for this lane's check (i): `linarith/int.rs`
never mentions `mul_le_mul_of_nonneg_left` at all. `int_prelude/
sign_product.rs` — which DOES cite `p.mul_le_mul_of_nonneg_left` at line
249 — is an ordinary `int_prelude` hand-proof file, not `crate::linarith`'s
own automatic-search emission code; it uses the theorem as a downstream
proof INPUT for `mul_nonneg_iff` and its four siblings, unaffected by a
retirement that keeps the declared name and type byte-identical. Under this
ADR's check (i) (citation by a PRODUCER's own emitter/search code, or an
instance's own proof field), `Int.mul_le_mul_of_nonneg_left` is NOT blocked.
It still does not retire here — it fails check (ii) only, the same
build-position gap every non-`mul_left_cancel` candidate has, unresolved
in this lane (§5).

This is exactly the failure mode `docs/contributor-guide/measurement-
hazards.md` and `dont-generalize-a-lanes-local-finding` name: a prior lane's
"blocked on X" is a claim about one route, checked here rather than
inherited. The ORIGINAL finding in that same table row — `Rat.neg_neg` IS
cited by `ring/rat.rs`, a real producer emitter, six sites — is confirmed
directly and stays a real blocker.

### 4. Widened search (deliverable 5): `Alg.ringMulZero` against `Int.mul_zero`/`Rat.mul_zero`

ADR-1578's own three generic theorems (`Alg.monoidIdentUnique`, `Alg.
groupInvUnique`, `Alg.ringMulZero`) were never checked against a carrier
hand proof by either ADR-1578 or ADR-1584 — both scoped their retirement
measurement to ADR-1584's six NEW theorems. Grepped all four preludes
(`nat`, `int`, `rat`, `creal`) for a carrier theorem named `mul_zero`,
`ident_unique`, or `inv_unique` (the natural Mathlib-style rendering of each
generic theorem's conclusion):

- **`monoidIdentUnique`/`groupInvUnique`**: no carrier theorem under any of
  these names in any of the four preludes. Negative, not merely unsearched —
  these are internal-uniqueness lemmas with no natural single-carrier
  restatement in this tree's existing naming.
- **`ringMulZero`**: `Int.mul_zero`, `Rat.mul_zero` (and `Nat.mul_zero`,
  which is NOT a candidate — `Alg.ringMulZero` needs a `Ring`, i.e. an
  additive inverse, and `Nat`'s multiplicative structure has none; ADR-1578
  itself only instantiates this theorem at `Int.ring`/`Rat.ring`). Both
  `Int.ring`/`Rat.ring` build `mul`/`zero` as DIRECT selectors onto `Int.mul`/
  `Int.zero` and `Rat.mul`/`Rat.zero` (`declare_instances`'s own "every
  field direct" comment), so `Alg.ringMulZero` instantiated at either
  reduces to exactly `Int.mul_zero`'s/`Rat.mul_zero`'s own stated type —
  confirmed by `Kernel::infer`+`Kernel::def_eq`, not merely by the selector
  argument, in a new test:
  `ring_mul_zero_matches_int_and_rat_mul_zero_by_type`
  (`rat_prelude/algebra_instances.rs`).
- **`creal`**: `CReal.mul_zero`, `CReal.mul_le_mul_of_nonneg_left`, and
  `CReal.pow_add` all exist as named theorems, but NONE is a candidate under
  this ADR's checks — `CReal`'s carrier equality is `Equiv` (a Cauchy-
  sequence equivalence relation), never literal `Eq` (`CReal.mul_zero : ∀ x,
  Equiv (mul x zero) zero`, confirmed from its own doc comment), and the
  entire `Alg.*` spine (ADR-1578) is built on literal `Eq` throughout. This
  is not "no instance built yet" (a scoping gap this lane could close) — it
  is a structural mismatch the current spine cannot express at all. Closing
  it needs a `Setoid`-flavored variant of the record spine (`Eq` replaced by
  a caller-supplied equivalence relation and congruence obligations
  threaded through every law), a new design decision, not a checked
  retirement. Recorded here as a real widened-search finding, explicitly
  left for a future ADR rather than attempted.

Both `Int.mul_zero` and `Rat.mul_zero` fail check (i): `linarith/int.rs`
cites `Int.mul_zero` directly (line 531, a genuine emitter dependency this
time — unlike §3's correction), and `ring/int.rs`/`ring/rat.rs` each cite
their own carrier's `mul_zero` as a numeral-coefficient base case. Both stay,
doubly blocked (also fails (ii), same as every candidate not yet moved).

### 5. The one retirement landed: `Int.add_left_cancel`

`Alg.mul_left_cancel`'s own proof needs nothing but the abstract `Group`
record (no carrier at all), so it moved to `nat_prelude::structures::
declare_mul_left_cancel_early`, called from `nat_prelude::
build_nat_prelude_uncached` immediately after `declare_structures_all` — the
earliest position in the entire build. `sel`/`mk_instance`/`derive_left_unit`
(previously private to `rat_prelude::algebra_instances`) moved to
`nat_prelude::structures` alongside it, so a prelude built before
`rat_prelude` exists at all (`int_prelude`) can build an `Alg.*` record
instance too. `declare_algebra_ext_all` no longer re-declares `Alg.
mul_left_cancel`, `AlgebraExtNames.mul_left_cancel`'s own `name_str`
interning is idempotent and still resolves to the moved declaration.

At the retirement site (`int_prelude::add_basics::declare_add_left_cancel`),
the hand proof (a `cancel_neg_add_left`-chain, ~20 lines) is replaced by
`Alg.mul_left_cancel` applied at an INLINE, ANONYMOUS `Alg.Group` value for
`Int` — not the named `Int.addGroup` (still declared, unchanged, by
`algebra_instances::declare_instances` at the tail; an anonymous value of
the same type is enough and avoids any ordering dependency on that later
declaration). The `Group` value's fields are all already declared before
this site: `add`/`zero`/`neg`/`add_assoc`/`add_comm`/`add_zero`
(`algebra.rs`, called before `add_basics`) and `add_left_neg` (this file,
the call immediately before this one in `declare_add_basics`); `zero_add`
(the LEFT identity law `Int` has no primitive for) is derived inline from
`add_comm`+`add_zero` via the same `derive_left_unit` shape ADR-1578 used
for `Nat.commAddMonoid`. The declared NAME and TYPE of `Int.add_left_cancel`
are unchanged — every downstream consumer (`add_left_inj` in the same file,
and every other citation across the tree) sees no difference.

**Lines**: `int_prelude/add_basics.rs`'s hand proof was ~20 lines; the
retired version is longer (~70 lines), because it builds the `Group` value
inline rather than referencing a pre-existing named instance — the
DUPLICATE PROOF ENGINEERING this retirement removes is conceptual (one
proof of "cancellation in a group", `Alg.mul_left_cancel`, instead of two
independent hand chains for `Int` and any future carrier), not raw line
count for this one carrier. `nat_prelude/structures.rs` grew by the moved
`sel`/`mk_instance`/`derive_left_unit`/`build_mul_left_cancel_generic`/
`declare_mul_left_cancel_early` (~280 lines, moved, not duplicated —
`rat_prelude/algebra_instances.rs` and `rat_prelude/algebra_ext.rs` lost the
same functions, net addition is the ~15-line `declare_mul_left_cancel_early`
wrapper and its call site).

### 6. What stayed, and why (deliverable 4)

- **`Rat.neg_neg`, `Int.mul_zero`, `Rat.mul_zero`** — option (b): the
  emitter citation stays. `Rat.neg_neg` is cited by `ring/rat.rs` (six
  sites); `Int.mul_zero` by `linarith/int.rs` and `ring/int.rs`;
  `Rat.mul_zero` by `ring/rat.rs`. Retiring any of these needs the citing
  producer retargeted first — `ring-tactic`/`ring`, and `linarith-generic`,
  are the lanes that would unblock them, not this one (brief's explicit
  scope boundary: this lane does not touch `linarith/`, `ring/`, `simp/`).
- **`Rat.sub_self`, `Int.mul_le_mul_of_nonneg_left`, `Rat.mul_le_mul_of_
  nonneg_left`, `Rat.pow_add`** — option (a): fails only the build-position
  check, and this lane did NOT move them. Each is declared well inside
  `int_prelude`/`rat_prelude`'s own body (`int_prelude/algebra.rs:947`,
  `rat_prelude/group.rs:327`, `rat_prelude/scaling.rs:1348`, `rat_prelude/
  polynomial.rs:314`), not at a leaf position like `Int.add_left_cancel`
  was — `Rat.neg_neg`/`Rat.sub_self` in particular sit inside `rat_prelude/
  group.rs`, upstream of matrix/probability/creal work that cites them by
  the hundreds (grepped: `Rat.neg_neg` alone has 40+ downstream citations
  across `creal/`, `rat_prelude/matrix*.rs`, `rat_prelude/probability.rs`).
  Moving the generic theorem+instance early enough to retire them is the
  SAME technique this ADR used for `mul_left_cancel`, but the RISK is
  different in kind, not degree — a mistake in `Int.add_left_cancel`'s
  narrow, single-consumer retirement site fails one theorem's own build; a
  mistake moving `Rat`'s `Group`/`Ring`/`OrderedRing` instance earlier risks
  breaking the whole downstream `rat_prelude`/`creal` build, which this lane
  did not have the budget to attempt and re-verify end to end. Left as a
  sized, named next step, not silently deferred: build `Alg.neg_neg`'s early
  hook plus a `Rat.addGroup`-shaped inline value positioned before
  `group.rs`'s own `neg_neg`/`sub_self` declarations (both fields this early
  `Rat` value needs — `add`/`neg`/`zero`/`add_assoc`/`add_comm`/`add_zero`/
  `neg_add_cancel`/`add_neg` — are confirmed available by that point in the
  build; not confirmed here is what ELSE between the old and new position
  cites `Rat.neg_neg`/`Rat.sub_self` by name, the exact ADR-1581 §1 question
  a future lane must answer by moving and recompiling, not by inspection
  alone).

## Alternatives

**Retire everything whose type matches, ignoring the build-position and
emitter checks.** Rejected — this is exactly ADR-1581's rule this ADR
exists to apply: a type match is necessary, not sufficient.

**Move all six ADR-1584 candidates' generic prerequisites early in one
pass.** Rejected for the four still inside `rat_prelude`'s foundational
layer (`Rat.neg_neg`/`Rat.sub_self`/`Rat.mul_le_mul_of_nonneg_left`/
`Rat.pow_add`) — moving `Alg.mul_left_cancel` early was safe to verify in
isolation because `Int.add_left_cancel` has exactly one internal consumer
(`add_left_inj`, in the same file); the `Rat` candidates sit upstream of
work this lane did not have budget to re-verify end to end after a
reposition, and an unverified move is worse than a named, sized negative.

## Evidence

Measured 2026-09-03 on this host. `scripts/generic-retirement-check.py`:
8 candidate rows (ADR-1584's six plus two widened), committed to
`artifacts/refactor/generic-retirement-check.json`, registered with
`scripts/check-generated-artifact-ownership.py`.

`cargo test -p axeyum-lean-kernel --lib -- structures:: --test-threads=4`:
2/2. `cargo test -p axeyum-lean-kernel --lib -- int_prelude::
--test-threads=4`: **81 passed, 0 failed**, including `int_prelude_admits_
all_declarations` and `every_int_declaration_is_checked_and_axiom_free`.
`cargo test -p axeyum-lean-kernel --lib -- rat_prelude::algebra_ext::
rat_prelude::algebra_instances:: nat_prelude::structures::
--test-threads=4`: **22 passed, 0 failed**, including `retirement_int_
add_left_cancel` (now exercising the retired proof itself, not merely a
measured candidate) and the new `ring_mul_zero_matches_int_and_rat_mul_
zero_by_type`. `cargo test -p axeyum-lean-kernel --lib -- nat_prelude::
--test-threads=4`: **424 passed, 0 failed**. `cargo test -p
axeyum-lean-kernel --lib -- rat_prelude:: --test-threads=4` (the full
whole-prelude smoke test, ADR-1584's own baseline was 258): **259
passed, 0 failed** (868.65s under concurrent-lane load), the +1 being the
new widened-search test. `cargo clippy -p axeyum-lean-kernel --lib --tests
-- -D warnings`: clean (two `items_after_statements` findings fixed along
the way — an item declared after a statement in its block, no logic
change). `cargo check -p axeyum-lean-kernel --lib`: clean, one stale-import
warning fixed (`cancel_neg_add_left`, now unused in `add_basics.rs` — still
used by `order_add.rs`/`modeq.rs`).

## Consequences

**Easier.** `sel`/`mk_instance`/`derive_left_unit` now live in
`nat_prelude::structures`, reachable from `int_prelude` — the next lane that
wants to retire a build-position-blocked `int_prelude` candidate does not
need to re-derive this move; it needs only its OWN early hook and inline
instance value, the exact shape `declare_add_left_cancel` now is.
`scripts/generic-retirement-check.py` is a standing instrument, like
`linarith-retirement-census.py`: run it, read `candidates`, and know before
attempting a retirement whether check (i)/(ii)/(iii) already block it.

**Harder.** Six candidates (four from ADR-1584, two widened) are now NAMED,
CHECKED next targets rather than an open question, but the four blocked
only by build position still need the actual move-and-recompile verification
this ADR did not spend budget on for `rat_prelude`'s foundational layer —
a future lane reading this ADR needs §6, not just the table.

**Revisit when** `ring-tactic`/`linarith-generic` retarget their emitters
away from `Rat.neg_neg`/`Int.mul_zero`/`Rat.mul_zero` (unblocking those
three's check (i)), or a lane moves `Alg.neg_neg`/`Alg.sub_self`/`Alg.
mul_le_mul_of_nonneg_left`/`Alg.pow_add`'s prerequisites early enough inside
`rat_prelude` and re-verifies the full `rat_prelude::` sweep (unblocking
the remaining four's check (ii)), or a lane designs a `Setoid`-flavored
`Alg.*` variant for `CReal` (the widened search's third finding, §4).
