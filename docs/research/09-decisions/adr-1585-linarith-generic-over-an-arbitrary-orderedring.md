# ADR-1585: `linarith::generic` — a `≤`/`=` emitter over an arbitrary `Alg.OrderedRing`

Status: accepted
Date: 2026-09-03
Lane: `linarith-generic`

Index-summary: ADR-1584 §5 named three blockers to retargeting `linarith`
(ADR-1576/1581) at `Alg.OrderedRing` instead of a fixed `NatPrelude`/
`IntPrelude`: missing field citations, a generic numeral builder, and
decoupling emission from `IntDev`/`NatDev`. This lane closes all three.
Blocker 1: three order lemmas (`Alg.add_le_add_right`,
`Alg.le_of_add_le_add_right`, `Alg.add_le_add`) derived generically from
`OrderedRing`'s five primitive order laws — no new record field.
Blocker 2: `Alg.ofNat : OrderedRing -> Nat -> carrier` (a `Nat.rec` over
`R`'s own `add`/`one`/`zero`) plus `ofNat_add` and `ofNat_le_ofNat_of_le`
(the latter conditional on an explicit `zero <= one` witness — not
derivable from the five order laws alone). Blocker 3:
`linarith::generic`, a `≤`/`=` Farkas emitter built only from an
`OrderedRing` term's selectors and the lemmas above, with a fragment
deliberately short of `linarith::int`'s (no `<`, no literal
multiplication — both scoped out explicitly, not silently). Reproves all
seven `int_prelude` retirement targets ADR-1576/1581 named, symbolically,
at `Int.orderedRing`, matching the hand-proved type exactly; proves three
goals at `Rat.orderedRing` that had no `linarith` route before this ADR;
declines three false goals; and three corrupted-certificate tests confirm
the KERNEL — not the procedure's own check — is what rejects a bad
witness. `linarith::int`/`linarith::nat` are unchanged and un-retired: see
§4 for why, and what `linarith::generic` still cannot express.
Index-status: accepted

## Context

ADR-1584 §5 measured the gap and declined to close it: "Structurally
reachable, but not with the record as built here, and this ADR does not
attempt it." Its own three blockers, quoted:

1. "The record itself is missing fields the emitter's fixed chain cites"
   — `add_le_add_right`, `le_of_add_le_add_right`, and the whole `lt`/
   strict fragment; "some are cheaply derivable... the `lt` fragment is
   genuinely new, not a derivation."
2. "A generic numeral-construction routine" — the emitter's literal
   handling currently reaches for `Nat.succ`/a carrier's own literal
   representation, neither of which exists generically.
3. "Decoupling the emission closures from `IntDev`/`NatDev`" — a real
   refactor, not a drop-in swap.

This ADR takes each in turn, and is explicit about what it does NOT close:
the `lt` fragment (blocker 1's genuinely-new half) is left open, and
`linarith::generic`'s own scope is narrower than `linarith::int`'s as a
direct consequence (see §3).

## Decision

### 1. Three derived order lemmas, no new record field

`crates/axeyum-lean-kernel/src/rat_prelude/ordered_ring_ext.rs` (new),
each a real `∀ (R:OrderedRing) …` kernel theorem, proved once from
`OrderedRing`'s five primitive order laws (`le_refl`, `le_trans`,
`le_antisymm`, `add_le_add_left`, `mul_nonneg`) plus `Ring`'s `neg`/
`negAdd`/`addComm`/`addAssoc`/`addZero` — never a new field on the record
itself, matching the brief's explicit preference ("derive them
generically... as `Ring.toCommGroup` derived `identL`/`invL`", ADR-1584):

- **`Alg.add_le_add_right`** — from `add_le_add_left` + `addComm`,
  rewriting both sides of `add_le_add_left(c,a,b,h)` across
  `add c x = add x c`.
- **`Alg.le_of_add_le_add_right`** — cancels `c` by adding `neg c` on the
  left of the hypothesis, then rewrites both sides via a generic
  `Eq (add (neg y)(add x y)) x` cancellation (the same shape
  `Int.add_neg_cancel_left` hand-proves once per carrier, built here
  generically from `assoc`+`addComm`+`negAdd`+`addZero`). No standalone
  hand-proved `Int.*`/`Rat.*` counterpart exists under this exact name
  (only the `Iff` form `add_le_add_iff_right`), so this is a NEW fact at
  both carriers, checked for type-correctness rather than compared
  against a hand proof.
- **`Alg.add_le_add`** (two-sided) — cites `add_le_add_right` by name plus
  `add_le_add_left` + `le_trans`.

**Evaluation**: `add_le_add_right`/`add_le_add` instantiated at
`Int.orderedRing`, closed over `(a,b,c)`/`(a,b,c,d)`, have the SAME TYPE
(`Kernel::infer` + `Kernel::def_eq`, never a doc comment) as the existing
hand-proved `Int.add_le_add_right`/`Int.add_le_add` — both already existed
as kernel theorems, so this is a genuine (unattempted) retirement
candidate pair, not merely a type-shape coincidence.

### 2. `Alg.ofNat` and its two laws

Same file. `Alg.ofNat : Pi (R:OrderedRing), Nat -> R.carrier`, a `Nat.rec`
over `R`'s own `add`/`one`/`zero` (`ofNat R 0 = R.zero`,
`ofNat R (succ n) = add (ofNat R n) one`) — the constant-motive-in-`n`
shape `Alg.npow` (ADR-1584) already uses, since the return type does not
depend on `n`. Declared in `rat_prelude/ordered_ring_ext.rs`, not
`nat_prelude/structures.rs`, because `Nat.rec` does not exist yet at the
point the algebra spine itself is declared (`nat_prelude.rs`'s own build
order interns the spine using only `LogicPrelude`, strictly before `Nat`'s
own inductive is declared) — measured, not assumed, by trying the
placement in `structures.rs` first.

- **`Alg.ofNat_add`**: `∀ R m n, ofNat R (m+n) = add (ofNat R m)(ofNat R
  n)`, by induction on `n` (the argument `Nat.add` recurses on, exactly
  `Alg.pow_add`'s own reason) — base needs only `addZero`, the step needs
  one congruence on the IH plus one `addAssoc`.
- **`Alg.ofNat_le_ofNat_of_le`**: `∀ R, le R.zero R.one -> ∀ m n, Nat.le m
  n -> le (ofNat R m)(ofNat R n)`, by induction on the `Nat.le`
  DERIVATION (`Nat.le.rec`, `m` fixed as the recursor's parameter — the
  same shape `nat_prelude/order.rs`'s `le_trans` uses), not on `n`
  directly. **The `zero <= one` hypothesis is load-bearing and explicit,
  not incidental**: it is NOT derivable from `OrderedRing`'s five order
  laws alone — they say nothing about the ring unit's sign, and nothing in
  the record rules out an instance where `one < zero`. Both
  `Int.orderedRing` and `Rat.orderedRing` supply it easily
  (`le_of_lt` applied to the carrier's own `zero_lt_one`), but a generic
  `∀ R` statement cannot assume it.

**Evaluation**: `Alg.ofNat Int.orderedRing 3` reduces (`def_eq`) to
`Int.ofNat 3`, with a discriminating negative control against
`Int.ofNat 4` (so a copy-pasted wrong numeral would fail loudly).
`ofNat_add`/`ofNat_le_ofNat_of_le` both type-check symbolically (closed
over free `m`, `n`, and — for the second — the `Nat.le` witness and the
`zero<=one` witness) at both `Int.orderedRing` and `Rat.orderedRing`.

### 3. `linarith::generic`, scoped short of `linarith::int` by design

`crates/axeyum-lean-kernel/src/linarith/generic.rs` (new). A `Problem`
struct caches every selector/derived-lemma application against one fixed
`(ring, R:OrderedRing)` term as plain `ExprId`s (mirroring `IntPrelude`'s
own `Copy`-snapshot pattern, just built from selectors instead of
top-level constants) — no `IntDev`/`NatDev` field or method appears
anywhere in the module. The certificate SEARCH
(`super::{find_certificate,find_combination}`) is untouched, confirming
ADR-1584's own finding that it was already carrier-agnostic.

**The fragment is deliberately narrower than `linarith::int`'s, and this
is stated in the module's own doc comment rather than discovered by a
reader hitting a stuck term later**:

- **No `<` at all.** `Alg.OrderedRing` has no `lt` field (ADR-1584's own
  "genuinely new, not a derivation" verdict, unresolved here too); a `<`
  hypothesis parses as a useless opaque atom, a `<` goal declines
  `GoalNotAtomic`. This is the first stuck shape a caller will hit.
- **No literal multiplication.** None of the seven retirement targets or
  three new-capability goals below need it, and a generic literal-mul
  unroller would need `distribL`/`mulOneR` chained the way
  `linarith::int`'s `mul_succ_step` chains `Int.left_distrib`/`mul_one` —
  real, scoped-out work. A literal-multiplier subterm parses as an opaque
  atom (sound: an unknown ring element, never a wrong answer).

Everything else — the additive `≤`/`=` fragment, Farkas combination, the
constant-first canonical-form normalizer (flatten / bubble-sort arrange /
prepend-zero / reassociate) — is `linarith::int`'s exact structure, ported
mechanically: `IntDev` method calls become either direct selector
applications (`R.add`, cached once) or calls into the generic
`Eq`/`congr`/`trans`/`subst` toolkit
(`nat_prelude::structures`'s free functions, used directly rather than
through the `EqB` wrapper this lane also added — a wrapper cannot be held
across a RECURSIVE call site such as `flatten`/`reassoc` without a real
borrow conflict, since it holds `&mut Kernel` for its own lifetime;
`EqB` is used only in `ordered_ring_ext.rs`'s non-recursive derivations).

**A genuine bug the port surfaced that `linarith::int` does not have**:
the shared `find_certificate` accepts any residual satisfying
`LinForm::is_nonneg_cone` (nonnegative CONSTANT *or* nonnegative ATOM
coefficients — the ℕ-style reading, "an atom is an unknown natural"), and
returns the SMALLEST-WEIGHT certificate meeting that bar. Over an
arbitrary `OrderedRing`, an atom is not guaranteed nonnegative (exactly
`linarith::int`'s own stated reason for its `is_constant()` check on the
residual), so a smaller-weight certificate whose residual still mentions
an atom can be found FIRST and then correctly refused by `emit_le` — with
no fallback to the larger, genuinely-constant certificate the goal
actually needs. Measured on `0<=a, 0<=b |- 0<=a+b`: the naive port
declined a true goal. Fixed by exposing `find_combination` (`pub(crate)`,
was private to `linarith.rs`) and calling it in `prove_le` with the
STRICT acceptance `is_constant() && const_term() >= 0` directly, so the
search itself skips the unusable smaller certificate. `linarith::int`/
`nat.rs` are unaffected — this only widens what `find_combination`'s
existing signature is called with, and does not change
`find_certificate`'s own behaviour.

## Evidence

Measured 2026-09-03 on this host.

**Retirement, seven of seven, all matching by TYPE** (`Kernel::infer` +
`Kernel::def_eq`, closed over free variables the same way
`algebra_ext.rs`'s own retirement tests do): `Int.add_le_add_three`,
`Int.add_le_of_le_neg_add`, `Int.add_le_of_le_sub_left`,
`Int.add_le_of_le_sub_right`, `Int.add_left_comm`,
`Int.add_neg_cancel_left`, `Int.add_neg_cancel_right` — ADR-1576's five
plus ADR-1581's two `int_prelude` retirements, every one re-proved through
`linarith::generic` at `Int.orderedRing` from the SAME hypothesis/goal
shapes, admitted on the first attempt after the fixes in §3/below.

**New capability at `Rat.orderedRing`** (no `linarith` route over ℚ
existed before this lane): transitivity (`a<=b, b<=c |- a<=c`), sum of
nonnegatives (`0<=a, 0<=b |- 0<=a+b` — the exact goal that found the
`find_combination` bug above), and a slack-1 goal (`a<=b |- a<=b+1`,
exercising `Alg.ofNat`/`ofNat_le_ofNat_of_le` genuinely — a companion
assertion confirms the SAME goal declines when no `zero_le_one` witness is
supplied, so the gating is real, not decorative).

**Three false goals decline**: `a<=b |- b<=a`, `a<=b<=c |- c<=a`,
`|- a+1<=a` (no hypotheses) — all `Decline::NoCertificate`/similar, none
silently "proved".

**Three corrupted certificates, `verify: false`** (the procedure's own
arithmetic check disabled, so only the KERNEL can catch a bad witness):
multiplier 2 where 1 is correct, residual 0 where 1 is required, and a
hypothesis slot carrying a proof of a DIFFERENT true proposition
(`le_refl c` in a slot typed `le a b`) — all three rejected at
`Kernel::infer`. A fourth test, the positive control, confirms the SAME
route (`emit_le_from_certificate`, `verify: false`) admits the UNCORRUPTED
certificate, so the three rejections are not evidence of a broken
emitter.

**Gates**: `cargo test -p axeyum-lean-kernel --lib -- linarith::
--test-threads=4`: **72 passed, 0 failed** (17 new
`linarith::generic::generic_tests`, every pre-existing `linarith::{tests,
int_tests,core_tests}` unaffected). `-- structures:: rat_prelude::
algebra_ext:: --test-threads=4`: **17 passed, 0 failed** (ADR-1578/1584's
own suites unaffected by the `EqB`/`Problem` additions).
`cargo clippy -p axeyum-lean-kernel --lib --tests -- -D warnings`: clean.
`rustfmt --edition 2024` on every touched file.

**Cost, measured `--release`, single unpinned run on a shared host (order-
of-magnitude, not a baseline — see `docs/contributor-guide/
measurement-hazards.md` on why an unpinned shared-box number is advisory
only, and `linarith::cost`'s own module doc for the same caveat ADR-1576
made about its own numbers)**: 200 repeats of `add_le_add_three`'s shape
(3 hypotheses, one hop each), search only (kernel recheck excluded, same
convention `linarith::cost::Row::search_ms` uses):

| route | ms/term |
| --- | ---: |
| `linarith::int` (per-carrier, `IntDev`) | 8.591 |
| `linarith::generic` (`Alg.OrderedRing`, `Int.orderedRing`) | 9.686 |

Roughly 13% slower on this one shape — plausible and small: every term
`linarith::generic` builds carries one extra selector application per
field access (`App(Const(field_sel), R)` before the field can be used,
where `linarith::int` reaches the same field as a bare top-level
constant), and nothing else differs — the search, the certificate, and
the normalizer's structure are identical. **One shape, one host, not a
claim the ratio holds generally** — `linarith::generic`'s narrower
fragment (§3) means it has fewer cases to walk for goals within its
scope, which could cut the other way on a goal shape this measurement did
not try. Reproduce with `cargo test --release -p axeyum-lean-kernel --lib
-- linarith::generic::generic_tests::measured_ms_generic_vs_int --exact
--ignored --nocapture`.

## `linarith::int`/`linarith::nat`: kept, not retired — see status doc for the full accounting

Per ADR-1581's rule (a hand proof's type match is necessary, not
sufficient for retirement — the replacement's own prerequisites must be
checked against the retirement site's actual build-sequence position),
**nothing is deleted by this ADR**. Two separate reasons `linarith::int`
specifically cannot be deleted, neither of them a build-order technicality:

1. **`int_prelude`'s own `declare_*` call sites still cite
   `linarith::int::declare` directly** — retargeting even one of the
   seven retirement targets at `linarith::generic` would need those call
   sites rewritten to build an `Int.orderedRing` term and go through
   `linarith::generic::prove` instead, which this ADR does not attempt
   (matching ADR-1581's own "recording this as blocked-pending-check, not
   as blocked outright" for its own five candidates).
2. **`linarith::int` covers ground `linarith::generic` structurally
   cannot reach without further work**: the whole `<`/strictness
   fragment (`Int.lt`, `le_succ_of_lt`, `lt_of_lt_of_le`, `lt_irrefl`),
   literal multiplication via `Int.mul` unrolling, and the refutation
   route (`¬(≤)` goals via `find_refutation`) — none of which
   `Alg.OrderedRing` as built (here or in ADR-1584) can express or this
   module attempts. `linarith::nat` additionally serves ℕ, which has no
   negation and is therefore not an instance of `OrderedRing` at all (no
   `neg` field) — `linarith::generic` cannot reach ℕ under any
   circumstance without a separate `Alg.OrderedSemiring`-shaped record,
   not attempted here.

## Alternatives

**Add `lt`/`add_lt_add_of_le_of_lt`/`mul_pos` to `Alg.OrderedRing` in this
ADR, closing blocker 1 completely.** Rejected on scope: ADR-1584 already
measured this as "genuinely new, not a derivation," and none of this
lane's seven retirement targets or three new-capability goals need it.
Building it without a concrete consumer risks the same "mechanism ahead
of consumer" gap ADR-1578's own Context section flags for a different
layer. Left named as the first stuck shape (§3) for a future lane with an
actual `<`-goal retirement target in hand.

**Rewrite `int_prelude`'s seven retirement-target `declare_*` sites to go
through `linarith::generic` instead of `linarith::int`, deleting the
hand/per-carrier versions.** Rejected per ADR-1581's rule directly: doing
so needs (a) `int_prelude` to build an `Int.orderedRing` term and hand it
through at each site, a nontrivial call-site change seven times over, and
(b) each site's actual build-sequence position checked against
`linarith::generic`'s own prerequisite declarations (`Alg.ofNat`,
`Alg.add_le_add`, …), exactly the check ADR-1581 §1 found necessary and
this lane did not perform. Left as a sized future task, not silently
deferred: the retirement candidates are all seven, matched by type,
listed above.

## Consequences

- `linarith::generic` is a genuine second producer over the SAME trust
  anchor `linarith::nat`/`linarith::int` use (`Kernel::add_declaration`/
  `Kernel::infer`), reachable at any future `Alg.OrderedRing` instance —
  the moment a fourth ordered-ring carrier exists in this tree, this
  module reaches it with zero additional emitter code, which is exactly
  the promise a carrier-generic tactic layer makes and `linarith::int`/
  `nat` structurally cannot (each is one Rust module per carrier).
- **Easier**: the next lane that wants `<` over `Alg.OrderedRing` has
  `Alg.add_le_add`/`add_le_add_right`/`ofNat`/`ofNat_add` already built
  and tested to start from, and `linarith::generic`'s own module doc
  names the exact three things still missing.
- **Harder**: `linarith` is now a producer with THREE emission layers
  (`nat`, `int`, `generic`) sharing one search, and any future change to
  `Certificate`/`LinForm`'s semantics (e.g. widening `is_nonneg_cone`)
  needs checking against all three call sites, not two — `generic.rs`'s
  own stricter `find_combination` call is exactly this kind of
  per-emitter constraint that a shared-search refactor could silently
  break.
