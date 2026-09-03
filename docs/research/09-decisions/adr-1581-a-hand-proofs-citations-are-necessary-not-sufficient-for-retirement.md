# ADR-1581: a hand proof's citations are necessary, not sufficient, for retirement

Status: Accepted
Date: 2026-09-03
Lane: `linarith-2`

Index-summary: A census over `nat_prelude`/`int_prelude` hand proofs whose
lemma citations lie entirely in `crate::linarith`'s documented vocabulary
finds *candidates*, not *targets*: five of the first twelve it found declined
at `Kernel::add_declaration` with `UnknownConst`, because `linarith::declare`
depends on the EMITTER's own fixed lemma chain being already declared at the
retirement site's position in the build sequence — a constraint the hand
proof's own citations say nothing about. This ADR amends ADR-1576 with that
finding, the two ℤ fragment extensions (`Int.le_succ_of_lt` closing the `<`
strictness edge, literal-multiplier `Int.mul` up to `MAX_MULTIPLIER`), and
five more retirements: three `nat_prelude` (`lt_of_lt_of_le`, `lt_of_le_of_lt`,
`add_lt_add_left`, moved within `declare_order`'s build sequence to after
their prerequisites), two `int_prelude` (`add_le_of_le_neg_add`,
`add_le_of_le_sub_right`, no repositioning needed). Running total with
ADR-1576's fifteen: **twenty theorems**, 308 source lines deleted, 98 added.
Index-status: Accepted

## Context

ADR-1576 retired fifteen hand-written order proofs by hand-picking them and
measuring the result; it did not say how to find the *next* fifteen. This
lane built `scripts/linarith-retirement-census.py`, a static census over
every `<dev>.theorem`/`<dev>.int_theorem` call site in `nat_prelude`/
`int_prelude`, flagging one as a candidate when its hand proof — plus one
level of resolved local-helper delegation — cites only lemma names in
`linarith::nat`/`linarith::int`'s own documented vocabulary (their module
docs' "lemma | role" tables), excluding disqualified shapes (induction,
case-split, `Exists`, number-theoretic families) and self-citations to
lemmas the emitter itself depends on.

Its positive control re-derives ADR-1576's own fifteen from the real
pre-retirement source at `f7cbb3ee3^`/`5b45a40c0^` on every run — not
asserted — and finds and flags all fifteen.

## Decision

### 1. A build-order dependency the census cannot see, and does not need to

The census flagged twelve strong candidates (six `nat_prelude`, six
`int_prelude`) by lemma-citation coverage alone. Attempting them in place,
four failed — not with `Decline` (the search declined to find a certificate)
but with the KERNEL refusing an EMITTED term:
`UnknownConst { name: NameId(225) }`. The search succeeded; the term it built
cited `Nat.add_le_add_left`, which does not exist yet at
`lt_of_lt_of_le`/`lt_of_le_of_lt`/`add_lt_add_left`'s position inside
`declare_order`'s own build sequence — `add_le_add_left`/`add_le_add_right`/
`le_of_add_le_add_right` are declared **later in the same function**.

`emit_le`'s chain is unconditional: every ℕ `Le` proof the emitter produces
cites `add_le_add_left`, `add_le_add_right`, `le_of_add_le_add_right`,
`le_add_right`, `le_trans`, regardless of what the hand proof it replaces
used. `lt_of_lt_of_le`'s hand proof cited only `le_trans` (already available)
— the census correctly read the OLD proof, and the OLD proof's citations say
nothing about what the NEW one needs, because linarith does not replay a hand
proof's reasoning; it searches independently and always reaches for the same
fixed chain.

**The fix, verified by compiling, not predicted:** move the three
declarations to immediately after `le_of_add_le_add_right` within
`declare_order` (nothing between the old and new positions cites any of the
three names — checked). `nat_prelude::` 422 tests green afterward, first
attempt after the move.

`Nat.le_intro` — also flagged, also failing the same way — could **not** be
moved: `le_of_add_le_add_left` (declared before `add_le_add_left`/
`add_le_add_right`/`le_of_add_le_add_right`) cites `p.le_intro` in its own
proof, so `le_intro` must exist BEFORE that point, which is strictly before
the emitter's prerequisites exist. The two requirements are mutually
exclusive at this position. Left as the hand proof, with a comment recording
why — a sized negative, not a defect in the census.

`int_prelude`'s two remaining candidates (`add_le_of_le_neg_add`,
`add_le_of_le_sub_right`) needed no repositioning: `declare_add_le_of_le_sub`
runs well after every ℤ-emitter prerequisite is declared. Not every
candidate hits this; roughly half did, in this batch of five.

**The rule this generalises:** a candidate's hand-proof citations bound what
the OLD proof needed. They do not bound what `linarith::declare` needs — that
is fixed per carrier, independent of the goal, and must be checked against
the retirement site's actual position in the build sequence separately, by
attempting the retirement and reading the kernel's answer.

### 2. A lemma the emitter depends on cannot be retired to the emitter

Separately, the census's own `linarith_foundational` scan (of `linarith/
nat.rs`/`linarith/int.rs`'s own `p.<name>` citations) excludes any candidate
whose name the emitter itself uses — `Nat.add_le_add_left`/`_right`,
`Int.add_le_add_left`/`_right`, and this lane's own `Int.le_succ_of_lt`
(cited inside `collect`'s strictness weakening). Retiring one would make the
emitter's search for ITS OWN theorem reference a name the kernel has not
declared yet — the same `UnknownConst` failure mode as §1, but structural
rather than positional: no repositioning fixes it, because the dependency is
on the theorem's own future self.

### 3. Two ℤ fragment extensions land with this batch

- **`Int.le_succ_of_lt : ∀ a b, lt a b → le (add a one) b`**, closing the
  strictness edge ADR-1576 recorded as declined (`a < b ⊢ a+1 ≤ b`). Built
  from `Int.lt.elim` (the CPS form of `lt_dest`'s witness) rather than a
  hand-rolled `Exists.elim`. `linarith::int`'s `collect` now weakens a `<`
  hypothesis to `a+1 ≤ b` directly instead of merely `a ≤ b` via `le_of_lt`.
- **Literal-multiplier `Int.mul`**, bounded by `MAX_MULTIPLIER` (4) on either
  side. `Int.mul` does not ι-reduce at a literal the way `Nat.mul` does, so
  each copy costs a real `left_distrib` + `mul_one` chain (a new private
  `mul_succ_step` helper) rather than a free unfold — the same reason the
  bound matters for the certificate search now applies to this unrolling
  too. A literal past the bound declines `NonLinear`; a genuine two-atom
  product (`x * y`) is still an opaque atom, unchanged.
- Two doc-comment fixes recorded by ADR-1576 as owed: `Int.add_le_add_left`/
  `_right` now correctly document all three integers binding before the
  hypothesis, at both the field docs and the `declare_add_le_add_left_right`
  comment.

`linarith::` 55 tests green (was 52): two ℤ suites gained a positive
(strictness proved, literal mul unrolls) and a corresponding control
(out-of-range literal declines `NonLinear`, genuine product still opaque).

### 4. The measured population, and what is left

| | `nat_prelude` | `int_prelude` |
| --- | ---: | ---: |
| `.theorem`/`.int_theorem` call sites | 644 | 242 |
| already retired (ADR-1576 + this lane) | 13 | 7 |
| remaining candidates | 3 | 4 |
| declined | 641 | 238 |

Decline histogram, both carriers combined (879 total): disqualifying marker
(induction/case-split/number-theory family) 560, uncovered citation(s) 249,
no lemma citations — a bare defeq/refl proof, almost always a custom
recursive function's own defining equation (`stirlingFirst`, `fib`) the
parser cannot reach — 44, emitter-foundational (circular) 26.

**The seven remaining candidates are NOT order-chain sites** and were
deliberately left to whichever lane owns ring-chain retirements:
`add_add_add_comm`/`succ_injective` (ℕ, pure additive rearrangement/
injectivity, no `Le`/`Lt` conclusion), `le_intro` (ℕ, build-order blocked,
§1), `add_mul`/`add_left_neg`/`one_mul` (ℤ, ring identities —
distributivity, additive inverse, multiplicative unit), `add_left_cancel`
(ℤ, additive cancellation, `Eq`-concluding). This lane's scope was
order-CONCLUDING (`Le`/`Lt`) theorems; a census candidate is not automatically
in scope for the lane that finds it.

## Consequences

- `scripts/linarith-retirement-census.py` is the standing instrument for the
  next lane: run it, read `candidates`, and know before attempting a
  retirement that a `disqualifying marker`/`uncovered citation` decline means
  don't bother, while a clean flag still needs the build-order question §1
  raises answered by compiling, not predicted from the report alone.
- `derived_laws`/`prelude_theorem_inventory`-adjacent tests (`every_int_
  declaration_is_checked_and_axiom_free`) needed `Int.le_succ_of_lt`
  registered; the equivalent ℕ ledger (`kernel_declaration_projection`)
  needed no update, since none of the ℕ moves are new declarations.
- `check-fact-depends-derived.py --fix`: the five retired theorems' facts
  gained the emitter's fixed dependency set in `depends_on` — the same
  "real widening of the proof dependency graph" ADR-1576 noted, now applied
  to the fact ledger. `validate-facts.py`: 2714 facts, 0 errors.

## Cross-references

- [ADR-1576](adr-1576-a-tactic-is-a-producer-and-its-return-is-measured-in-retired-proofs.md)
  — the tactic-as-producer decision and the first fifteen retirements, which
  this ADR amends with the build-order and self-reference findings.
- [ADR-1510](adr-1510-a-contract-is-sized-by-the-frontier-and-a-decline-dies-with-its-fact.md)
  — a contract is sized by the frontier; `linear-arithmetic-v1`'s live
  population stays empty for the same reason ADR-1576 recorded.
