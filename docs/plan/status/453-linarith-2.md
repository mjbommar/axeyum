# Lane: linarith-2 — extend the ℤ fragment (strictness, mul) and retire order-lemma call sites

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, linarith-2, 2026-09-03).** Continued `omega-1`'s
`crate::linarith`: fixed the `Int.add_le_add_left`/`_right` doc comments,
landed `Int.le_succ_of_lt` closing the ℤ `<`-hypothesis strictness edge, added
literal-multiplier `Int.mul` (bounded by `MAX_MULTIPLIER`), built the
retirement census tool ADR-1576's own text called for, and retired five more
order-chain theorems (three ℕ, two ℤ). ADR-1581 amends ADR-1576 with the
build-order finding that blocked half the census's first batch. Full account:
[ADR-1581](../../research/09-decisions/adr-1581-a-hand-proofs-citations-are-necessary-not-sufficient-for-retirement.md).

**Doc fix.** `Int.add_le_add_left`/`_right`'s doc comments (the `IntPrelude`
field docs and `order_add.rs`'s `declare_add_le_add_left_right` comment) said
`le a b → ∀ c, …`, implying `c` binds after the hypothesis. The declaration
(`int_theorem(name, 3, …)`) binds all three integers before it. Fixed at both
sites — commit `4a147b2bb`.

**ℤ strictness closed.** `Int.le_succ_of_lt : ∀ a b, lt a b → le (add a one) b`
lands in `int_prelude/order_add.rs`, built from `Int.lt.elim` (the CPS form
of `lt_dest`'s witness — `int_prelude` already had this, from `order_coercion.rs`)
rather than a hand-rolled `Exists.elim`: the witness `n` gives
`a + ofNat n.succ = b`, and `Le (ofNat 1) (ofNat n.succ)` (`Nat.le_succ_succ`
on `Nat.zero_le n`, `Int.le (ofNat 1) (ofNat n.succ)` by the same defeq
`le_of_ofNat_le_ofNat` documents) lifts through the now-correct
`add_le_add_left` and the witness equation to the goal. `linarith::int`'s
`collect` now weakens a `<` hypothesis to `a+1 ≤ b` directly, not merely
`a ≤ b` via `le_of_lt`. **The decline test flips**:
`a_strict_hypothesis_is_weakened_and_the_strictness_is_lost` →
`a_strict_hypothesis_keeps_its_strictness`, now declaring through the kernel
(not just checking the search emitted a term). Registered in
`derived_laws` (266, was 265) for `every_int_declaration_is_checked_and_axiom_free`.
Commit `9a44d47a7`.

**ℤ numeral multiplication.** `Int.mul` by a literal of magnitude
`0..=MAX_MULTIPLIER` (4) now parses and normalizes on either side, in both
`parse_term` (search) and `flatten` (emission). `Int.mul` does not ι-reduce at
a literal the way `Nat.mul` does — `left_distrib`/`mul_one` (both already in
`int_prelude`; `Int.mul_succ` does **not** exist, so a new private
`mul_succ_step` bridges `ofNat (succ n)` to `add (ofNat n) (ofNat 1)` by pure
ι/δ, one `left_distrib` + one `mul_one` application per copy) — real lemma
cost per copy, unlike ℕ's free unroll, which is why the bound is load-bearing
here in a way it is not on the certificate-search side. A literal past the
bound declines `NonLinear`; a genuine two-atom product (`x*y`) stays an
opaque atom, unchanged (`a_product_atom_is_still_usable_as_an_unknown` still
green). Flips `a_product_is_an_opaque_atom_even_at_a_numeral_multiplier` →
`a_numeral_multiplier_within_the_bound_now_unrolls` (declares through the
kernel); three new controls: literal-on-the-left (`mul_comm` bridge),
literal-past-the-bound (`NonLinear`), genuine two-atom product goal (still
`NoCertificate`, not `NonLinear`). `linarith::` 52 → 55 tests. Commit
`4aef98a56`.

**The retirement census** (`scripts/linarith-retirement-census.py`, registered
in `check-generated-artifact-ownership.py`): finds `nat_prelude`/`int_prelude`
`.theorem`/`.int_theorem` call sites whose hand proof — plus one level of
resolved local-helper delegation — cites only lemma names already in
`linarith`'s documented vocabulary (a small, explicit primitive addition
beyond it: `le_step`/`le_of_succ_le_succ` for ℕ, none needed for ℤ). Its
**positive control re-derives ADR-1576's own fifteen from the real
pre-retirement source** at `f7cbb3ee3^`/`5b45a40c0^` on every run — not
asserted — and finds and flags all fifteen. Excludes: a lemma the emitter
itself depends on (self-referential — caught for `add_le_add_left`/`_right`
and this lane's own `le_succ_of_lt`), a bare defeq/refl proof with zero
citations (almost always a custom recursive function's own equation —
`stirlingFirst`, `fib` — the parser cannot reach), and anything with an
induction/case-split/number-theory marker. Commits `8165f8c27`, `281b97a5d`
(the second fixes a real bug: the artifact committed in the first was
generated **before** this lane's own retirements landed, caught only by
running the ownership gate's perturb-and-restore check locally, not by
reading the diff).

**Five more theorems retired.** ℕ: `lt_of_lt_of_le`, `lt_of_le_of_lt`,
`add_lt_add_left` (`nat_prelude/order.rs`, commit `f67958bf2`) — all three
had to MOVE within `declare_order`'s build sequence, to just after
`le_of_add_le_add_right`: `linarith::nat`'s `emit_le` unconditionally cites
`add_le_add_left`/`add_le_add_right`/`le_of_add_le_add_right`, none declared
yet at these theorems' original position, and the census's citation check —
reading the OLD hand proof — cannot see that the NEW proof needs something
different. ℤ: `add_le_of_le_neg_add`, `add_le_of_le_sub_right`
(`int_prelude/order_add.rs`, commit `fda4ef0d6`) — no repositioning needed,
first attempt. `le_intro` was flagged but **not** retired: cited inside
`le_of_add_le_add_left`'s own proof, so it must be declared before that
point — strictly before the emitter's prerequisites exist. The two
requirements are mutually exclusive at that position; left as the hand proof
with a comment. Full reasoning: ADR-1581 §1–2.

**Running total with ADR-1576's fifteen: twenty theorems retired**, 308
source lines deleted, 98 added (184/45 + 124/53). `nat_prelude::` 422 green,
`int_prelude::` 81 green, `linarith::` 55 green throughout.

**The seven remaining census candidates are out of my scope** (order-chain,
per the brief) and are the next lane's brief. 886 call sites examined
(644 `nat_prelude` + 242 `int_prelude`), 879 declined; decline histogram:

    disqualifying marker (induction/case-split/number-theory)  560
    uncovered citation(s)                                      249
    no lemma citations (bare defeq/refl proof)                  44
    emitter-foundational (circular)                              26

    nat_prelude remaining candidates (3): add_add_add_comm (47 lines, pure
      additive rearrangement), le_intro (14 lines, build-order blocked —
      see above, do not re-attempt without also restructuring
      le_of_add_le_add_left), succ_injective (13 lines, Eq-concluding
      injectivity, not order)
    int_prelude remaining candidates (4): add_mul (26 lines, RING —
      distributivity), add_left_cancel (24 lines, Eq-concluding additive
      cancellation), add_left_neg (13 lines, RING — additive inverse),
      one_mul (10 lines, RING — multiplicative unit)

None of the seven conclude `Le`/`Lt`; all are additive-rearrangement, ring
identity, or plain-`Eq` cancellation facts, which is why this lane left them
for whichever lane owns ring-chain or equality-cancellation retirements —
`ring-tactic-1` per the brief's own lane split. Regenerate with
`python3 scripts/linarith-retirement-census.py` before trusting these
numbers; they are current as of `281b97a5d`.

**Fact ledger.** `check-fact-depends-derived.py --fix`: the five retired
theorems' facts gained the emitter's now-cited dependencies (e.g.
`F:nat-lt-of-lt-of-le` gained `add_le_add_left`/`add_le_add_right`/
`add_assoc`/`add_comm`/`add_right_comm`/`le_add_right`/
`le_of_add_le_add_right` — ADR-1576's own "real widening of the proof
dependency graph" note, now applying to the ledger). `validate-facts.py`:
2714 facts, 0 errors. Commit `8165f8c27`.

**Gates run.** `linarith::` 55, `nat_prelude::` 422, `int_prelude::` 81, all
`--release` via `scripts/cargo-serialized.sh`, all green; `cargo clippy -p
axeyum-lean-kernel --all-targets --lib -- -D warnings` exit 0 after every
commit; `scripts/check-links.sh` all links ok; `check-fact-depends-derived.py`
missing_edges=0; `validate-facts.py` 0 errors.

**Did not run / partial.** `scripts/check-generated-artifact-ownership.py`
(the full ceremony) takes ~15+ minutes and returned **3 FAILs**: two
pre-existing and unrelated to this lane (`KNOWN
artifacts/autogenesis/partition-edge-baseline-v1.json` — an unclassified
script; `OWNER scripts/private-helper-census.py` — did not restore from a
perturbed copy in the sandbox), and one that named MY new entry (`OWNER
scripts/linarith-retirement-census.py` — same symptom). I verified the third
directly, without the sandbox: perturbed the committed artifact, ran the bare
script, and it restored byte-identical — the same property the ownership
gate's OWNER arm measures. I did not chase why the SANDBOXED run reports
differently for either script (unrelated to my correctness, and the other
failing OWNER entry is a script I never touched) — the next lane running this
gate should re-check whether all three FAILs still reproduce, since "sandbox
not reachable" is one of the two explanations the gate's own message offers.
The workspace-wide `cargo test --workspace` / `just check` / `scripts/check.sh`
did not run (not required by the brief, and the targeted crate gates above
cover every file this lane touched).

<!-- plan-section: landed-changes -->

| 2026-09-03 | linarith-2 | doc fix: `Int.add_le_add_left`/`_right` binder order (`4a147b2bb`) |
| 2026-09-03 | linarith-2 | `Int.le_succ_of_lt` closes the ℤ `<`-strictness edge (`9a44d47a7`) |
| 2026-09-03 | linarith-2 | ℤ numeral multiplication by a literal `≤ MAX_MULTIPLIER` (`4aef98a56`) |
| 2026-09-03 | linarith-2 | three `nat_prelude` order-chain retirements, moved past their prerequisites (`f67958bf2`) |
| 2026-09-03 | linarith-2 | two `int_prelude` order-chain retirements (`fda4ef0d6`) |
| 2026-09-03 | linarith-2 | `scripts/linarith-retirement-census.py`, registered as a generated artifact, and the fact ledger's widened `depends_on` (`8165f8c27`, `281b97a5d`) |
| 2026-09-03 | linarith-2 | ADR-1581 amending ADR-1576 with the build-order and self-reference findings (`7c0490d94`) |
