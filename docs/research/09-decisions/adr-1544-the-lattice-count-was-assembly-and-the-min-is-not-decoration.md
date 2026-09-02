# ADR-1544: The lattice count was assembly, and the `min` the floor lemma produces is not decoration

Status: accepted
Date: 2026-09-02
Index-summary: **Eisenstein's lemma is still NOT proved, and neither is
quadratic reciprocity.** What lands is ADR-1540's residue 4 (step 1's counting
identity, `Nat.eisenstein_floor_sum`) and its residue 1 (the additive Gauss
bijection instantiated, `Nat.gauss_fold_sumRange_eq`), plus the per-point
witness `Nat.ble_select_add_of_ne` neither had. All three admitted on the FIRST
kernel attempt, all axiom-free, because both were assembly of declarations that
already existed — ADR-1540 said of residue 4 "every input now exists and nobody
has run it", and that was correct. Two findings worth carrying: the floor
family's `Min.min` is **not** removable at the generality the theorem states
(it is removable only at `m = (p−1)/2`, `n = (q−1)/2`, which is a fact about
primes, not about counting), and the rectangle's half-planes are cheaper
spelled NON-strictly (`≤`) than strictly (`<`), because the non-strict pair is
the floor lemma's own shape and its complementarity hypothesis is exactly
"the two products differ". Residue 2 stays open and is now measured: **no
`sumRangeIf` exists in any prelude**, against a `prodRangeIf` control returning
12 declarations.
Index-status: accepted

## Context

ADR-1260 routed Eisenstein's lattice count around ADR-1135's missing-aggregate
wall and named three residues; ADR-1290 closed the floor-counting family;
ADR-1540 closed the side condition and built the additive permutation law, then
named four residues of its own. Its residue 4 read, verbatim: *"Step 2's
assembly — `Nat.countRectangle_partition` at the two strict predicates, its
per-point hypothesis discharged by this lane's `mul_succ_ne_mul_succ_of_coprime`
and its row counts named as floors by ADR-1290's
`countRange_mul_succ_le_eq_floor`. Every input now exists and nobody has run
it."*

**That claim was checked in-tree before it was believed**, per the standing rule
that a handoff's sizing is a claim about one route. `examples/shape_search`,
rebuilt from this branch (`declarations=2048`), found every named input present:
`countRectangle_partition`, `countRectangle_partition_compl`,
`countRange_mul_succ_le_eq_floor`, `countRange_mul_succ_le_eq_min`, `gaussFold`,
`gauss_fold_shift_injective_on`, `gauss_fold_shift_maps_into`,
`sumRange_permute`, `sumRange_point_change`, `mul_succ_ne_mul_succ_of_coprime`,
`leastResidue`, `gaussNegCount`. A one-character typo on the first of those
returns `ABSENT` against a `positive control: any-kind=2048`, so the positive
readings are not an unpointed tool answering emptily.

The one prerequisite ADR-1540 explicitly did NOT measure it declined to guess
about, and it was right to: **`sumRangeIf` does not exist.**
`shape_search --name-like sumRangeIf` returns `ABSENT`; the same query at
`prodRangeIf` returns 12 declarations across `Nat` and `Int`. That absence is
what still blocks residue 2, and nothing in this ADR builds one.

## Decision

### 1. The per-point witness the partition always needed

```text
Nat.ble_select_add_of_ne : ∀ a b, Not (Eq a b) →
  Eq (add (bool_select_nat (ble a b) 1 0) (bool_select_nat (ble b a) 1 0)) 1
```

`Nat.countRectangle_partition` (ADR-1260) takes its complementarity as a
BOUNDED hypothesis on the two selectors, deliberately, so that the side
condition stays in the consumer. Nothing had ever discharged that hypothesis
from a side condition — `countRectangle_partition_compl` discharges it from
`setCompl`, which a strict half-plane pair cannot supply. This is the missing
half: one `Nat.lt_or_ge` split, `ble_eq_true_of_le` and `ble_eq_false_of_lt` on
each side, and the hypothesis spent exactly once, refuting `lt_or_eq_of_le`'s
equality branch in the `b ≤ a` case.

### 2. Step 1, assembled

```text
Nat.eisenstein_floor_sum : ∀ ap aq m n,
  Eq (gcd (succ ap) (succ aq)) 1 → Lt m (succ ap) →
  Eq (add (sumRange (fun x => Min.min n (div (mul (succ aq) (succ x)) (succ ap))) m)
          (sumRange (fun y => Min.min m (div (mul (succ ap) (succ y)) (succ aq))) n))
     (mul n m)
```

`countRectangle_partition` at the two predicates, its hypothesis discharged by
§1 fed `mul_succ_ne_mul_succ_of_coprime`, then `countRange_mul_succ_le_eq_floor`
once per axis lifted across the outer sum by `sumRange_congr_lt`. Six direct
dependencies, no induction, no new arithmetic.

**Three deliberate restatements of ADR-1260's step 1**, none of which weakens
the theorem, and one of which is a strict generalization:

1. **Coprimality and `Lt m pp`, not two odd primes with `m = (p−1)/2`,
   `n = (q−1)/2`.** Nothing in the argument uses primality or the specific
   `m`, `n`. It uses `gcd p q = 1` and, at every `x < m`, the side condition's
   `Lt (succ x) pp` — which `lt_of_le_of_lt` gets from `Lt x m` (definitionally
   `Le (succ x) m`) and `Lt m pp`. `n` is unconstrained, because the side
   condition bounds only the coordinate paired with `q`; that asymmetry is
   ADR-1540's, restated here. C3 of the check script verifies that Eisenstein's
   own instances satisfy both hypotheses at all 240 ordered pairs of distinct
   odd primes below 60, so this is a generalization and not a different
   theorem.
2. **The divisors are `succ ap`, `succ aq`.** That is how ADR-1290's floor
   lemma supplies positivity, so no `Lt zero p` hypothesis is formed anywhere.
3. **The row counts stay `Min.min n ⌊·⌋`.** See below — this is the finding.

### 3. `Min.min` is not decoration

`floor_count.rs`'s module doc records that "Eisenstein's own consumer never
sees the `min` bind", and ADR-1290's control `M8` records that dropping the
`min` from the assembled identity SURVIVES numerically. **Both are true and
neither licenses dropping it here**, because they are statements about
Eisenstein's `m`, `n` and this theorem is stated at general coprime `pp`, `q`
with unconstrained `n`.

The check script separates the two readings and records both:

- `M4` — the min-free identity over the coprime range the theorem states —
  is **REFUTED**.
- `M5` — the same mutation restricted to odd prime pairs with
  `m = (p−1)/2`, `n = (q−1)/2` — is a **recorded SURVIVOR**, reproducing
  ADR-1290's `M8`.

A next lane that wants the bare floors has to prove
`div (mul q (succ x)) pp ≤ n` under `pp = succ (2m)`, `q = succ (2n)`,
`succ x ≤ m`. That is one arithmetic fact and it is true; it is simply not a
fact about counting and does not belong to this theorem.

### 4. The half-planes are spelled `≤`, not `<`

ADR-1260 and ADR-1540 both describe the two predicates as the STRICT
`p·(y+1) < q·(x+1)` and `q·(x+1) < p·(y+1)`. This assembly uses the non-strict
`ble` pair instead, for one reason: `countRange_mul_succ_le_eq_floor` is stated
at `ble (mul (succ ap) (succ j)) B`, so the non-strict predicate IS the floor
lemma's shape and needs no bridging congruence, while the strict one is
`ble (succ (mul p (succ y))) …` and would.

**The headline statement is unchanged by the choice** — the predicates appear
nowhere in it, only the floors do. And under `≤` the complementarity hypothesis
is precisely "the two products are distinct", which is
`mul_succ_ne_mul_succ_of_coprime` verbatim; under `<` it would additionally need
the equality case ruled out on both sides. `M10` records that no numeric check
can separate the two spellings away from `a = b`, which is why the declared
types are pinned character for character in the module's test file.

### 5. The additive Gauss bijection, instantiated (ADR-1540's residue 1)

```text
Nat.gauss_fold_sumRange_eq : ∀ m a, Eq (gcd a (succ (mul 2 m))) 1 →
  Eq (sumRange (fun k => succ k) m)
     (sumRange (fun j => gaussFold (succ (mul 2 m)) a (succ j)) m)
```

ADR-1540 called this "assembly, not new mathematics" and that is exactly what
it turned out to be: the same three steps `int_prelude/gauss_assembly.rs`
already runs MULTIPLICATIVELY through `Int.prodRange_permute`, with
`Nat.sumRange_permute` in place of the product.
`Nat.gauss_fold_shift_injective_on` / `_maps_into` are already `Nat`-typed and
quantified over exactly the predicates `sumRange_permute` takes, so there is no
bridging step at all; one `sumRange_congr_lt` repairs
`succ (pred (gaussFold …))` by `succ_pred_of_pos` fed the positivity half of
`gauss_fold_in_range`, whose `Le k m` hypothesis at `k := succ j` is the
congruence's own `Lt j m` definitionally.

`C5` checks the stronger fact the sum equality follows from — that the fold's
image on `[1,m]` is exactly `[1,m]`, at 356 coprime `(m, a)` pairs — so the
theorem is not passing by an accidental coincidence of sums.

## What this does NOT prove

**Quadratic reciprocity is not proved. Eisenstein's lemma is not proved.**
Step 1's counting identity is proved; step 1's mod-2 reading is not, and step 2
is not. ADR-1540's residues, updated:

1. ~~The additive Gauss bijection, instantiated.~~ **Closed here** (§5).
2. **The residue/fold reconciliation** —
   `Σ leastResidue = Σ gaussFold + pp·N − 2·Σ_neg gaussFold` — still open, and
   the reason is now measured rather than guessed: it wants a conditional sum,
   and **`sumRangeIf` exists in no prelude** (`shape_search --name-like
   sumRangeIf` → `ABSENT`; the `prodRangeIf` control → 12 declarations). The
   transport from `Nat.prodRangeIf` should be the same deletion-of-a-wrapper
   move ADR-1540 used for `countRange_permute → sumRange_permute`, but nobody
   has run it and this ADR does not claim it is easy.
3. **The mod-2 bookkeeping** over `Int.sumRange`/`Int.modEq_sumRange` — open,
   untouched.
4. ~~Step 2's assembly.~~ **Closed here** (§2), in the `min` form.
5. **New:** the `min`-free corollary at `pp = succ (2m)`, `q = succ (2n)`
   (§3). Not attempted.

## Numeric verification

Re-runnable, and **this is the command, not a claim that it passed**:

```sh
python3 docs/research/09-decisions/adr-1544-eisenstein-lattice-checks.py
```

Five claims (C1–C5) and ten controls (M1–M10). C2 sweeps 31,404 instances of
the floor identity over coprime `(pp, q)` below 21 with `m < pp` and `n < 12`;
C3 checks 240 ordered odd-prime pairs; C4 checks 452 `(m, a)` instances of the
additive bijection and C5 the stronger image claim at 356.

Exit status depends on the finding. That claim is itself measured: **12 of 12
mutations of the script exit 1** — the floor sum shifted, the fold threshold
loosened, the fold's index range shifted, one comparison made strict, three
targets moved off by one, an equality filter inverted, an image range shifted,
one refuted control re-recorded as a survivor, and each of the two recorded
survivors de-recorded.

**M5 and M10 are recorded as deliberate SURVIVORS** and asserted to survive.
M5 is the min-free reading at Eisenstein's own instances (§3); M10 is the
strict spelling of the two half-planes (§4). Neither can be separated from the
landed statement by any numeric check, which is why both declared types are
pinned character for character in
`crates/axeyum-lean-kernel/src/nat_prelude/eisenstein_lattice_tests.rs` and
`gauss_fold_sum_tests.rs`.

## Mutation table

The kernel-side controls are the two test files' own load-bearing-hypothesis
assertions, each of which exhibits a numeric instance where the theorem WITHOUT
the hypothesis is false:

| mutation | witness | result |
| --- | --- | --- |
| `eisenstein_floor_sum` without coprimality | `pp = q = 2`, `m = n = 1`: floor sum `2`, `n·m` `1` | REFUTED (`dropping_coprimality_gives_a_false_identity`) |
| `eisenstein_floor_sum` without `Lt m pp` | `pp = 2`, `q = 1`, `m = 2`, `n = 1`: floor sum `3`, `n·m` `2` | REFUTED (`dropping_the_bound_on_m_gives_a_false_identity`) |
| `ble_select_add_of_ne` without `Not (Eq a b)` | `a = b = 9`: selector sum `2` | REFUTED (`the_selector_partition_applies_and_needs_its_hypothesis`) |
| `gauss_fold_sumRange_eq` without coprimality | `m = 1`, `a = 3` (`pp = 3`): fold sum `0`, triangular sum `1` | REFUTED (`dropping_coprimality_gives_a_false_identity`) |
| the two summands of `eisenstein_floor_sum` swapped | — | **no numeric witness**; the identity is symmetric in the swap. Caught only by the pinned type. |
| the half-planes spelled strictly | — | **no numeric witness** (M10). Caught only by the pinned type. |
| the `min` dropped, at Eisenstein's own `m`, `n` | — | **SURVIVES** (M5). The landed theorem keeps the `min` because M4 refutes the min-free reading at the generality it states. |

**Three of the seven rows have no numeric witness**, which is the honest
summary: two of the mutations here are invisible to every instantiation and are
caught only by the character-for-character type pins, and one is a recorded
survivor. A next lane should not read this table as "the controls cover the
space".

## Consequences

- `NatPrelude` crossed clippy's 16 KiB `large_stack_arrays` threshold at 1026
  fields on this branch: `derive(Debug)` lowers to `debug_struct_fields_finish`
  over two LOCAL arrays with one entry per field. Silenced at the struct with a
  comment naming the real fix — ADR-1512's per-module name registry, already
  applied to `CRealPrelude` and not to this one. **The next lane to add a
  `NatPrelude` field inherits the allow, not the failure**, which is the
  outcome that matters, but the underlying growth is real and the registry
  refactor is where it should be paid.
- Three facts are registered, one per statement, all row 1 of ADR-0603's graded
  family. **Row 2 is UNASSESSED for all three** — the false readings are
  refuted numerically at named witnesses and asserted as `def_eq` controls in
  the test files, but none is stated as a kernel theorem, and no claim is made
  that one is impossible.
