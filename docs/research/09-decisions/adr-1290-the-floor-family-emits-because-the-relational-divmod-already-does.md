# ADR-1290: The floor-counting family EMITS, because the relational `divMod` already does

Date: 2026-08-31
Status: Accepted
Lane: `eisenstein-floors`

Index-summary: ADR-1260's residue 1 — naming the rectangle partition's row counts as floors — was predicted to "fight `Nat.div`/`Nat.mod` being stuck at symbolic arguments". It does not, and the reason is that the emitter was already in the tree four modules earlier: **`Nat.div_mod_mul_le_iff` is the floor adjunction stated against the RELATIONAL `divMod d n q r`, with the quotient an ordinary bound variable.** Three declarations land, all admitted on the FIRST kernel attempt, all axiom-free: `Nat.countRange_succ_le_eq_min` (the counting core, no division in the statement at all), `Nat.countRange_mul_succ_le_eq_min` (the bridge, `div` appearing nowhere), and `Nat.countRange_mul_succ_le_eq_floor` (the executable corollary, one `div_mod_exec` instantiation). The `min` is `Min.min`, not `Nat.sub` — the count saturates and truncated subtraction is what ADR-0970/ADR-0985 had to route around. Two of the six mutants are recorded as surviving, and one of the evaluation probes has **no unique kill by construction** and says so.
Index-status: Accepted

## Context

[ADR-1260](adr-1260-eisenstein-routes-around-the-missing-aggregate-wall.md)
landed `Nat.countRectangle_partition` and named three residues between it and
Eisenstein's lemma. This lane was sent at residue 1, with the brief predicting
the hardest possible answer:

> **`Nat.div` and `Nat.mod` are STUCK at symbolic arguments.** A hypothesis
> `m mod k = r` is a liability. Prefer a lemma that EMITS a shape over a
> hypothesis about a residue. […] if the answer is that floors cannot be made to
> emit, say so precisely and stop.

That framing is right about the hazard and wrong about this family, and the
distinction is worth stating precisely because it decides how the remaining
quadratic-reciprocity work should be shaped.

## Decision

**The floor family EMITS, and nothing new had to be built to make it.** The
deciding step is one already-declared theorem:

```text
Nat.div_mod_mul_le_iff : ∀ d n q r s, divMod d n q r → (d*s ≤ n ↔ s ≤ q)
```

`Nat.divMod d n q r := n = d*q + r ∧ r < d` (`division.rs`) is a RELATION, not a
projection. `q` and `r` are ordinary universally-quantified variables, so there
is nothing in the statement that could be stuck — the same structural move as
`Nat.even_or_odd`, which produces `m = h + h` rather than taking `m mod 2 = 0`.
`Nat.div_mod_exec : ∀ ap n, divMod (succ ap) n (div n (succ ap)) (mod n (succ ap))`
closes the loop at the very end, once, when an executable form is wanted.

So the family is:

| declaration | statement | division in it |
| --- | --- | --- |
| `Nat.countRange_succ_le_eq_min` | `countRange (fun y => ble (succ y) c) n = Min.min n c` | **none at all** |
| `Nat.countRange_mul_succ_le_eq_min` | `divMod a B q r → countRange (fun j => ble (mul a (succ j)) B) n = Min.min n q` | **none** — `q` is a bound variable |
| `Nat.countRange_mul_succ_le_eq_floor` | `countRange (fun j => ble (mul (succ ap) (succ j)) B) n = Min.min n (div B (succ ap))` | one, and only in the conclusion |

All three admitted by `Kernel::add_declaration` on the **first attempt**, all
`axiom_footprint` empty, `nat_prelude::` 320 passed / 0 failed.

### The step that decides it, stated exactly

`countRange` is `Bool`-valued, so the bridge is a `Bool` equation rather than an
`Iff`:

```text
ble (mul a (succ j)) B  =  ble (succ j) q
```

`div_mod_mul_le_iff` at `s := succ j` gives the `Iff` between the two `Prop`s;
`ble_eq_of_iff` (private to `floor_count.rs`) turns it into the `Bool` equation
by two `Nat.lt_or_ge` splits, so **no negated `Prop` is ever formed** —
`ble_eq_true_of_le` and `ble_eq_false_of_lt` on each side, with one impossible
branch closed through `lt_of_lt_of_le` + `lt_irrefl`. `Nat.countRange_congr`
moves it under the count.

### Why `Min.min` and not `Nat.sub`

The count saturates. Written with subtraction it is `n − (n − min n c)` or a
disjunction, and ADR-0970/ADR-0985 took the disjunctive shape for
`gaussCountBleClosedFormDisj` precisely to keep `Nat.sub`'s truncation out of an
induction. `Min.min` states the same thing with no truncation, and both branch
lemmas (`min_eq_left`, `min_eq_right`) were already proved in
`minmax_lemmas.rs`. The whole step induction is then: split `lt_or_ge j c`,
learn the boolean, and read off which `min` branch fires.

`Min.min` is also why this declaration sits last in the build order —
`declare_minmax_lemmas_all` is the only dependency that is not far above.

## What was nearly rebuilt

**`Nat.gaussCountBleClosedFormDisj` is this lemma at `a := 2`**, and it has
existed since ADR-0985. Its statement counts
`ble (succ half) (mul 2 (succ j))` — the COMPLEMENT of what is wanted here —
against `div half 2`, in the disjunctive `Nat.sub`-avoiding shape. Had this lane
started from the general form without reading `gauss_lemma.rs`, it would have
produced a second, incompatible proof of the same induction.

It is not superseded: it is stated about the complement and consumed by
`gaussNegCountTwoClosedForm`, so the two coexist. But the next lane wanting a
count-versus-floor lemma at some other predicate should read both before
building a third.

Two more things that were in the tree and might have been rebuilt:

- **`bool_true_or_false`** (`ops.rs`) — the constructive `Bool` dichotomy, which
  had been three independent copies until it was shared. `ble_eq_of_iff` does
  not need it (the `lt_or_ge` route is cleaner) but the first draft did.
- **`Nat.countRange_congr`** is UNCONDITIONAL (pointwise at every `i`, not just
  below `n`), and `count_range_congr_lt` is the bounded form. The unconditional
  one is what this family needs, because the adjunction holds at every index.

## Numeric verification

Re-runnable, and **this is the command, not a claim that it passed**:

```sh
python3 docs/research/09-decisions/adr-1290-floor-count-checks.py
```

Five claims (C1–C5) and eight controls (M1–M8). C1 is the counting core over
1,681 `(c, n)` pairs; C2 is the adjunction over 37,820 `(a, B, s)` triples; C3
is the two composed over 37,820 `(a, B, n)` triples; C4 checks that Eisenstein's
row count IS C3 and that its `min` never binds there, over 240 ordered prime
pairs; C5 assembles the lattice identity over 120 unordered pairs. Exit status
depends on the finding: any control that behaves other than recorded exits 1.

**Two controls are recorded as SURVIVING, deliberately, and the script asserts
that they survive** — so a change making either of them fail would also fail the
script:

- **M7** — `min c n` in place of `min n c`. `Min.min` is commutative in VALUE, so
  no numeric check and no evaluation test can distinguish the two argument
  orders. Only the declared type does, which is why
  `the_family_states_the_intended_types` pins all three character for character.
- **M8** — the `min` dropped entirely from the assembled lattice identity C5.
  True, because `⌊q·x/p⌋ ≤ (q−1)/2` for `1 ≤ x ≤ (p−1)/2` and distinct odd
  primes. That is a fact about primes, not about counting, so it belongs to the
  consumer; the lemma stays unconditional.

ADR-1260's own script was re-run rather than inherited:
`python3 docs/research/09-decisions/adr-1260-eisenstein-checks.py` — PASS, exit
0, all eight claims and ten controls as recorded.

**ADR-1275 has no check script**, contrary to the brief that sent this lane. Its
controls are the `int_prelude` cargo tests (`the_sum_range_family_states_the_
intended_types` and the evaluation probe), and its mutation table was produced
by editing Rust, not by a Python driver. There is nothing to re-run for it
beyond `cargo test -p axeyum-lean-kernel --lib int_prelude::`.

## The mutation table

Three outcomes: **declaration rejected / statement false / admitted, true, and
not your theorem.** Each mutant was applied in this lane's own worktree and
reverted with `git checkout` immediately after; none was ever on disk in the
shared checkout.

MUTATION-TABLE-PLACEHOLDER

## What these controls cannot catch

Stated as plainly as ADR-1275 stated its own limit, because the shape is the
same:

> **The evaluation probes in `floor_count_tests.rs` have NO unique kill on any
> of the three declarations.** They evaluate `Nat.countRange` of a concrete
> predicate against hand-computed numerals, so what they pin is the COUNTING
> CONVENTION the statement is written in — that the bound is exclusive, that
> `ble (succ y) c` means `y < c` and not `y ≤ c`, that `div 11 3` rounds down.
> They never instantiate the theorems. Every mutation of the *proof* is caught
> by the trusted gate first, because `countRange_zero`/`countRange_succ` are both
> `Eq.refl` and pin the recursion exactly; every mutation of the *statement* that
> changes a value is caught by the gate too, since the proof no longer checks.

The probes are kept for the reason ADR-1275 kept its own: they are the only
thing that would notice if `Nat.countRange`'s own convention ever changed under
this family, and they are what makes the `succ` shift's meaning legible to a
reader.

The second thing no control here can catch is **whether `Min.min n q` is the
right way to state the saturation for the consumer that does not exist yet.**
C4 measures that Eisenstein's row count never makes the `min` bind, so a
consumer will always immediately discharge it with `min_eq_right`. That is a
mild cost paid for an unconditional statement, and it is a judgement, not a
measurement.

## What this does NOT prove

**Eisenstein's lemma is not proved, and neither is quadratic reciprocity.** What
is settled is ADR-1260's residue 1, in general form, and the sizing question the
brief actually asked.

The remaining residues, updated:

1. ~~The row count is a floor.~~ **Closed here.**
2. **The side condition.** `p·y ≠ q·x` for `1 ≤ x ≤ m`, `1 ≤ y ≤ n`, distinct
   odd primes — Euclid's lemma, which this kernel has. Unchanged, and
   ADR-1260's C5b verified it at 504 prime pairs.
3. **Eisenstein's lemma itself.** `Int.sumRange` exists now (ADR-1275) with
   `sumRange_sub`, `sumRange_ofNat` and an unconditional `modEq_sumRange`, so
   the mod-2 bookkeeping has its tools. The remaining work is the classical
   derivation `(a−1)·Σk = p·(F + N) − 2·Σ_neg`, which needs the
   `leastResidue`/`gaussFold` machinery in `gauss_lemma.rs` related to a floor
   sum — and *that* relation is where a `div` finally has to be named, through
   `countRange_mul_succ_le_eq_floor` or `div_mod_exec` directly.

## The generalisable finding

**"`Nat.div` is stuck" is a statement about the PROJECTION, not about division.**
This prelude carries a relational Euclidean specification with a constructive
existence theorem, an adjunction in both the `≤` and `<` directions, uniqueness,
and an executable-satisfies-the-relation bridge — five theorems that between
them mean *no proof about floors ever has to reduce one*. Every one of them
predates this lane.

So before sizing any future target as blocked on stuck arithmetic, ask whether
the prelude carries a RELATIONAL form of the stuck operation. `divMod` is the
one that exists; the same question is worth asking of `Nat.sqrt`, `Nat.log` and
`Nat.factorization`, each of which has the same projection-shaped hazard.
