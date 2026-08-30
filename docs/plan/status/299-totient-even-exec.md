# Lane: totient-even-exec — `Nat.countRange_reversal_even` built and verified

<!-- plan-section: lane-status -->

**DONE for this dispatch (`totient-even-exec`, 2026-08-29).**

## The task

Execute `docs/plan/status/295-totient-even.md`'s hand-traced plan for
`Nat.totient_even`. That plan identified one genuinely new piece — a general,
`totient`-independent evenness lemma over `countRange` — and flagged it as
the whole risk, since it was traced without compiling anything. This dispatch
built it, found and fixed the one place the trace didn't hold, and verified
it against the kernel.

## What was built: `Nat.countRange_reversal_even`

```
Nat.countRange_reversal_even :
  forall (L : Nat) (h : Nat -> Bool),
    (forall j, Lt j L -> Eq Bool (h (sub (pred L) j)) (h j)) ->
    (forall j, Lt j L -> Eq Bool (h j) true -> Not (Eq Nat j (sub (pred L) j))) ->
    Even (countRange h L)
```

`L` is bound outermost (not `h` first, as the plan's prose sketch has it) —
an equivalent, differently-curried statement, chosen so `L` is directly the
`WellFounded.fix`-eliminated variable.

New file: `crates/axeyum-lean-kernel/src/nat_prelude/count_range_reversal.rs`
(~890 lines after formatting). Registered in `nat_prelude.rs` (field, doc,
`name_str` constructor, `mod` declaration, dispatch call right after
`declare_parity_all` — see "what did not hold" below for why not right after
`declare_totient_all`). Listed in `nat_prelude_tests.rs`'s `theorem_names`
(the environment-derived coverage assertion, `every_nat_declaration_is_
checked_and_axiom_free`, requires this — it caught the omission on the first
full-suite run). One new concrete-instance test,
`count_range_reversal_even_applies_at_a_vacuous_concrete_instance`.

Nothing in the statement or proof mentions `gcd`/`totient` — it is a pure
counting fact, reusable well beyond this task.

## Which traced steps held, and which didn't

**Held exactly as traced:**

Detail moved to [`../notes/299-totient-even-exec.md`](../notes/299-totient-even-exec.md).

