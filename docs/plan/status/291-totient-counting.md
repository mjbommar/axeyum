# Lane: totient-counting — unblocking the `Nat.totient` mirror family

<!-- plan-section: lane-status -->

**DONE for this dispatch (`totient-counting`, 2026-08-29).**

**The task.** The nat-totient lane (`287-nat-totient.md`) closed 1 of 9
dispatched `ml430` `Nat.totient` mirrors and triaged the other 8 as
bottlenecking on three pieces: (1) a general "two distinct witnesses ⇒
count ≥ 2" lemma, (2) the fixed-point-free-involution pairing argument for
`totient_even`, (3) the multiplicative formula
`totient(mn) = totient(m)·totient(n)`. This lane was pointed at a candidate
shortcut for piece 2 (`Int.prod_range_pairing_collapse`,
`int_prelude/wilson.rs`) and asked to check it before building anything,
then pick one piece and land it.

**Checked the pointer first.** `Int.prod_range_pairing_collapse` is a real,
general fixed-point-free-involution/pairing lemma — but it collapses an
`Int.prodRange` to `1` under `ModEq`, over a Wilson-specific concrete
`sigma := Nat.inverseIndex`. It does **not** transport to "a
`Bool`-predicate-defined `Nat.countRange` subset has even cardinality"
without re-deriving the whole two-step structural induction against a
`Nat`-valued (not `Int.ModEq`-valued) conclusion, over a `Nat.countRange`
domain rather than `Int.prodRange`. That is genuinely separate work, not a
corollary — recorded in `totient_lemmas.rs`'s module doc so the next lane
on `totient_even` does not re-check this.

**Chose piece 1** (the general witness-counting lemma) instead, because
unlike pieces 2/3 it needed **no new induction principle** — only
composition of `Nat.countRange`'s existing defining equation
(`countRange_succ`, itself proved by `Eq.refl`) with `le_dest`/`exists_rec`
(already in `order.rs`, the same shape `le_of_add_le_add_left` uses).

**Landed, axiom-free, in `nat_prelude/totient_lemmas.rs`:**

Detail moved to [`../notes/291-totient-counting.md`](../notes/291-totient-counting.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | totient-counting | `Nat.countRange_succ_of_true`, `Nat.countRange_le_of_le`, `Nat.countRange_ge_two_of_two_witnesses` — the general "two distinct witnesses ⇒ count ≥ 2" machinery (piece 1 of the nat-totient triage), axiom-free, chosen over the `Int.prod_range_pairing_collapse`-transport route (checked, does not corollary) and the multiplicative-formula piece because it needed no new induction. Does not close any mirror by itself; the exact remaining trichotomy assembly for `totient_eq_one_iff`/`dvd_two_of_totient_le_one` is recorded in `totient_lemmas.rs`'s module doc for the next lane. |
