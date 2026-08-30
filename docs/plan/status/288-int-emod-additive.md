# Lane: int-emod-additive — the `emod` additive law + the three `even_add*` mirrors

<!-- plan-section: lane-status -->

**Lane block (DONE, int-emod-additive, 2026-08-29).** The `int-parity-two`
lane closed 7 of 10 `ml430-int-*` division-by-two mirrors and left exactly
three open, all needing "an additive compatibility law for `emod` under
`Int.add`'s branch table" that it sized as a separate, comparably-large task.
This lane built that law and closed all three.

```
F:ml430-int-even-add-3c4536e3       F:ml430-int-even-add-bc8e1394
F:ml430-int-even-add-one-af33da18
```

**The law did NOT need a fresh `Int.rec` case split on `Int.add`'s branch
table**, contrary to the sizing in `docs/plan/status/282-int-parity-two.md`.
`Int.ModEq` (`modeq.rs`) already carries general additive congruences —
`mod_eq_add_right : ModEq n a b → ModEq n (a+c) (b+c)` and
`mod_eq_add_left : ModEq n a b → ModEq n (c+a) (c+b)` — and composing them
via `mod_eq_trans` gives the additive law directly:
`ModEq n a b → ModEq n c d → ModEq n (a+c) (b+d)` (`modeq_add`,
`parity.rs`). One composition, no new case analysis. This is the answer to
the brief's "check whether the `Nat` `div_mod_shift` shape transports"
question: **it did not need to** — `div_mod_shift`'s shape (shift a
dividend by an exact multiple of the divisor, via `div_mod_unique`) solves a
different problem than "what is `(m+n) % 2` given `m % 2`/`n % 2`", and the
`ModEq` route already in this prelude was the closer fit.

**The route, in full:**

Detail moved to [`../notes/288-int-emod-additive.md`](../notes/288-int-emod-additive.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | int-emod-additive | `emod` additive law (`Int.ModEq`-based `modeq_add`) + `Int.even_add`/`Int.even_add'`/`Int.even_add_one` closed, all axiom-free; two `nat-*` stragglers left for a future lane |
