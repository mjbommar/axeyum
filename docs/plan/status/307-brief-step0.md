# Lane: brief-step0 -- retrieval moves out of the lane and into the dispatcher

<!-- plan-section: lane-status -->

**Lane block (`DONE -- tool, nine mutation-verified controls, and `just brief``,
brief-step0, 2026-08-29).**

## Headline

`scripts/brief-step0.py` produces the evidence a brief should *contain* rather
than *ask for*, in **0.2-0.5 s** against a warm snapshot. `just brief <targets>`
is the loop-closing mechanism, and §6 argues why a gate was **not** the right
answer here.

On its first real use it found **14 of 141 open facts whose statement already
has an exact-constant match in the kernel environment** -- including
`F:ml430-nat-dvd-antisymm-507f9026`, which is `open` while `Nat.dvd_antisymm` is
proved at precisely its statement.

## 1. The two numbers, re-measured before anything was built on them

| practice | docs | of 272 | pct |
| --- | --- | --- | --- |
| mutation testing (`mutation`/`mutant`, case-insensitive) | 125 | 272 | **46.0%** |
| `shape_search` / `shape-search` | 13 | 272 | **4.8%** |

```
/usr/bin/grep -lEi 'mutation|mutant' docs/plan/status/*.md | wc -l        -> 125
/usr/bin/grep -lE  'shape_search|shape-search' docs/plan/status/*.md | wc -l -> 13
ls docs/plan/status/*.md | wc -l                                          -> 272
```

GNU grep at `/usr/bin/grep`, not the interactive `ugrep` shell function.
Positive control: `/usr/bin/grep -lE '[a-z]' docs/plan/status/*.md | wc -l` →
**272** -- the query reaches every document, so a zero would have meant
something. Negative control: a fabricated token → **0**.

The retrospective measured 269 documents; three landed since. Both percentages
are unchanged to one decimal place. **Compliance tracks mechanization, not
emphasis** survives re-measurement.

## 2. What the tool reports

Four sections per target, plain text, pasteable into a brief.

**1 -- Does it already exist?** Every declaration in a kernel-built snapshot is
ranked by the **multiset of constants in its RENDERED TYPE** against the fact's
`formal.statement`. Names are never compared: a name search cannot find a lemma
whose name you do not know, which is the case that has cost the work. Carrier
and sort tokens are held out of the multiset and compared separately, because a
rendered type spells the carrier once per binder *and* once per `Eq.{1}`
argument while a surface statement spells it once per binder group.

It separates propositions a name search cannot:

```
F:ml430-nat-add-eq-zero-64233539   ∀ {m n : ℕ}, m + n = 0 ↔ m = 0 ∧ n = 0
  [1.00] Nat.add_eq_zero_iff   … Iff (Eq (add x0 x1) zero) (And (Eq x0 zero) (Eq x1 zero))
  [0.89] Nat.add_eq_zero       … (Eq (add x0 x1) zero) -> And (Eq x0 zero) (Eq x1 zero)
```

Detail moved to [`../notes/307-brief-step0.md`](../notes/307-brief-step0.md).

