# Lane: lean-attestation-s5 -- s5 can attest, and one preregistered row is not a proposition

<!-- plan-section: lane-status -->

**Lane block (`DONE -- 159 of 160 attested, 1 rejected and recorded`,
lean-attestation-s5, 2026-08-29).**

## Headline

**s5 can do it, and it is cheap: 3.6 s for all 160 rows.** Three lanes today
worked around a missing Mathlib by inventing a weaker, labelled *quotation*
grade. That grade was honest and it was also unnecessary on this fleet.

| | before | after |
| --- | --- | --- |
| extension rows carrying a real Lean attestation | 0 | **159** of 160 |
| rows Lean REJECTS | unknown | **1**, recorded |
| grade | flat literal `"quotation"` | derived per row from the run |
| facts asserting a now-false quotation claim | 35 | **0** |
| new artifacts under `artifacts/autogenesis/` | -- | **0** (folded into the manifest) |

The row count is **160**, not the 120 the brief said: a third draw landed 40
more rows the same day.

## 1. Can s5 do it? Yes, end to end

Verified by elaborating, not by listing a build directory.

```
host            s5   (ssh BatchMode, 16 c, 27 G)
mathlib         ~/lean-import-scale/mathlib4   c5ea00351c28f...  .lake/build 6.2 GB
lean            4.30.0  d024af099ca4bf2c86f649261ebf59565dc8c622
import Mathlib + 160 proof-free axioms  ->  3.6 s
negative control                        ->  REJECTED (good)
```

The checkout's 64 `git status` entries are all **untracked probe `.lean` files**
from earlier lanes. No tracked file is modified and the commit is the one we
pin, so the checkout is trustworthy.

## 2. The finding: `Nat.le_induction` is not a well-formed proposition

**159 of 160 elaborate. One does not.**

```
F:ml430-nat-le-induction-2f088ac3   Nat.le_induction
family natural-induction-and-divisibility   partition HELD-OUT

  ∀ {m : ℕ} {P : (n : ℕ) → m ≤ n → Prop},
    P m ⋯ → (∀ (n : ℕ) (hmn : m ≤ n), P n hmn → P (n + 1) ⋯)
          → ∀ (n : ℕ) (hmn : m ≤ n), P n hmn

  error: don't know how to synthesize placeholder   ⊢ m ≤ m
  error: don't know how to synthesize placeholder   ⊢ m ≤ n + 1
```

`⋯` is Lean's pretty-printer glyph for an **elided proof term** (here `m.le_refl`
and `le_succ_of_le hn`). Re-parsed it is a hole Lean cannot fill. So we
preregistered a string that is not a proposition, and it **can never be closed
as stated**.

This is precisely the risk the quotation grade named and structurally could not
detect — *"a pretty-printed type is not guaranteed to re-parse"* — and the
per-row `source_statement_sha256` cannot see it either, because the checksum
faithfully binds a **lossy** string. Only elaboration distinguishes them.

**Confirmed in both directions**, because a parse error can desync Lean's parser
and swallow following lines:

Detail moved to [`../notes/305-lean-attestation-s5.md`](../notes/305-lean-attestation-s5.md).

