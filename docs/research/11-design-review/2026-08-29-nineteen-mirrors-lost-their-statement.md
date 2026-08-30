# Nineteen mirrors have lost the Mathlib proposition they mirror (2026-08-29)

**Measured across the whole ledger, after correcting my own earlier conclusion.**

An `ml430` mirror fact is created with:

| field | content |
| --- | --- |
| `statement` | a prose **reference**: "The proposition declared as `Nat.coprime_add_self_left` in the pinned Mathlib v4.30 source." |
| `formal.statement` | **Mathlib's actual proposition**, e.g. `∀ {m n : ℕ}, (m + n).Coprime n ↔ m.Coprime n` |

Verified at the creating commit for facts from both the original 214 and the
later draws — the convention is the same in both cohorts.

**For 19 facts, `formal.statement` has been overwritten with our kernel's own
rendering** — `theorem Nat.coprime_add_self_left : ((x0 : AxNat) -> ...)`. Since
the top-level field is only a prose reference by name, **those 19 facts no
longer carry the proposition they claim to mirror anywhere.**

## Why this matters

The mirror programme's whole claim is "we proved the thing Mathlib states". For
these 19, that claim cannot be checked from the fact: you must go to git history
or back to the pinned source to learn what was asserted. A fact that records
only its own theorem is not a mirror; it is a restatement.

Nothing is *false* — the kernel theorems are real and axiom-free, and each fact
still names the Mathlib lemma in prose. But the ledger stopped being
self-contained for these rows, and self-containment is what makes a referee able
to check the claim in one command.

## Correction to my own earlier reading

Two hours ago I looked at **one** such fact (`F:ml430-nat-totient-eq-zero`),
found Mathlib's statement intact at the top level, and reported the problem as
"less severe than I said — the convention diverged, the meaning was not lost."

That fact came from a **draw**, where the generator writes Mathlib's statement
at top level. The original-214 cohort writes prose there. I generalised from one
fact of the wrong cohort — the third time today I have generalised from a single
instance, and the second time the generalisation ran in the reassuring
direction.

## Scope, and why it is recurring

The count grew as I looked wider: a lane reported **1**, the next reported **3**
(its own scope), the ledger-wide measurement is **19**. It recurs because
flipping a fact to `proved` is the moment a lane has the kernel's rendered type
in hand, and writing it into `formal.statement` is the natural thing to do.

## What a fix needs

1. **Repair**: restore each `formal.statement` from the creating commit (or from
   the nursery manifest, which holds the pinned `type`). Surgical text
   substitution only — a lane found a JSON re-dump reformats unrelated compact
   arrays.
2. **A guard**, because prose has not stopped it: an `ml430` fact's
   `formal.statement` must not be a kernel rendering. The signature is cheap —
   it starts `theorem ` or mentions `AxNat`/`AxInt`, neither of which can appear
   in a Mathlib surface statement.
3. **Somewhere for the kernel type to live**, since lanes clearly want to record
   it. `kernel_theorem` already names *which* theorem discharges the mirror; a
   sibling field for its rendered type would satisfy the impulse without
   overwriting the claim.
