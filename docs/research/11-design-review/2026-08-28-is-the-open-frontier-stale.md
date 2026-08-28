# Is the open frontier stale? Measured: essentially no

Date: 2026-08-28. Prompted by a lane discovering that
`F:ml430-nat-coprime-of-lt-prime-1978a919` was **already proved** —
`declare_coprime_of_lt_prime` had been admitted in `de2e39eee` by a direct
route — while the ledger still carried it as `open`. It flipped the status
and needed no new Rust.

One such case raises a real question. This repository has measured, twenty-plus
times, that **more lane-hours go to re-deriving what exists than to proof
difficulty**. If `open` facts are routinely already proved, the frontier
dispatches lanes at finished work and the retrieval problem has simply moved
up a layer.

## Method

Every `open` fact matching `F:ml430-(nat|int)-<name>-<hash>` — **125** of them —
mapped to a candidate declaration `Nat.<name>` / `Int.<name>` (hyphens to
underscores), then matched against a **freshly built** `--release`
`prelude_theorem_inventory --include-constructed` (6,477 rows, 514 distinct
`Nat.`/`Int.` names). Positive control: `Nat.add_comm`, 7 rows.

`--release` is mandatory — in debug this tool SIGABRTs on a stack overflow that
looks exactly like an absent subject.

## Result: 2 name hits, and BOTH are false positives

| open fact | kernel declaration of that name | verdict |
| --- | --- | --- |
| `F:ml430-nat-coprime-of-dvd-6f652673` — `(∀ k prime, k ∣ m → k ∣ n → k ∣ 1) → Coprime m n` | `Nat.coprime_of_dvd`, the **4-argument divisor-descent** form `dvd a₁ a₂ → dvd b₁ b₂ → Coprime a₂ b₂ → Coprime a₁ b₁` | different statement; that form is the *separately proved* `F:…-of-dvd-18fcd09f` |
| `F:ml430-int-gcd-eq-gcd-ab-63005aef` — `↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y` | `Int.gcd_eq_gcd_ab`, **existential** Bézout `∃ u v, g = m·u + n·v` | different statement — see below |

So **zero of 125** open facts are already proved under exact-name matching. The
`coprime_of_lt_prime` case was a one-off, not a symptom.

## The one substantive finding: existential vs named-witness Bézout

`Int.gcd_eq_gcd_ab` is a genuine near-miss rather than a naming accident. The
kernel proves the **existential** form; Mathlib's statement names *computable*
witnesses `gcdA`/`gcdB` and asserts the identity at them. Ours is strictly
weaker in the sense that matters for a program: it does not hand back the
coefficients.

**I sized this wrong, and a lane corrected me.** I wrote "small, but real work"
and suggested the witnesses might be *extracted* from the existing proof. They
cannot be. Read line-by-line, `declare_gcd_eq_gcd_ab`'s magnitude coefficients
come from `Nat.gcd_bezout`, a `Theorem` whose existential witnesses live inside
a `Prop` and are therefore unprojectable without choice; and the sign flip
(`match_sign`/`sign_cases`) is a `Prop`-typed `Or`-elimination, not a
computable branch. Closing the fact needs a **fresh computable
extended-Euclidean `Definition`** built with `WellFounded.fix` that returns
actual data, plus a from-scratch induction re-deriving Bezout for it — a
multi-hundred-line construction, not an extraction.

That is worth more than a sizing correction. **The distance between our
existential form and Mathlib's is exactly the distance between a `Prop` and a
program**, and no rearrangement of an existing proof closes it: a witness
buried in a `Prop` is gone. Any fact whose Mathlib statement names a
*computable* function has this shape and should be budgeted as new
construction, never as a status flip.

This is the same shape ADR-0603 already names: a classical statement and our
constructive substitute are not the same row, and conflating them is how a
family gets recorded as covered when it is not.

## What this method CANNOT see, stated so the number is not overread

- **Spelling.** Kernel names are camelCase, Rust and docs are snake_case; across
  447 `CReal` names, 315 carry an underscore, 225 an internal capital, 117 both.
  A declaration named `Nat.coprimeOfLtPrime` would not match `coprime_of_lt_prime`
  here. The 125 checked are `ml430` imports, whose names follow Mathlib's
  snake_case closely, so exposure is low — but it is not zero.
- **Inline steps.** A proof built inside a larger declaration and never named has
  nothing to index; no name-based method reaches it. This is documented as
  hiding place 2 and it has bitten repeatedly.
- **Statement equality.** Matching a *name* says nothing about the statement, as
  both hits above demonstrate. A name-match is a prompt to read the type, never
  a conclusion.

So read this as: **the frontier is not systematically stale**, with a lower
bound on already-proved rows of zero-by-name. It is not a proof that every open
row is genuinely open.

## Cheap recurring check

Re-run when the ledger or the prelude moves substantially. The whole check is
one fresh inventory plus a set intersection, and it took minutes. The failure it
guards against — dispatching lanes at finished work — costs a lane-hour each
time, and this session paid that twice from stale coordinator notes.
