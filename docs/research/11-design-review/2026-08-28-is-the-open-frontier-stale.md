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

## Addendum: 30 of the 128 open facts are blocked on THREE missing definitions

Measured 2026-08-28 while choosing the next lanes, with `choose` (19
`declare_` fns) and `coprime` (15) as positive controls so a zero means
something:

| family | open facts | `declare_` fns | prelude fields | carrier |
| --- | ---: | ---: | ---: | --- |
| `nat.log` | 12 | 0 | 0 | **absent** |
| `nat.sqrt` | 10 | 1 | 1 | **absent** — see below |
| `nat.clog` | 8 | 0 | 0 | **absent** |
| `nat.factorial` | 6 | 0 | 5 | present |
| `nat.prime` | 7 | — | — | present (`primes.rs`) |

**The `nat.sqrt` row is a trap I nearly walked into.** The single `declare_`
hit is `declare_no_rational_sqrt_two` — the *irrationality of √2*, a statement
about squares — and the single field is `no_rational_sqrt_two`. There is no
`Nat.sqrt` function. That field's own doc comment says so outright: "no
`sqrt`, no rational embedding". A substring match on a family name found a
theorem *about* the concept and read as the concept existing.

So **30 of 128 open facts — 23% of the whole open frontier — sit behind three
absent definitions**, not behind proof difficulty. None of the twelve
`nat.log` facts can be *stated* in this kernel today, let alone proved.

Two consequences:

- **This is the highest-leverage work on the frontier**, and it is
  infrastructure rather than theorem-proving. Each definition is a
  non-structural (division-decreasing) recursion, which is a different
  technique from everything closed today.
- **The frontier's "open" count conflates two very different states**: a fact
  whose statement is expressible and unproved, and a fact whose statement
  cannot be written at all. `fact-frontier.py` reports both as `proof route
  only — needs a kernel proof`, which is true of the first and misleading
  about the second. Worth splitting if it is cheap.

Method note, again: the check that works is `declare_` function count **plus a
positive control from a family known to exist**. Grepping a family name across
a module directory returned 40 files for `log` — almost all of them the word
"log" in prose.

## Correction: 35 of those 30-odd "highest-leverage" facts ARE the holdout

The addendum above called the three absent definitions "the highest-leverage
work on the frontier" and three lanes were dispatched at them. That framing was
wrong in a way worth recording, because the error was invisible from where it
was made.

Measured afterwards against `artifacts/autogenesis/nursery-v1.json`:

| family | rows | partition |
| --- | ---: | --- |
| `natural-logarithm` | 21 | **held-out, in full** |
| `natural-square-root` | 16 | **held-out, in full** |

Those two families **are** the held-out partition — 37 rows total, 35 of them
`nat.log` / `nat.sqrt` / `nat.clog` mirrors. Held-out rows are blind evaluation
population, keyed `<family>:<statement-shape>` precisely because a proof route
for one member is evidence about its siblings, so closing one spends the
family. A capsule registered against a single held-out row once cost 19 of 76
propositions — 25% of the partition — for one theorem.

**Nothing was spent.** `check-autogenesis-holdout-isolation.py` reads
`held_out=37 settled=0 references=0 PASS`. Each lane independently declined to
flip the `ml430` mirrors, because our definition is not Mathlib's. The briefs
did forbid it — for that reason, not because the rows were evaluation
population, which the coordinator did not know. The outcome was right and the
reasoning that produced it was not, so it would not have held reliably.

**The queue was silent.** `fact-frontier.py` already printed `NAMED BY <gate
script>` when a fact was load-bearing for a control, and a grep for
`held.out|nursery|partition` returned **0**. The single annotation that would
have caught this was the one absent. It now prints a `HELD-OUT` marker on all
37, with four controls — including the two that matter, that a *non*-held-out
fact is not warned about, and that the population is non-empty — and the guard
is mutation-verified to kill exactly one named test.

**What stays true from the addendum**: the three definitions genuinely did not
exist, building them was legitimate, and all three landed axiom-free with their
own new `F:nat-{log,sqrt,clog}-*` facts. What changes is the conclusion drawn
from the count. **A large block of open facts in one family is as likely to be
a preregistered evaluation set as a neglected opportunity**, and the frontier's
own row count cannot tell them apart. Check the partition before sizing the
prize.

## A boundary I over-generalized: `Quot.sound` blocks a ROUTE, not provability

The producer lane measured, correctly, that **`Nat.gcd.eq_def` carries
`Quot.sound`** (as do `Nat.gcd_zero_left`, `Nat.gcd_succ`), because `Nat.gcd`
is defined by well-founded recursion. It concluded that
`Nat.ModEq.gcd_eq` **"cannot be produced this way"**, and named it among the
targets its transport route could not reach.

I turned that into a general constraint and put it in three subsequent briefs
as *"nothing axiom-free can unfold `Nat.gcd`'s well-founded recursion, so any
family whose statements mention `Nat.gcd` is out of reach."*

**The first half is true and the conclusion is too broad.** A lane proved
`Nat.ModEq.gcd_eq` outright, axiom-free — `Nat.mod_eq_gcd_eq`, footprint 0
(verified here against `Nat.add_comm` as a control). It never unfolds the
recursion: it eliminates the balanced-witness `modEq` definition twice, derives
`gcd a m ∣ gcd b m` and its mirror through `dvd_add` / `dvd_add_iff_right` /
`dvd_mul_right_of_dvd`, and closes with `dvd_antisymm`. Accepted first attempt.

The precise statement, which is what the briefs should have said:

> **`Quot.sound` blocks unfolding `Nat.gcd`'s recursion, so it blocks the
> IMPORT/TRANSPORT route, which needs an axiom-free candidate that steps the
> definition. It does not block proving facts ABOUT `gcd` by other means** —
> the divisibility characterisation (`gcd_dvd_left`/`_right`, `dvd_gcd`,
> `dvd_antisymm`, `eq_one_of_dvd_one`) reaches many of them and needs no
> unfolding at all.

Every `gcd` fact closed in this repository has gone the second way, including
nine in one lane. So the boundary is real, narrow, and about a *mechanism*, not
about a subject.

**The general shape, since I have now made this error twice**: a lane reports
what blocked *its* route. Promoting that to "this cannot be done" is the same
over-generalization as `[[dont-generalize-a-lanes-local-finding]]`, and it is
easy precisely because the measurement is sound. Ask which route the finding
constrains before writing it into a brief.
