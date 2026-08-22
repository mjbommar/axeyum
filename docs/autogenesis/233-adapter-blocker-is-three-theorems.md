# 83% of the population is blocked by three theorems, and we already prove one of them

> ## ⚠ THIS DOCUMENT'S CENTRAL CLAIM IS WRONG. Corrected 2026-08-22, same day.
>
> The counts below are accurate. **What they mean is not what this document says.**
>
> `StatementImportError::TrustedDeclaration { name, kind }` carries a SINGLE name:
> it is raised on the FIRST trusted declaration the adapter encounters, not on the
> closure. So `detail` reports which blocker came first, not the blocker set. This
> document read a first-hit distribution as a complete one.
>
> All three theorems have since been made self-derivable and are no longer trusted
> ([`235`](235-congrarg-congr-mt-substitution-result.md)). Re-running the census
> with that active: `congrArg`/`congr`/`mt` block **zero** of 114 rows, and the
> outcome distribution is **unchanged at 114 / 15 / 7 / 2**. Five new first-blockers
> simply took their place:
>
> ```
> eq_of_heq 41 · eq_self 20 · Quot 19 · if_neg 18 · ite_self 15 · propext 1
> ```
>
> So the corrected finding is the opposite of the headline: **the blocker closure is
> deep, not shallow.** Each row carries roughly thirty trusted Lean-core `Nat`
> theorems, and removing a layer exposes the next. "113 of 114 unblocked by three
> theorems" and the "5.7× change in what is attempted" were both wrong.
>
> Kept rather than deleted, because the reasoning error is the useful part: the
> numbers were verified and their MEANING was not. Asking what a field contains is
> a different question from asking what it counts.

Date: 2026-08-22

Source: the frozen 2026-08-19 census, re-read from `observation.json`.
Companion: [`230`](230-producer-decline-shape-census.md) did this for the 15
`producer-decline` rows; this does it for the 114 that never reach a producer.

## The measurement

`adapter-rejection` is 114 of 138 rows. Every one has the same `reason`, and
between them they name **four declarations**:

| Blocking declaration | Kind | Rows |
|---|---|---:|
| `congrArg` | Theorem | **56** |
| `congr` | Theorem | **38** |
| `mt` | Theorem | **19** |
| `propext` | **Axiom** | **1** |

`reason` and `detail` are non-empty on all 114 rows, and none is held-out. The
four values account for 114 of 114 — there is no tail.

**This is not 114 problems. It is three theorems and one axiom.**

## Why the adapter is right to refuse

The policy is not a bug and must not be relaxed. `type_slice.rs` refuses when the
closure of a retained declaration "would expose a trusted declaration to the
producer" — that is, would hand an untrusted proposer a *proof-bearing* Mathlib
declaration. A producer that can cite Mathlib's `congrArg` can discharge goals by
appealing to Mathlib's proof, which is precisely the trust this programme exists
not to take. Loosening the check would convert the whole nursery into an
expensive way of believing Mathlib.

## Why that does not make these 113 rows unreachable

The three blockers are all **theorems**, and all three are derivable in our own
kernel from primitives we already have:

| | derivation |
|---|---|
| `congrArg : a = b → f a = f b` | from `Eq.rec` |
| `congr : f = g → a = b → f a = g b` | from `Eq.rec` |
| `mt : (a → b) → ¬b → ¬a` | propositional; no axiom |

And the first of those is **not hypothetical here**. The bounded-induction
producer landed today
([`232`](232-first-general-producer-result.md)) already constructs the congruence
step directly from the kernel's generated `Eq.rec`, precisely because an isolated
statement-import kernel keeps only Definitions and Inductives and no `congrArg`
exists to borrow. The capability that removes the single largest blocker is
already written; it is on the wrong side of the adapter.

So the fix preserves the boundary rather than weakening it: **for a small, fixed,
reviewed set of declarations that we prove ourselves, substitute our derivation
for the imported one.** The producer still never sees a Mathlib proof. It sees
ours.

`propext` is genuinely different — a real axiom, not derivable — and stays
refused. One row.

## What it would change

| | rows | share |
|---|---:|---:|
| reach a producer today | 24 | 17% |
| reach a producer if the three theorems are reconstructed | 137 | **99%** |
| irreducibly blocked by an axiom | 1 | 1% |

**Reachable is not provable, and the distinction matters.** Getting past the
adapter only means a producer gets a turn; most of those 113 will still decline,
and [`230`](230-producer-decline-shape-census.md) already shows the shapes waiting
on the other side — 8 inequalities, 4 biconditionals, 2 divisibilities. The claim
here is narrower and stronger than a yield forecast: **the binding constraint on
this population is three named theorems, and it is the only constraint whose
removal is a 5.7× change in what is even attempted.**

## Why nobody saw it

The census recorded these counts on 2026-08-19 and nothing read them for three
days. `adapter-rejection: 114` was quoted repeatedly — in the plan, in the
retrospective, in this lane's own summaries — as though 114 were the interesting
number. The interesting number was four, and it was one `Counter()` away the
whole time.

Produced by a Haiku subagent under a mechanical brief with two mandatory positive
controls, then independently recounted here before landing.
