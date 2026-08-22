# 83% of the population is blocked by three theorems, and we already prove one of them

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
