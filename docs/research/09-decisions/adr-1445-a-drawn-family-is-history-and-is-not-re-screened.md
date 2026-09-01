# ADR-1445: A drawn family is history and is not re-screened

Status: accepted
Date: 2026-09-01
Index-summary: `gen-autogenesis-nursery-refill.py --check` re-derived already-drawn families against TODAY's screens, so the divergence-registry sweep took three drawn families under the ten-candidate floor and turned the gate red with no legal remedy; membership of a drawn family is now frozen exactly as its partition already was, the screen drift is published instead of thrown away, and only fresh families face current screens.
Index-status: accepted

## Context

`scripts/gen-autogenesis-nursery-refill.py --check` went **red on `main`**, and
the bisect is unambiguous:

```
a3da5621c~1   EXIT 0   AUTOGENESIS_NURSERY_REFILL_OK|entries=460|...
a3da5621c     EXIT 1   family 'natural-find-greatest' yields 0 screened
                       candidates, fewer than the 10 the refill takes
```

`a3da5621c` is the divergence-registry sweep (ADR-1415), which registered five
constructions — `Squarefree`, `Nat.nth`, `Nat.findGreatest`, `Nat.floorRoot`,
`Nat.ceilRoot`. Each was verified against Mathlib's source at the pinned commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, and **each is correct**; nothing
below asks for any of them to be withdrawn.

The generator's `--check` re-derives the whole draw from today's inputs and
compares byte-for-byte against `artifacts/autogenesis/nursery-v2-extension.json`.
`select()` therefore re-screens **every** family, including the 46 already drawn,
and a family whose pool has since fallen below `PER_FAMILY` raises.

### What was measured

Re-running the screens against the 460 committed entries
(`blockers_for(entry.statement, registry)` over the current registry):

| family | drawn rows now screened out | partition | pool today |
| --- | --- | --- | --- |
| `natural-find-greatest` | 10 of 10 | held-out | **0** |
| `natural-integer-root` | 10 of 10 | held-out | **0** |
| `natural-nth-selector` | 10 of 10 | held-out | **0** |
| `natural-factorial-choose-and-squarefree` | 1 of 10 (`Nat.Squarefree.ext_iff`) | train | 44 |

**31 rows across four families, not three.** The fourth matters: its pool is
still 44, so the ten-candidate floor does not fire for it at all — but dropping
`Nat.Squarefree.ext_iff` from the pool shifts the tenth selected row, so
`--check` would still have reported the manifest stale after the floor was
satisfied. A fix aimed only at the floor is incomplete.

Partition split of the 31: **30 held-out, 1 train.** All 31 are
`epistemic_status: open`. Zero of the 460 drawn rows has a pinned statement that
no longer matches the inventory (`source_statement_sha256` re-derived: 460/460
agree). The registry's rejection count over the family modules moved **42 → 97**.

### Are the 31 still-valid mirrors, or genuinely unclosable?

**Genuinely unclosable as mirrors, in all four families, and for the same
reason.** Every one of the five registry entries is `class: codomain` or
`class: definitional` — that is, our construction is a *different function or a
different type* from Mathlib's, so the pinned statement is a different
proposition and closing it here would manufacture a flip. This is the mirror-flip
criterion applied exactly as written:

* `Squarefree` — Mathlib's is `Prop`-valued at the bare root namespace; ours is
  an executable `Nat → Bool` decision procedure. A codomain divergence.
* `Nat.nth` — Mathlib's is noncomputable, splits on `Set.Finite` through
  `Classical.propDecidable`; ours is a fuel-bounded search of arity 3 over a
  `Bool` predicate.
* `Nat.findGreatest` — same recursion, but Mathlib elaborates `DecidablePred` as
  an instance implicit and this kernel has no instance implicits, so the *type*
  differs.
* `Nat.floorRoot` / `Nat.ceilRoot` — Mathlib's body is a product over
  `a.factorization : Finsupp`, which this kernel cannot express; ours is a
  bounded search, extensionally equal and definitionally not.

All five were re-read against the Mathlib checkout at
`/data0/axeyum/lean-import-toolchain/mathlib4`, confirmed at
`git rev-parse HEAD` = `c5ea00351c28e24afc9f0f84379aa41082b1188f`, rather than
taken from the registry's own `why` text:

```
Mathlib/Algebra/Squarefree/Basic.lean:41   def Squarefree [Monoid R] (r : R) : Prop
Mathlib/Data/Nat/Factorization/Root.lean:54   def floorRoot (n a : ℕ) : ℕ :=
  if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k ↦ p ^ (k / n)
Mathlib/Data/Nat/Factorization/Root.lean:113  def ceilRoot (n a : ℕ) : ℕ :=
  if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k ↦ p ^ ((k + n - 1) / n)
Mathlib/Data/Nat/Nth.lean:60   noncomputable def nth (p : ℕ → Prop) (n : ℕ) : ℕ := by
  classical exact
    if h : Set.Finite (setOf p) then h.toFinset.sort.getD n 0
    else @Nat.Subtype.orderIsoOfNat (setOf p) (Set.Infinite.to_subtype h) n
Mathlib/Data/Nat/Find.lean:168   def findGreatest (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ
```

One correction, in the registry rather than in the substance: the
`Nat.findGreatest` entry records `mathlib_source.path` as
`Mathlib/Order/Basic.lean`, "re-exported through Mathlib.Data.Nat.Find". At this
commit the `def` is **in** `Mathlib/Data/Nat/Find.lean:168`, and
`Mathlib/Order/Basic.lean` does not define it. The divergence the entry claims —
instance-implicit `DecidablePred` against this kernel's explicit argument — is
exactly right; only the file it points at is wrong. Not repaired here, because
this lane must not touch the registry.

`natural-find-greatest` at pool 0 is **not** a different situation from the
others at pool 0; the three zero-pool families each rest on a single registry
entry that covers their whole module. The one-row family differs only in degree.

So the honest reading is that these 31 rows will never be closed on this route,
and no amount of work changes that. The population genuinely thinned.

### Why "the floor is a live invariant" has no legal remedy

That is the reading the failure invites, and it does not survive contact with
what would have to be done to satisfy it. The only ways to make the floor green
again are:

1. **Un-register a divergence.** Forbidden, and rightly: each entry is true, and
   deleting a true entry to satisfy a floor is manufacturing a green gate.
2. **Delete or re-draw the 31 rows.** 30 of them are **held-out**. Deleting
   held-out rows is precisely the silent alteration of a blind evaluation
   population that ADR-0542 exists to forbid, and re-drawing replacements from
   today's pool would make held-out membership a function of when the generator
   was last run — which is not preregistration at all.

A gate whose only remedies are forbidden actions is not an invariant; it is a
trap that will fire again on the next honest divergence. And it *will* fire
again: the registry only grows.

### The generator already holds the other reading everywhere else

This is the decisive measurement, and it is in the code rather than in an
argument. `guard()` scopes R4, R5, R9, R11 and R12 to
`new_entries = [e for e in entries if e["family"] not in frozen]`, and R9's own
comment states the principle outright:

> Scoped to what this draw adds — an earlier draw's rows are frozen, and
> repairing one is an amendment, not a regeneration.

`frozen_partitions()` (ADR-0615) already freezes a drawn family's **partition**
against re-derivation, for exactly the reason at issue here: re-deriving moved
seven of eight families and put a train family with 8 of 10 mirrors proved into
held-out. ADR-0542 then supplies the amendment ledger as the only legal way to
move one.

So every layer of this generator except `select()` treats a completed draw as
history. `select()` is the inconsistency, and it went unnoticed only because
until `a3da5621c` no screen had ever changed after a draw.

### Does ADR-0542's amendment ledger already cover this?

**No.** `amendments()` is keyed by family and carries `from`/`to` **partitions**;
it repairs a family whose blind value was *spent*. Nothing here was spent —
`natural-find-greatest`'s rows are as blind as they ever were, they are simply
unclosable in any partition. Moving those families out of held-out via the ledger
would record a breach that did not happen and would waste the only irreversible
repair the population has.

ADR-0542's *principle* — repairs are amendment ledgers, never deletions — is what
decides this ADR. Its *mechanism* is the wrong instrument for it.

## Decision

**A family an earlier draw preregistered is frozen in membership as well as in
partition. Only fresh families face today's screens and the ten-candidate
floor.**

1. `select()` reads a `drawn_freeze()` — the manifest's own entries, trusted only
   against `extension_sha256`, the same route `frozen_partitions()` already
   uses — and re-emits a drawn family's rows in recorded order.
2. **Membership is frozen; content is not.** Each frozen row is rebuilt from the
   pinned statement inventory by the same `_entry_for()` the fresh path uses, and
   the rebuild must equal the recorded row on every field derived from the pinned
   source (`source_name`, `module`, `statement`, `source_statement_sha256`,
   `constants`, `candidate_id`, `fact_id`, `statement_shape`, `proof_shape`,
   `fragment`, `source_group`, `provenance_class`, `mutation_of`,
   `answer_access`). A drawn row that has vanished from the inventory, changed
   statement, or moved module is a **refusal**, not a silent pass. The two fields
   derived from live in-repo rules — `partition` and `route_hypotheses` — are
   re-stamped, which is what keeps the ADR-0542 amendment path working.
3. The thinning is **published, not discarded**. The manifest gains a top-level
   `historical_draw_screen_drift` block naming every drawn row today's screens
   would now reject, with its family, partition and blocking constant, plus
   counts. It sits outside `entries`, so no drawn row's bytes change.
4. The ten-candidate floor and every screen still apply in full to a fresh
   family. Nothing about drawing new population is relaxed.

## Consequences

* `--check` stops being a hostage to the divergence registry. The next honest
  divergence changes the published drift block and nothing else.
* The gate does not become unfailable. It now fails on the things that should
  fail it — a drawn row whose pinned source changed or vanished, a fresh family
  under the floor, a manifest that does not match its own digest, a hand-edited
  partition — and stops failing on the one thing that has no legal remedy.
* The 30 unclosable held-out rows stay in the blind population, correctly
  classified. `check-dispatchable-frontier.py`'s `classify()` already consults
  the registry, so nothing will be dispatched at an unclosable mirror; the drift
  block is what makes the dead weight countable by a referee instead of invisible.
* A future draw that wants to *replace* dead held-out rows must do it as an
  explicit, recorded amendment. This ADR does not authorize that, and deliberately
  does not build the mechanism for it: the right time to design a
  retire-and-replace ledger is when someone has a reason to run one, not while
  fixing a red gate.

## Alternatives rejected

* **Skip the floor for drawn families only.** Fixes three families and leaves the
  fourth: `natural-factorial-choose-and-squarefree` never trips the floor and
  still re-derives a different tenth row. Measured, not assumed.
* **Exempt these five constructions from the screen for drawn rows.** A
  per-entry allowlist that grows with the registry, and it hides the thinning
  rather than reporting it.
* **Withdraw a registry entry.** Refused on the brief's hard constraint and on
  the merits: all five definitions were read from the Mathlib checkout at the
  pinned commit while writing this ADR (output quoted above) and all five
  divergences are correct.
