# ADR-1664: an originated theorem may rest on an import, on a route of its own

Status: proposed
Date: 2026-09-05
Lane: `lean-import-composition`
Roadmap: `docs/math-department/14-lean-lang.md` Next Ten item 8 (reviewers 03,
06, 08)

Index-summary: two footprint regimes coexisted — originated theorems with
`proof_route: kernel-lean` and an empty `Kernel::axiom_footprint`, imports with
`proof_route: imported-kernel-lean` on which `[]` is rejected — and nothing said
whether they may touch, so measure theory, probability and topology could enter
only as islands. Decided by building the composed theorem rather than weighing
the options (`crates/axeyum-lean-import/tests/imported_composition_footprint.rs`,
4 tests, every number on an `AXEYUM-COMPOSE|` marker line). **Propagation is
transitive and per PROOF TERM, not per environment**: two originated theorems of
the same type in the same kernel, one proved `fun p h => Classical.em p` and one
`fun p h => h`, measure the import's whole six-name closure and `EMPTY`
respectively. Composition costs 0.19 ms at `add_declaration` against 0.09 ms for
the sibling that avoids the import — the import itself costs 122 ms (106
declarations) to 17.5 s (Mathlib's 3,585). **Decision: option (2)** — allow it,
on a distinct `kernel-lean-over-import` route that never counts toward the
axiom-free headline. Option (3) ("allow when the composed footprint is `[]`") is
rejected on the measurement that `Kernel::axiom_footprint` **structurally cannot
see** the three assumptions an import adds, so its `[]` on an Init-only
composition would promote into the axiom-free headline a theorem resting on
things the metric cannot express. Two findings reported in passing: the
department file's `[propext, Classical.choice, Quot.sound]` is wrong — the
kernel reports **eight** names for IVT — and `count-landmark-facts.py` never
read `proof_route`, so all **7 of 7** imported facts, IVT and EVT included, were
counted as landmarks.
Index-status: proposed

## Context

`docs/math-department/14-lean-lang.md` lists this as Next Ten item 8, and three
chairs are blocked behind it. Reviewer 03 (classical analysis):

> 7 imports exist and each carries Mathlib's three axioms; **no decision says
> whether an originated theorem may *depend* on an imported one**, so imports
> cannot compose with anything we prove.

Reviewer 08 (probability) is "same as 03". Reviewer 06 (topology) needs the same
answer to state an honest typed decline. The file's own blocker section names it
as one of its two design blockers, "Trust composition".

Two regimes exist and are each internally settled:

* **Originated.** `proof_route: kernel-lean`, `axiom_footprint: []` on all of
  them, read from `Kernel::axiom_footprint` and never from source text.
  [ADR-1601](adr-1601-classical-logic-enters-as-a-hypothesis-not-as-an-axiom.md)
  makes classical principles *hypotheses discharged at use*, never axioms, and
  measured that policy's carrying cost at 11 binders and zero new obligations
  across ten theorems.
* **Imported.** `proof_route: imported-kernel-lean`
  ([ADR-1090](adr-1090-ivt-evt-row-4-labeled-import-lands-mathlib-topology-admits-clean.md)),
  7 facts, `scripts/validate-facts.py` refuses `[]` on the route by
  construction.
  [ADR-0601](adr-0601-three-producers-one-trust-anchor.md) makes imports labeled
  scaffolding, never headline;
  [ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md)
  row 4 is where a classical theorem's import lands in a graded family.

What no document decides is the *edge between them*. Until it is decided, an
import is an island: nothing we prove may cite it, so bringing measure theory in
buys a row in the ledger and nothing else.

The department's method (`docs/math-department/00-roadmap.md`) is "do not weigh
the arguments, build the theorem the decision is about and report what it cost",
and that is how this ADR was written.
[ADR-0509](adr-0509-the-trusted-surface-is-measured-as-reached-not-only-declared.md)
sets the standard the answer has to meet: a trusted surface is what a walk
REACHES, not what a document declares. It refused to move a number by deleting a
package and published a second, *reached* number instead. The rule below is the
same discipline applied one level up — a composed fact's footprint is derived
from `Kernel::axiom_footprint`, never transcribed — and it is also why the three
import-route assumptions have to be written down explicitly: no walk over the
environment reaches them, so a *reached* number alone would understate the
trust base rather than overstate it.

## Evidence

`crates/axeyum-lean-import/tests/imported_composition_footprint.rs` — four
tests, one `AXEYUM-COMPOSE|` marker line each, run 2026-09-05 at `766cfeb0f`.
Reproduce with

```sh
cargo test -p axeyum-lean-import --test imported_composition_footprint \
  -- --nocapture --test-threads=1            # 3 passed, 1 ignored
cargo test -p axeyum-lean-import --test imported_composition_footprint \
  -- --nocapture --ignored                   # the Mathlib endpoint, ~18 s
```

### 1. An Init-only import composes to an empty footprint

`bool-and-comm.ndjson`, Lean `Init` only, 48 declarations admitted. The import
itself measures `EMPTY`. An originated theorem

```text
(x : Bool) -> Eq.{1} Bool (Bool.and x Bool.true) (Bool.and Bool.true x)
   := fun (x : Bool) => Bool.and_comm x Bool.true
```

also measures `EMPTY`. Import 51.7 ms, `add_declaration` 0.163 ms.

### 2. The discriminating pair — propagation is per proof term

`classical-em.ndjson`, 106 declarations. `Classical.em`'s footprint is

```text
Classical.choice, Quot, Quot.lift, Quot.mk, Quot.sound, propext
```

In **one** kernel holding that import, two originated theorems of the **same
type**

```text
(p : Prop) -> (h : Or p (Not p)) -> Or p (Not p)
```

| proof term | measured footprint | `add_declaration` |
|---|---|---|
| `fun p h => Classical.em p` | the six names above, exactly | 0.194 ms |
| `fun p h => h` | `EMPTY` | 0.091 ms |

Both halves are load-bearing. The first confirms **transitivity** — the composed
theorem inherits the import's *whole* closure, not a summary of it, so a
composed fact's footprint can be derived rather than asserted. The second is the
positive control: if the footprint read the ENVIRONMENT rather than the proof
term, the sibling would report the six names too, and no per-theorem tier would
be possible at all. It does not, so **the tier is decidable per theorem**, and a
lane that loads an import does not thereby contaminate everything it proves that
session.

### 3. The Mathlib endpoint, re-derived and not quoted

`ivt-intermediate-value-icc.ndjson`, 3,585 declarations, 17.5 s. The footprint
of `intermediate_value_Icc` is **eight** names:

```text
Classical.choice, Quot, Quot.lift, Quot.mk, Quot.sound,
String.Internal.append, propext,
wrapped._@.Mathlib.Topology.Defs.Filter.2998874748._hygCtx._hyg.2
```

`docs/math-department/14-lean-lang.md` says imports carry `[propext,
Classical.choice, Quot.sound]`. That is Lean's own `#print axioms` vocabulary,
not ours: this kernel classifies the whole quotient package as `Quotient`
declarations and additionally reports `String.Internal.append` and one opaque
`wrapped._@…` constant. Ours is the more conservative reading. The department
file's row is corrected by this lane; the schema's `proof_route` description
already recorded the three-versus-six discrepancy for `Classical.em` and was
right.

### 4. Cohabitation is blocked, on a name and not on a principle

`build_nat_prelude` into a kernel already holding the 48-declaration Init slice
is **rejected**, at `False`.

The order is forced by the API: `import_ndjson` constructs its own staging
`Kernel`, which is the fail-closed contract — nothing is published unless the
whole stream translates and every declaration passes `Kernel::add_declaration`.
So import-then-prelude is the only reachable order, and it collides. The test
resolves the collision to a name rather than printing `DeclarationExists {
name: NameId(46) }` (a `NameId` names nothing — the same failure mode CLAUDE.md
records for `UnboundFVar`) and enumerates the overlap: **17 names shared**
between the 48-declaration import and the 1,990-declaration prelude — `Bool`,
`Bool.false`, `Bool.rec`, `Bool.true`, `Decidable`, `Decidable.decide`,
`Decidable.isFalse`, `Decidable.isTrue`, `Decidable.rec`, `DecidablePred`, `Eq`,
`Eq.rec`, …

This is a **name-space** obstacle, not a trust one, and it bounds what the
decision can license *today*: a composed theorem can cite an import and other
imported declarations, but it cannot yet cite an import and `Nat.add_comm` in
one proof term. The route decided below is nonetheless the right shape now,
because the shared-vocabulary bridge (`docs/math-department/14-lean-lang.md`
Next Ten item 4, the carrier correspondence ledger) is what removes the
obstacle, and it must not have to invent a trust vocabulary as well.

### 5. What the two ledger counters do with an import today

Measured 2026-09-05: neither `scripts/count-landmark-facts.py` nor
`scripts/check-fact-characterisation.py` reads `proof_route` at all. Both split
the ledger on the `[generated]` title prefix and `epistemic_status`. So **7 of
the 7 `imported-kernel-lean` facts are counted as landmarks today**, Mathlib's
IVT and EVT included — 7 of 1,523, or 0.46 %, but they are exactly the rows
ADR-0601 says are "labeled scaffolding, never headline". The composition tier
would inherit the same hole and grow it.

## Decision

**An originated theorem MAY depend on an imported one. It lands on a distinct
`proof_route: kernel-lean-over-import`, it carries the import's assumptions as
well as its own measured footprint, and it counts toward the axiom-free headline
never and toward a separately reported composed tier always.**

This is option (2) of the three the department file named. In detail:

1. **Route.** `kernel-lean-over-import` joins `ROUTES`. It is NOT in
   `AXIOM_FREE_CAPABLE`, so the existing rule already rejects `[]` on it.
2. **Footprint.** The value is `Kernel::axiom_footprint` of the composed
   theorem — derived, per §2, never asserted — **plus** the three import-route
   assumption names the seven existing imported facts already spell:

   ```text
   lean4export-3.1.0-stream-faithfulness
   axeyum-lean-import-wire-translation
   lean4export-3.1.0-delivered-bytes-are-the-intended-export
   ```

   Every one of them must be present. They are what `Kernel::axiom_footprint`
   structurally cannot see, and §3's Init-only case proves the gap is real: a
   composition over `bool-and-comm` measures `EMPTY` from the kernel and still
   rests on all three.
3. **Provenance.** `provenance.prior_art` is required, as on
   `imported-kernel-lean`: the proof term is partly ours and partly not, and a
   composed theorem that reads as wholly local is the failure the import route
   exists to prevent.
4. **Traceability.** At least one entry of `depends_on` must be a fact on an
   imported route. "Originated over an import" is a claim about a dependency,
   and the ledger must be able to name *which* import, so the tier is walkable
   rather than merely labelled.
5. **Counting.** The axiom-free counter is unchanged: it counts `[]` on
   `kernel-lean` and on nothing else. The validator prints a composed-tier line
   beside the existing imported line. `count-landmark-facts.py`'s landmark rule
   excludes both import-dependent routes — which also repairs §5's existing
   miscount of 7.

### The chair's headline sentence

Before: *"N results this project established, every one of them axiom-free."*

After, unchanged in its first clause and extended by one:

> **N results this project established, every one of them axiom-free; K further
> results this project proved on top of M labeled imports, each carrying the
> imported proof's axioms and the import route's three assumptions; and M
> imports checked here but authored elsewhere, which are not results of ours.**

Three numbers, three trust bases, no total across them. Today N = 2,474 (the
originated `kernel-lean` facts with an empty footprint), K = 0, M = 7.

### What `check-fact-characterisation.py` does with the tier

Nothing, deliberately. That script asks whether a fact CHARACTERISES itself —
`curated` / `generated` / `transcribed` — which is a question about prose, not
about trust. Fusing the two axes would make its ratchet unreadable. A composed
fact is classified by its title exactly like any other. This is stated here so
the silence is a decision rather than an oversight.

## Alternatives

**(1) Forbid dependence; imports stay islands.** Rejected. The measurement gives
no mechanical reason for it: propagation is transitive and exact (§2), so a
composed theorem's trust base is *fully derivable* and nothing is hidden; and it
is cheap (0.19 ms at the gate, against a 122 ms – 17.5 s import). Forbidding
would cost reviewers 03, 06 and 08 their entire subject in exchange for a
property — "no originated theorem touches an import" — that the route label
already expresses without the prohibition. It would also be unenforceable in the
direction that matters: nothing stops a lane from *retyping* an imported proof
by hand, which is strictly worse, because the dependence then goes unrecorded.

**(3) Allow only when the composed footprint is `[]` after import (Init-only),
route (2) otherwise.** Rejected, and the measurement is what rejects it. §1
shows the Init-only case really does measure `EMPTY`; §3 shows why that is the
wrong test. `Kernel::axiom_footprint` walks *declarations* and keeps the ones
admitted on trust. The import's three assumptions are not declarations — they
are claims about how the declarations reached the environment (the exporter
rendered Lean's environment faithfully, our wire translation preserves meaning,
and the delivered bytes are the producer's intended export; format 3.1 has no
footer, so completion is relative to the bytes handed over). No walk over the
environment can see them. So option (3)'s criterion is measuring the wrong
quantity: it would route an Init-only composition to `kernel-lean` with `[]`,
promoting into the axiom-free headline a theorem whose trust base includes three
assumptions the metric cannot express. It also fails on the authorship axis,
which is half of why `imported-kernel-lean` exists at all: an Init-only
composition is no more *ours* than a Mathlib one. Option (3) is option (2) plus
a rule that is wrong exactly where it fires.

## Consequences

**Easier.** Reviewers 03, 06 and 08 can start: a measure-theoretic or
topological statement may now be proved on top of an imported Mathlib lemma and
land as a fact, with its trust base derived and visible. ADR-0603's graded
statement family gains a fifth shape — *originated over a labeled import* —
between row 1 (general constructive form) and row 4 (labeled import), and it is
the row that makes row 4 worth having.

**Harder.** Three things.

* The composed footprint has two provenances in one array — kernel-derived names
  and route-assumption strings. That is already true of the seven imported facts
  and is enforced rather than merely conventional now, but it means a reader
  must know the vocabulary. The schema description carries it.
* Every claim surface that says "axiom-free" must now say *which* of three
  numbers it means. The headline sentence above is the fixed form.
* A composed fact cannot be produced by today's kernel in the same environment
  as our own preludes (§4). Until Next Ten item 4's carrier correspondence
  ledger lands, the tier is reachable only for theorems whose whole proof term
  lives in the imported vocabulary. **This ADR is a decision about how such a
  fact is recorded, and the first one is not yet built.** `K = 0` is the honest
  count and the validator's composed-tier line will print nothing until it is
  nonzero.

**Revisited when.** The first `kernel-lean-over-import` fact lands — at which
point rule 4's traceability requirement gets its first real exercise and the
composed-tier line gets its first nonzero value. Also revisit if the
name-collision bridge lands and a composed theorem can cite both an import and a
prelude theorem: rule 2's footprint would then mix a kernel walk that crosses
both vocabularies, and the derivation should be re-measured rather than assumed
to still be exact.

**Reversible on evidence.** If a composed fact is ever found whose footprint is
NOT the union of the import's closure and the three route assumptions — for
example because a bridge admits a declaration that launders a trusted one — the
route's derivation rule is wrong and this ADR is reopened, not patched.

## Related

* [ADR-0601](adr-0601-three-producers-one-trust-anchor.md) — three producers,
  one trust anchor; imports are labeled scaffolding, never headline
* [ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md) —
  the graded statement family this adds a row between
* [ADR-1090](adr-1090-ivt-evt-row-4-labeled-import-lands-mathlib-topology-admits-clean.md)
  — the labeled-import route and the seven facts on it
* [ADR-1601](adr-1601-classical-logic-enters-as-a-hypothesis-not-as-an-axiom.md)
  — why OUR classical principles are hypotheses and not axioms, which is what
  makes the two regimes distinguishable in the first place
* [ADR-0509](adr-0509-the-trusted-surface-is-measured-as-reached-not-only-declared.md)
  — a trusted surface is what a walk reaches; rule 2 derives the composed
  footprint for exactly that reason, and names the three assumptions no walk
  can reach
* `docs/math-department/14-lean-lang.md` — Next Ten item 8, and items 4 and 9
  which remove §4's obstacle
* `docs/math-department/03-classical-analysis.md` — the reviewer whose blocker
  this closes
