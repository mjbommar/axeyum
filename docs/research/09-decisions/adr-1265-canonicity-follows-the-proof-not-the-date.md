# ADR-1265: canonicity follows the proof, not the date

Date: 2026-08-31
Status: Accepted
Lane: `trust-closure-equivalent`

Index-summary: A repair that made `Rat.int_right_distrib` forward to `Int.add_mul` moved that pair from ADR-0790's INDEPENDENT bucket (canonical = earlier `provenance.date`) into its DISCLOSED bucket (canonical = the member reached in the other's closure), inverting the designation without touching either fact. `equivalent_to` moves to `F:rat-int-right-distrib`, the pair is disclosed in `equivalent-pairs.tsv` (13 -> 14), and a new `canonical_is_the_dependency` guard enforces ADR-0790's direction rule, which nothing checked. Neither headline number moves: settled 2253, DISTINCT PROPOSITIONS 2233, before and after.
Index-status: Accepted

## Context

`scripts/check-trust-closure.py` was RED on `main`:

```
TRUST_CLOSURE_ERROR|EQUIVALENT-IN-CLOSURE F:rat-int-right-distrib:
  `Rat.int_right_distrib`'s closure contains `Int.add_mul`, whose canonical
  kernel type is byte-identical -- the target was not proved, an equivalent
  was renamed.
TRUST_CLOSURE|declarations=2711|identity_classes=15|kernel_facts=2165|
  subjects=2075|unresolved=90|absent=0|disclosed_equivalent_pairs=13|failures=1
```

It went red because a fix was correct. ADR-1170 wired up
`scripts/check-shape-duplicates.py`, a complete gate that had been registered
nowhere; its first automatic run found five duplicate groups, one of them
genuine — `Rat.int_right_distrib` and `Int.add_mul` stated the same
proposition and ran the same chain (`mul_comm` thrice plus `left_distrib`) in
two preludes. The repair made the Rat name forward:

```rust
let proof = d.lemma(int.add_mul, &[a, b, c]);
```

One proof term, two names. That is right, and it removed the duplicate proof.
What it did not do is move the ledger.

## The decision, and why it is not a new mechanism

ADR-0790 already decides this. Its canonical-choice rule reads, verbatim:

> Canonical choice, applied uniformly: for the 13 disclosed pairs, the
> canonical member is the one whose kernel theorem is REACHED IN the other's
> proof closure (the dependency, not the wrapper). For the 2 independent
> pairs, the canonical member is the one registered EARLIER by
> `provenance.date` (`Rat.int_right_distrib`, 2026-08-25, predates the
> `Int.add_mul` mirror by four days).

So this pair was one of the two INDEPENDENT ones, and it was settled by date.
It stopped being independent the moment the proof started forwarding. The pair
moved buckets, and the primary rule now applies to it: canonicity belongs to
`Int.add_mul`, the dependency.

Measured over the environment rather than argued (2,711 declarations, all 15
identity classes, closure from `Kernel::declaration_dependencies`):

| | classes |
| --- | --- |
| a REACHES relation exists between the two members | 14 |
| ...of which canonicity is on the REACHED member | 13 |
| ...of which canonicity is on the WRAPPER | **1** — this pair |
| genuinely independent (neither reaches the other) | 1 — `CPoint.apollonius_*` |

One inversion out of fifteen, and it is the one the repair created.

Therefore:

1. `equivalent_to` moves from `F:ml430-int-add-mul-66aa025b` to
   `F:rat-int-right-distrib`, which now names the Int fact as canonical.
2. The pair is disclosed in `artifacts/trust-closure/equivalent-pairs.tsv`,
   written by `check-trust-closure.py --update` rather than by hand: 13 rows
   to 14.
3. The duplicate is ACKNOWLEDGED in `F:rat-int-right-distrib`'s `notes`, which
   names the identity class, the ADR-1170 repair that created the containment,
   and this decision.
4. Both facts stay `proved` with their evidence intact. Nothing is deleted and
   nothing is retracted — ADR-0542 — and `retracted=0` in
   `check-settled-fact-statements.py` stays 0.

### The declaration is kept; only the FACT is a duplicate

`p.int_right_distrib` has 14 consuming call sites, every one inside
`rat_prelude/` (`scaling.rs` 12, `laws.rs` 1, `group.rs` 1), plus its own
declaration site and one test — 16 occurrences in total.

The comment ADR-1170's repair left in `rat_prelude/laws.rs` says "20 call sites
across `rat_prelude/` and `creal/sqrt.rs`". Both halves are wrong.
`creal/sqrt.rs` never names `p.int_right_distrib`; it carries a private local
`fn int_right_distrib` that re-derives the same chain inline — a THIRD copy of
this proposition, and one that no identity class can ever see, because it
declares nothing. That is CLAUDE.md's hiding place 2, and it is out of scope
here; it is recorded so the next lane does not have to rediscover it.

### Neither headline number moves

| | before | after |
| --- | --- | --- |
| FACTS SETTLED | 2253 | 2253 |
| facts carrying `equivalent_to` | 20 | 20 |
| DISTINCT PROPOSITIONS ESTABLISHED | 2233 | 2233 |

The pair was already collapsing to one proposition. Only which fact id a
reader is pointed at changed — and it now points at the one whose proof term
does the work.

## The gap this exposed, and the guard that closes it

ADR-0790 states the direction rule and **nothing enforced it**. Both
neighbouring gates were green on the inverted state, for structural reasons
rather than by accident:

- `guard_unlabeled_duplicate_pair` counts canonical members per class and
  found exactly one. A count cannot see a direction.
- `check-trust-closure.py`'s `guard_alias_occurrence` keys its disclosed
  backlog on `(fact, subject, equivalent-reached)` and never reads
  `equivalent_to` at all. Disclosing the pair silences it whichever way
  canonicity points.

So after the disclosure row alone, a lane could flip the two markers back
tomorrow, both gates would pass, and the published DISTINCT PROPOSITIONS count
would point a reader at a fact that proves nothing of its own. A disclosure
that makes the tree green without making the inversion detectable is the
checker-that-cannot-fail defect arriving through the door marked "follow the
existing mechanism".

`guard_canonical_is_the_dependency` (`check-proposition-duplication.py`) reads
the transitive closure — `check-trust-closure.py`'s `closures(decls)`, computed
from the admitted term, never a fact's authored `depends_on` — and rejects when
a class's canonical member reaches a marked class-mate.

Verified against the reconstructed pre-fix ledger (both markers restored from
`HEAD~1`, current projection):

```
PROPOSITION_DUPLICATION_ERROR|CANONICAL-IS-NOT-THE-DEPENDENCY
  F:rat-int-right-distrib (`Rat.int_right_distrib`) ... REACHES `Int.add_mul`
  (F:ml430-int-add-mul-66aa025b), which carries the `equivalent_to` marker
  guard canonical_is_the_dependency  scanned=15 rejected=1
  every other guard                            rejected=0
```

Exactly one guard fires, which is the measurement that the direction really is
invisible to the other nine.

`scripts/tests/test-proposition-duplication.sh` gains
`case_canonical_is_the_dependency` and its mutation. The suite's baseline
projection carries no dependency edges at all, so this guard is unreachable
from every other case; the new case adds one edge from `T.d1` (canonical) to
`T.d2` (marked). Result: **11 cases, 10 mutations, each killing exactly one**,
and the new mutation kills only `canonical-is-the-dependency`.

## Proof that the disclosure did not silence the guard

A per-pair backlog is only worth having if it stays per-pair. Three probes
against the shipped tree, each with a captured projection:

| probe | result |
| --- | --- |
| remove the row this lane added | `EQUIVALENT-IN-CLOSURE F:rat-int-right-distrib`, failures=1 |
| remove a DIFFERENT pre-existing row (`F:nat-succ-le-succ`) | `EQUIVALENT-IN-CLOSURE F:nat-succ-le-succ`, failures=1 — and it does NOT name the rat pair |
| add a row that no longer occurs | `STALE-DISCLOSURE F:nat-succ-injective`, failures=1 |

The ratchet holds in both directions: a pair not listed rejects, a listed pair
that stopped occurring also rejects.

## Consequences and what was deliberately not done

- `artifacts/trust-closure/population.json` is NOT updated, though `--update`
  rewrites it. It would have raised `min_subjects` 2004 -> 2075, `min_ratio`
  0.9579 -> 0.9584 and `min_declarations` 2548 -> 2711 — and **dropped the
  hand-written `ratio_floor_note`**, which is the paragraph telling the next
  lane not to lower that ratio to accommodate growth. `--update` does not
  preserve it. Raising a floor is a separate, deliberate act; the file was
  restored to `HEAD`. That the generator silently discards its own file's
  reasoning is a defect worth fixing separately.
- The `creal/sqrt.rs` inline third copy is left alone.
- `unresolved=90` is untouched; see below.

## `unresolved=90`, and it is one away from firing

`unresolved` counts kernel-route settled facts whose kernel declaration
`subject_of` cannot identify — no `formal.kernel_theorem` key, no unambiguous
`evidence[].kernel_declaration`, and the dotted-name regex over the fact's
`checker_command`s finds nothing. Such a fact counts toward `kernel_facts` but
is not a SUBJECT, so `guard_self_occurrence`, `guard_alias_occurrence` and
`guard_forbidden_trust` never examine it. The line prints "(not enforced)".

Measured on this tree:

| | count |
| --- | --- |
| no `kernel_theorem` key, no evidence declaration, regex found nothing | 81 |
| explicit `"kernel_theorem": null` — authoritative "not about one theorem" | 7 |
| several distinct `evidence[].kernel_declaration` (umbrella facts) | 2 |

**Only 9 of the 90 are deliberately unresolvable.** The other 81 are
under-annotated rather than unresolvable, and it is mechanical: sampling
`F:cauchy-schwarz-over-constructed-plane`,
`F:fermat-little-theorem-over-constructed-naturals` and
`F:geometry-stewart-over-constructed-reals`, each has evidence rows whose `id`
literally spells the declaration (`kernel-CPoint.cauchy_schwarz`) while
`kernel_declaration` is `null` and `formal.kernel_theorem` is absent. Filling
either field resolves them.

It is *indirectly* enforced and the margin is one:

```
kernel_facts 2165, resolved 2075, ratio 0.958430
min_ratio floor 0.9579 -> unresolved may reach 91 before guard_population fires
```

So 90 is not drift — it is 90 of a permitted 91. The next kernel-lean fact that
lands without naming its declaration turns an L0 gate red, and the failure will
read as a population-floor breach rather than as a missing annotation. That is
a real queue item and it is not this lane's; ADR-1005 already bound 660 subjects
that had been resolved by text extraction, and the same treatment applied to
these 81 would take resolution to ~99.6% and put the floor back out of reach.

## References

- ADR-0790 — duplicate identity classes are labeled, not deleted; the two
  numbers; the canonical-choice rule this ADR applies.
- ADR-1170 — the retrieval gate existed and ran nowhere; the repair that
  created the containment.
- ADR-0542 — no deletion of a settled fact, only an amendment.
- ADR-1005 — binding fact subjects that had been resolved by text extraction;
  the `min_ratio` note in `population.json`.
- ADR-0717 — risk 4, contamination, which `check-trust-closure.py` computes.
