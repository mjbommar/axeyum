# Lane: nursery-v2-component-coverage — nursery-v2-extension was invisible to the component-split gate

<!-- plan-section: lane-status -->

**Done** (`done`, nursery-v2-component-coverage, 2026-08-30). Extended
`scripts/check-autogenesis-nursery.py`'s declared-dependency component-split
check to the union of `nursery-v1.json` and `nursery-v2-extension.json`:
`build_cross_population_report()` found 3 previously-invisible cross-population
component crossings (none held-out) and they are now exempted with full detail
per ADR-0850's mechanism. ADR-0855 records the decision and settles ADR-0850's
open train/development invariant question from the existing record. Full
diagnosis, mutation guard->test table, and open items below.

## Task

`scripts/check-autogenesis-nursery.py` only ever reads
`artifacts/autogenesis/nursery-v1.json` for its declared-dependency
component-split check. `artifacts/autogenesis/nursery-v2-extension.json`
(340 entries) is invisible to it entirely — no v2-internal crossing and no
v1<->v2 crossing is checked anywhere.

## Diagnosis (independently measured, union graph over v1 entries + v2 entries,
adjacency from `artifacts/facts/*.json` `depends_on`, restricted to edges
where both endpoints are in the v1∪v2 selected set)

v1/v2 fact_id overlap: **none** (0 of 556 total ids collide).

Computing weakly-connected components over the **union** surfaces **3**
declared-dependency components that cross evaluation partitions
(train/development/held-out), none involving held-out:

1. `4c696b5744bb...` — 3 members, **entirely within v2**:
   `F:ml430-nat-div-gcd-pos-of-pos-left-dd878a3f` (train),
   `F:ml430-nat-div-gcd-pos-of-pos-right-8d26808c` (train),
   `F:ml430-nat-div-mul-cancel-99799a00` (development).
2. `510e9696bc85...` — 206 members, **v1 ∪ v2 merge**. This is v1's THREE
   ADR-0850-exempted components (`de94125d520a`, `6959be9c08c2`,
   `533d01fc3b24`, all train/development, previously the entire finding of
   ADR-0850) merged with TWO v2-internal crossing components
   (`aee5f7b663cc`, `11b9f2566178`) into one component, via real declared
   dependency edges between v1 and v2 facts (`int-gcd`/`int-dvd`/`nat-choose`/
   `nat-coprime`/`nat-factorial` families chain together). Also touches the
   two longitudinal Autogenesis-1 facts (`F:nat-mul-one`, `F:nat-zero-add`),
   same as ADR-0850 already found for the v1-only version of this component.
3. `55e86f8aed26...` — 4 members, **v1 ∪ v2 merge, newly visible only in the
   union** (does not appear as a crossing in v1-only OR v2-only analysis):
   `F:ml430-int-modeq-add-left-cancel-062ad5fe` (v1, train) plus three v2
   development entries (`...-c1adde5a`, `...-d7366811`, `...-f74acb64`).

Detail moved to [`../notes/nursery-v2-component-coverage.md`](../notes/nursery-v2-component-coverage.md).

