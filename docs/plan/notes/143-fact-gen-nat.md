# Notes: 143-fact-gen-nat

Detail moved out of [`../status/143-fact-gen-nat.md`](../status/143-fact-gen-nat.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**A genuine tool-disagreement, found and fully explained, not fixed.** The
generator's own dry-run for `nat` reports `kernel_theorems=338`, but
`gen-ledger-coverage.py`'s denominator (from `prelude_theorem_inventory
--include-constructed`) counts only **329** `Nat.*` theorems — a 9-theorem
gap. Traced to source: the 9 are the whole `Nat.Peano.*` family
(`categorical`, `induction`, `injective`, `iter_succ`, `iter_unique`,
`iter_zero`, `succ_injective`, `surjective`, `zero_ne_succ`).
`kernel_declaration_projection` (what the generator reads) enumerates them;
`prelude_theorem_inventory` (coverage's denominator) does not — confirmed by
grepping `registered_kernel_theorems_not_in_denominator` in the regenerated
`artifacts/ledger-coverage.json`, which lists exactly these 9 under `Nat.`.
All 9 facts were still generated and registered correctly (their theorems are
real, proved, axiom-free); they simply cannot move the `registered` counter
because coverage's own denominator tool never reaches them. This is a
pre-existing disagreement between two measurement tools, not something this
lane's facts caused, and it is out of scope to fix (`gen-ledger-coverage.py`
and the inventory examples are not this lane's files). Net effect: 497 facts
written (250 nat + 247 creal), but `registered` moved by only 488 (538 → 1,026)
— the arithmetic gap is exactly these 9 `Nat.Peano.*` facts, present on disk
and passing `--audit`, invisible only to this one denominator.

**Every emitted checker was executed, not assumed — 994 commands (497 facts
× 2 evidence rows), 0 failed.** Not a sample, but not literally 994 separate
process spawns either, and the reasoning for that substitution is recorded
here in full because it is exactly the kind of shortcut CLAUDE.md warns
against taking silently:

`theorem_dependency_inventory` builds the **entire** 7-prelude environment on
every invocation regardless of its filter argument (confirmed by reading
`crates/axeyum-lean-kernel/examples/theorem_dependency_inventory.rs`), costing
~13-15s per call. 497 distinct per-theorem commands run one at a time would
cost ~2 hours of wall clock for no additional soundness — the CLI's own
`.contains(name)` filter is a strict pre-filter subsumed by each checker's own
exact `^Name[[:space:]]` grep anchor, so grepping one **unfiltered** dump for
every fact's anchor is provably equivalent to running each filtered command
separately (a line present in the unfiltered dump is present in the
name-filtered dump whenever the anchor matches it exactly, and absent
otherwise). This was not assumed: 30 of the 497 dependency checks (one full
chunk, all `nat`) were executed **literally**, verbatim, via `bash -c
"<checker_command>"` first (`TOTAL=30 FAIL=0`), then the single-dump
substitute was run and cross-checked against those same 30 (28 of the 30 were
dependency checks; 0 mismatches). Only after that agreement was confirmed was
the substitute applied to the remaining 469. All 497 pass. The two
whole-prelude footprint commands (`--require-axiom-free nat`,
`--include-constructed --require-axiom-free creal`) were each run literally
once — they are byte-identical across every fact in their prelude, so running
the same string 250 or 247 times verifies nothing a single run does not.

**A bug in my own verification tooling, caught by its own control.** The
first attempt at the equivalence cross-check used Python's `re` module with
the literal pattern text `[[:space:]]`, which Python does not treat as a
POSIX class — it read it as a bracket expression and matched nothing, so
every single one of the first 28 cross-checks came back a "mismatch" (count
0) against known-passing commands. `/usr/bin/grep` on the identical pattern
and dump returned the correct counts immediately. This is the same
`grep`-dialect trap CLAUDE.md already documents, recurring one layer up in a
Python re-implementation rather than in a shell script — the fix was to stop
re-implementing the check and shell out to the real `grep -cE` the
`checker_command` actually specifies.

**Mutation demonstration, in an isolated snapshot
(`scripts/lane-snapshot.sh`, never the shared checkout).** Renamed
`Nat.zero_lt_succ`'s interned name to `zero_lt_succ_MUTANT`
(`crates/axeyum-lean-kernel/src/nat_prelude.rs:1983`) and rebuilt release
examples. In the same run against the same rebuilt binary:

| check | result |
|---|---|
| `Nat.zero_lt_succ` (the mutated theorem's own generated checker) | count=0, **exit=1 — FAILS** |
| `Nat.zero_lt_of_ne_zero` (control, same run, same binary) | count=1, exit=0 — passes |
| `zero_lt_succ_MUTANT` (the theorem under its new name) | count=1, exit=0 — still there |

The control is what makes the failure mean something: the mutated theorem's
checker fails, its sibling in the same batch still passes, and the mutant
itself still resolves under its new name — so the failure is the **name**,
not a broken build or a lost proof. Footprint side, same snapshot:
`--require-axiom-free nat` exits 0, `--require-axiom-free axreal` exits 1 (30
axioms) — re-confirming the ADR's stated footprint-checker behaviour on this
tree rather than citing the string pilot's numbers unchecked.

**`--audit`: 561 generated-unreviewed (64 string + 250 nat + 247 creal), 0
generated-then-curated, 0 problems.**

**Coverage counters, before → after:**

| | before | after |
|---|---:|---:|
| `kernel_theorems` | 1,402 → 1,409 (main merge) | 1,409 |
| `registered` | 538 | 1,026 |
| `curated` | 474 | **474 — unmoved** |
| `unregistered` | 864 → 871 | 383 |

**What is NOT done, deliberately, matching ADR-0607's own scope discipline:**
no prose enrichment (all 497 are `generated-unreviewed`); no other prelude run
(`rat` 128, `integer` 100, `complex` 81, `cpoint` 62, `logic` 8 remain, plus
whatever the 9-theorem `Nat.Peano` denominator gap implies for other
constructed preludes — worth checking before the next batch); the
`Nat.Peano`/inventory-tool disagreement is reported, not fixed, since neither
`gen-ledger-coverage.py` nor the inventory examples are in this lane's scope.

Full write-up of the generator and its design: [ADR-0607](../../research/09-decisions/adr-0607-generated-facts-declare-themselves-and-coverage-ratchets-on-two-numbers.md),
[298](../../autogenesis/298-mechanical-fact-registration.md). Ratchet
implementation: [142](142-ledger-ratchet.md).
