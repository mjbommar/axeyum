# 297 — The ledger-coverage gate: measuring how far the fact ledger trails the kernel

Date: 2026-08-27
Lane: ledger-coverage

## Task

`docs/plan/status/141-ledger-6-backlog.md` registered a hand-picked 12-fact
backlog and closed with an explicit admission: nobody has ever run the full
diff of `prelude_theorem_inventory --include-constructed`'s theorem list
against `artifacts/facts/`'s registered names, and a future lane should "run
that full diff and report its size as the headline trailing-the-kernel
measurement." Six ledger batches before it each hand-picked a short list to
register instead of measuring the gap. This lane builds that measurement and
makes it permanent: `scripts/gen-ledger-coverage.py`, gated in both
`scripts/check.sh` and `justfile` behind `--check`, so a newly-admitted
kernel theorem cannot silently stay unregistered forever.

## The denominator, and why

The population counted is every distinct `Declaration::Theorem` across every
constructed prelude, from `prelude_theorem_inventory --include-constructed`
(run `--release`; the debug build SIGABRTs and that reads as an absent
declaration, not a resource limit). That tool already excludes `Axiom`,
`Definition`, `Opaque`, `Inductive`, `Constructor`, `Recursor` and
`Quotient` by construction. This script inherits that exclusion rather than
re-deriving it:

* `Axiom` — not proved by us; excluding it is the *opposite* choice from what
  would inflate the metric, since `axreal`'s 30 axioms would otherwise read
  as "30 more theorems we could claim."
* `Definition` — a construction (`CReal.integral`, `CReal.e`), not a
  proposition a referee is asked to believe.
* `Inductive` / `Constructor` / `Recursor` — scaffolding the kernel
  generates from a type declaration; nobody registers `Nat.rec`.

Measured 2026-08-27 on this tree (post-merge with `main`, including the
`extreme_value.rs` / `mvt.rs` batch that landed same-day): **1,397 distinct
theorems**, all axiom-free — up from the "1,332+" figure this lane's brief
was given, itself already stale by the time of measurement. No further
filtering (size cutoff, namespace exclusion, "internal-looking name"
heuristic) is applied or needed: the distinct theorem set contains zero
`_proof_*`-shaped auto-generated names.

Per-prelude bucketing is by the theorem's own dotted NAMESPACE PREFIX
(`CReal.*` → `creal`, bare/`And.*`/`Or.*`/... → `logic`,
`axeyum.string.2.*` → `string`, ...), not by which `build_*_prelude` call
first reached it. The tool's own "origination" attribution exists and is
correct, but `creal`/`complex`/`cpoint` each build the FULL nested prelude
stack from scratch, so replicating that tie-broken algorithm here would be a
second, more fragile copy of logic this file does not own. Namespace
bucketing is simpler, self-contained, and reads the same name a fact's
`formal.kernel_theorem` would print.

## The headline number

**1,397 kernel theorems, 474 registered, 923 unregistered — 34% coverage.**

| prelude | kernel theorems | registered | unregistered |
|---|---:|---:|---:|
| creal | 369 | 132 | 237 |
| nat | 329 | 86 | 243 |
| rat | 244 | 116 | 128 |
| integer | 153 | 53 | 100 |
| complex | 117 | 36 | 81 |
| cpoint | 89 | 27 | 62 |
| string | 64 | **0** | **64** |
| logic | 32 | 24 | 8 |
| **total** | **1,397** | **474** | **923** |

The `string` prelude row is a real finding, not a join artifact: zero facts
in `artifacts/facts/` mention any `axeyum.string.2.*` name, confirmed by
grepping every fact's `formal` block. The entire string-prelude development
(64 theorems, axiom-free) has no ledger presence at all.

This is a large gap and it is not softened here: two-thirds of this
project's axiom-free theorem base is unregistered — proved, checked, and
invisible to a referee reading the ledger. `unregistered` names are emitted
per-prelude in `artifacts/ledger-coverage.json` as a literal work queue, not
just a count.

## The join, and why it needed three tiers, not one

A fact is "about" a kernel theorem through the first of three tiers that
applies: (1) `formal.kernel_theorem` when the key is present, including an
explicit `null` ("no single subject" — stops here, does not fall through);
(2) the declared name at the head of a `lean4` `formal.statement`
(`theorem <Name> :` / `def <Name> :` / bare `<Name> :`); (3) the sibling
`check-fact-depends-derived.py::theorem_of`'s checker_command regex,
imported rather than re-implemented so the two checkers cannot silently
diverge on what "the fact's subject" means.

**Tier 2 was necessary, not a nicety.** Using only tier 1 + the borrowed
tier-3 regex left `logic` at 2/32 "registered" and `string` at 0/64 — the
first is a fictitious near-zero. The borrowed regex's namespace allowlist
(`AxReal|AxNat|Nat|Int|Real|Rat|List|Bool|Prop|Acc|WellFounded|Str|CReal|
Complex|CPoint`) omits `And`, `Or`, `Iff`, `Decidable`, `Eq`, and has no
provision for a BARE (non-namespaced) name at all — so a fact like
`F:logic-and-left` (subject `And.left`) could never resolve through it, even
though its own `formal.statement` literally begins `theorem And.left : ...`.
Adding tier 2 raised `logic` to 24/32 and lifted the overall registered
count from 451 to 474.

One placeholder guard was needed along the way:
`F:real-lattice-is-constructed-axiom-free` carries the literal statement
`"TODO: the formal statement, precise enough to dispatch"`, which the
tier-2 regex otherwise happily parses as a declared name `TODO`. No real
kernel declaration renders ALL-CAPS, so tier 2 rejects an all-uppercase
capture — a narrow guard for the shape actually observed, not a general
"looks suspicious" heuristic.

**Join reliability, measured across all 818 facts:** 576 are `kernel-lean` +
`proved`/`computed`. Of those, 127 resolved via the explicit field, 374 via
the statement-name tier, 2 via the checker_command fallback, and **74 could
not be resolved at all** — genuinely unrecoverable from this fact's own
recorded evidence, not a bug in this script. Two examples: the `ml430-int-*`
facts carry `formal.language: "lean4-surface"` with Unicode notation
(`n + a ≡ a [ZMOD n]`), and their `checker_command`s name Rust *test
function* identifiers (`add_modeq_family_computes_at_concrete_values`), not
dotted kernel declaration names. `F:cauchy-schwarz-over-constructed-plane`
is the same shape (`cauchy_schwarz_statement_is_exact`). These are reported
in `join.unresolved_fact_ids`, not silently dropped or guessed at — a fact
whose evidence never names its kernel subject is exactly the case a future
`formal.kernel_theorem` addition would fix, and the field exists for this.

28 registered names resolved to something the theorem denominator does not
contain — surfaced in `registered_kernel_theorems_not_in_denominator`, all
inspected: every one is a `Definition` (`CReal.integral`, `CReal.e`,
`Rat.add`, `Complex.polyAdd`, ...), which is expected and not a defect —
these facts are legitimately about definitions, just outside this
denominator's scope.

## The gate cannot go vacuous by construction

`--check` regenerates and diffs against the committed
`artifacts/ledger-coverage.json`, mirroring `gen-plan.py --check`. Demonstrated
directly, not just unit-tested: appending one synthetic line
(`nat\tNat.synthetic_theorem_for_gate_demo\t0\t`) to a copy of the real
`prelude_theorem_inventory` output and running

```sh
python3 scripts/gen-ledger-coverage.py --check --theorem-tsv <fixture-with-synthetic-theorem>
```

exits 1 with `gen-ledger-coverage: ERROR: artifacts/ledger-coverage.json is
not what scripts/gen-ledger-coverage.py produces`, while the real `--check`
(no override) stays green. `--theorem-tsv` is a documented testing/demo
hook substituting for the cargo call; production usage never passes it.

`parse_theorem_inventory` separately refuses zero rows as an error — the
debug-build-SIGABRT / missing-`--include-constructed` trap CLAUDE.md
documents elsewhere, which would otherwise read as "measured, and nothing to
report" — and refuses a theorem name printed with two disagreeing footprint
sizes across nested prelude groups, since that would mean the underlying
tool's own output is internally inconsistent rather than that this script
should pick one arbitrarily.

## Mutation controls

`scripts/tests/mutation_controls.py ledger-coverage` registers seven guards
(placeholder-name rejection, explicit-null-stops-resolution, string-prelude
namespace recognition, footprint-disagreement detection, empty-inventory
rejection, kernel-route filtering, established-status filtering), each
required to be killed by exactly one test in
`scripts/tests/test_gen_ledger_coverage.py` (26 tests total, all passing).

## Scope discipline

Nothing under `artifacts/facts/`, `artifacts/autogenesis/`, `crates/`,
`hooks/`, or the other validators was touched. `scripts/check.sh` and
`justfile` each received one minimal, clearly-commented append next to the
existing `gen-import-backlog.py` registration, matching that gate's
`--check` convention exactly.
