# Coordinator verification log (2026-09-09)

Nine agents produced the area files in this folder. This file records which of
their claims the coordinator re-checked independently, what the check was, and
where a check changed the result. It exists because a nine-agent inventory whose
findings nobody re-derived is a set of assertions, not a measurement.

Base commit `ea8515407`. Every check below is a source read or a `grep` with an
explicit positive control; no build was run.

## Method

For each lane, the coordinator picked the claims that were load-bearing — the
ones a reader would act on — and re-ran them from scratch. Negative results
(`NO CALLER FOUND`) were checked with a positive control: a known-wired sibling
that the same search does find. An empty search result with no control is not
evidence.

## Results by lane

| Lane | Area | Checks | Outcome |
|---|---|---|---|
| L1 | SAT core, CNF | 5 | 5 pass |
| L2 | Front end, IR, rewriting | 4 | 4 pass |
| L3 | Dispatch, routing, backends | 4 | 4 pass |
| L4 | Arithmetic theories | 4 | 4 pass |
| L5 | BV, arrays, FP, datatypes | 4 | 4 pass |
| L6 | EUF, quantifiers | 5 | 5 pass |
| L7 | Strings, regex | 5 | 5 pass, 1 sharpened |
| L8 | Models, proofs, evidence | 4 | 4 pass |
| L9 | Harnesses, gates | 3 | 3 pass, corrected the coordinator |

A later follow-up measurement (below) corrected L8 on `bitblast_miter`.

## The four checks that changed something

**L9 corrected the coordinator's own count.** The README first said
`full_modules!()` held "roughly 200" modules. The exact count is 165
(`sed -n '70,252p' lib.rs | grep -c '^\s*mod '`). Fixed.

**The coordinator's grep was the narrow one, twice.**

- Counting feature-gated test suites, `^#!\[cfg(feature` returned 296 against
  L9's 298. L9 was right: `native_cdcl_baseline.rs` and
  `xor_cdcl_curated_measure.rs` use `#![cfg(all(feature = "full", feature =
  "batsat-reference"))]`, which that pattern silently omits. The broader
  `^#!\[cfg(` returns 298.
- Checking L3's claim that four `theory_combination` functions have no callers,
  a first grep showed 9 references to `shared_terms`. They are a local variable
  in `abduct.rs:306-337` plus two multi-line `pub use` blocks in `lib.rs` whose
  continuation lines a `grep -v 'pub use'` filter does not catch. L3's claim
  stands; the positive control (`classify_interface_equalities`, 23 real
  references) confirmed the search worked.

**A naive count contradicted L8 and was wrong.** `grep -c 'Evidence::Unsat(None)'`
returns 29 against L8's 8 construction sites. Decomposing: 16 are comments, 3
are inside the `#[cfg(test)]` region beginning at `evidence.rs:4930`, and 3 of
the remainder are match arms that *read* the variant rather than build it. That
leaves exactly 8. L8's number was right and the naive one was misleading.

**L7's finding was sharpened, not corrected.** L7 reported that
`axeyum-solver/src/strings.rs`'s `BoundedString` and the production encoder in
`axeyum-smtlib/src/parse.rs` are "kept in sync only by a comment." Checking the
three `parse.rs` references showed all three are comments (`:8306`, `:8332`,
`:10363`) and that `axeyum-smtlib` has no dependency on `axeyum-solver` at all.
The two encodings are not merely unsynchronized — they *cannot* share code
across that crate boundary without a refactor, and nothing enforces agreement.

## One case where the file was better than the summary

L8's report to the coordinator said `grep -rni carcara scripts/ .github/
justfile` "finds it only in `fetch-references.sh`." That is false —
`scripts/check-capability-assurance.py` matches too, and it is a registered gate
(`check.sh:872`, `justfile:579`). But L8's **file** already said exactly this,
naming that script as "a regex over prose, not a run of Carcara" at both
`:62-64` and `:301-304`. The summary was loose; the artifact was correct.

The general rule this instance teaches, and the reason this log exists: verify
the artifact, not the report about the artifact.

The coordinator added one fact to L8's picture: because that gate classifies the
free-prose `evidence` field of `capabilities.rs` by regex, the repository's
"external-artifact-checker" tier is populated by pattern-matching sentences
about Carcara rather than by Carcara accepting an artifact.

## Follow-up measurement: "is everything wired?" (2026-09-09)

Asked directly whether the implemented surface is integrated, the coordinator
ran a uniform module-level measurement rather than summing the lanes' tallies,
which use different units (files, functions, routes) and share no denominator.

Method: take every `mod X;` declared in `crates/axeyum-solver/src/lib.rs` (176,
counting the default set and the 165 inside `full_modules!()`). For each, search
every *other* file in the crate for either the module path (`X::`,
`use crate::X`) **or** any item name `lib.rs` re-exports from it. The second half
matters: `evidence.rs:4376` calls `crate::prove_qf_abv_unsat_alethe(...)`, the
crate-root re-exported name, so a module-path search alone reports it absent.

| Result | Count |
|---|---|
| Modules declared in `lib.rs` | 176 |
| Referenced by at least one other module in the crate | 161 |
| Referenced by no other module | 15 |

Resolving those 15 against consumers outside the crate:

| Module(s) | Status |
|---|---|
| `solver` | The `Solver` façade itself — it *is* the public API. Referenced by 44 solver test files and 8 other crates. |
| `strategy` | Reachable, but only from the Python bindings (`axeyum-py/src/solver/core.rs:201` calls `axeyum_solver::solve_with_strategy`). |
| `bitblast_miter` | Reachable from `axeyum-bench` (see the correction below). |
| `aufbv` | Reachable only from a bench example (`axeyum-bench/examples/route_solo.rs`). |
| `abduct`, `enums`, `faithfulness`, `horn`, `hypothesis_min`, `imc_lia`, `lex_reconstruct`, `pb`, `pdr_lia`, `records`, `toy_bv_vm` | Reachable only from `axeyum-solver`'s own test suite. Apparent hits in `axeyum-cas` and `axeyum-lean-kernel` are name collisions — neither crate depends on `axeyum-solver`. |

So about 11 of 176 modules are test-only at module granularity. That figure is a
floor, not the whole answer: it cannot see dead *functions* inside live modules,
and the lanes found several (all 7 `*_certified` interpolant variants, four
`theory_combination` functions, `prove_quant_unsat_alethe`).

## Fifth correction: `bitblast_miter` is not dead

L8 reported that `bitblast_miter.rs` (1,030 lines) has "no production caller."
That is wrong, and the coordinator's own first two searches repeated the error
before catching it. The module's exported entry point is
`certify_qf_bv_unsat_end_to_end_within` — a name that does not contain "miter" —
and it is called from `axeyum-bench/src/main.rs:5782` and
`axeyum-bench/src/certificate_process.rs:170`, both in the shipped bench binary,
plus `axeyum-verify/tests/tock_log2_external.rs:211`.

Corrected in `08-models-proofs-and-evidence.md` and in the README's synthesis.
The narrower true statement: nothing inside `axeyum-solver` calls the miter, so
a `Solver` user gets no miter check unless they go through `axeyum-bench`.

This is the fifth instance in this session of the same failure — **searching for
a module or concept by name instead of by the identifier a caller would actually
write**. Four of the five were the coordinator's.

## Sixth correction: BOTH duplicate-pipeline rows were wrong about which side is trusted (2026-09-09)

Found by the ADR lane executing roadmap items 1.3/1.4, which was told to verify
the inventory rather than take it on trust, and did. The coordinator re-verified
both against the source before accepting them.

**The `/0` witness claim.** The inventory published: "Neither preprocessing
pipeline is a superset of the other … the front door's path does not carry it."
False. `auto.rs:2344` carries `real_div_zeros` — same comment as
`preprocess.rs:221-224`, present since 2026-07-25 — and `auto.rs:2335`
additionally carries function interpretations, which `preprocess.rs` never
builds (zero `set_function` calls). The front door is a strict SUPERSET, and the
hazard described has not existed for months.

**The `ReductionLink` claim.** The inventory implied the shipping inprocessing
path used "a different certificate mechanism" and was therefore the untrusted
side. False. `ReductionLink` is `axeyum-cnf/src/reduction_link.rs:156` — the
SAME crate as `inprocess.rs` — and ADR-1780 (2026-09-08, one day before the
inventory was written) made the shipping path check its `unsat` against the
original formula through it (`sat_bv_backend.rs:2812`). `inprocess.rs` is the
side that structurally cannot, having no way to express the backend's
`compact()` renumbering.

What survives: `inprocess.rs` genuinely has no caller in `axeyum-solver`, and
the duplication in both subsystems is real. What does not survive: the claim
about which side carries the evidence — which was the framing of the whole
section, and its title.

**How the error was made.** Two independent passes verified `preprocess.rs`'s
witness loop and `auto.rs`'s pass ORDER, each in isolation, and inferred an
asymmetry from the pair. Neither asked whether `auto.rs` ALSO had the witness.
Every individual citation was correct; the conclusion drawn across them was not.

This is the same shape as the ten grep failures recorded above, at a larger
scale: **a partial view of each half is not a view of the whole.** It is also
the first error in this folder that a reader acting on the documents would have
paid for — the roadmap's item 1.4 was written to fix a hazard that did not
exist. Corrected in `00-README.md` §1, `02-frontend-ir-and-rewriting.md`, and
roadmap items 1.3 and 1.4, each carrying a dated correction note rather than a
silent edit.

## What was not verified

- No claim in this folder was confirmed by execution. Nothing here was built,
  and no gate was run.
- Reachability is a source-level property as measured. Dispatch through a trait
  object, a macro, or a registry table can hide a caller from a textual search.
  Each area file states its searches so a reader can re-run them.
- The coordinator re-checked roughly 38 claims across nine files totalling about
  5,200 lines. That is a sample chosen for load-bearing-ness, not a full audit.
  Claims not listed above carry their lane's evidence and nothing more.
