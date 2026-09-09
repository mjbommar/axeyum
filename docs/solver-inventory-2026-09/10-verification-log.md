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

## What was not verified

- No claim in this folder was confirmed by execution. Nothing here was built,
  and no gate was run.
- Reachability is a source-level property as measured. Dispatch through a trait
  object, a macro, or a registry table can hide a caller from a textual search.
  Each area file states its searches so a reader can re-run them.
- The coordinator re-checked roughly 38 claims across nine files totalling about
  5,200 lines. That is a sample chosen for load-bearing-ness, not a full audit.
  Claims not listed above carry their lane's evidence and nothing more.
