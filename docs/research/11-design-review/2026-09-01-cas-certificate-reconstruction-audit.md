# CAS certificate audit: what reconstructs, what could, what is `cas-internal`

**Status: IN PROGRESS.** The measurement section below is complete and
re-runnable. Per-module verdicts are being filled in; a row marked `TODO` has
not been read yet and is not evidence.

Dispatched against
[`2026-09-01-the-cas-certifies-far-more-than-the-ledger-records.md`](2026-09-01-the-cas-certifies-far-more-than-the-ledger-records.md).

## Both of the parent document's headline numbers are wrong, in opposite directions

The parent's finding — the CAS certifies more than the ledger records — survives.
Its two numbers do not. Both were produced by string queries that answer a
narrower question than the one asked, and they err in **opposite** directions, so
the gap the parent reports (40 modules against 19 facts) is roughly twice the
real one.

### The numerator: `40 of 53` counts doc-comment prose

The parent's query is `certificate|Certificate|fn verify|fn check_` over
`crates/axeyum-cas/src/*.rs` with no masking. This crate's doc comments are
unusually discursive — they discuss certificates at length in modules that emit
none — so the pattern matches text, not code.

Re-measured with Rust line comments, block comments and string literals masked
out (`scripts/` has no tool for this; the masker used is recorded in the ADR):

| query | modules |
| --- | --- |
| the parent's pattern, unmasked | **41 of 55** |
| the same pattern, comments and string literals masked | **27 of 55** |
| a second, differently-shaped query: `struct`/`enum` named `*Certificate`/`*Cert`/`*Witness`, or `fn verify_*`/`check_*`/`certify_*`/`validate_*`, masked | **23 of 55** |
| union of the two masked queries | **30 of 55** |

Two independent shapes agreeing at 27 and 23 is the check the parent's single
grep did not have. **The certificate-carrying surface is ~27 modules, not 40.**

(The module count also moved, 53 → 55, because the tree advanced between the two
measurements. Quote 55.)

### The denominator: `^F-cas-` counts a filename convention, not a route

`ls artifacts/facts/ | /usr/bin/grep -c "^F-cas-"` returns **19**, and that is a
correct answer to a question about filenames. The ledger's own notion of a CAS
result is `proof_route`, and `scripts/validate-facts.py` reports it directly:

```
routes: cas-certificate=48(kernel-reconstructed=14,cas-internal=34) …
```

**48 facts, not 19.** The 29 the filename query misses are named for their
mathematics rather than their producer: nine telescoping facts
(`F:apery-numbers-recurrence`, `F:franel-numbers-recurrence`,
`F:chu-vandermonde-convolution` and six binomial row-sum identities), seventeen
geometry facts, four GF(2) facts.

This matters beyond arithmetic, because it falsifies a specific claim in the
parent: that Gosper and Zeilberger creative telescoping have "no ledger fact at
all". `telescoping.rs` and `telescoping_check.rs` are each named by **nine**
settled facts. `gosper.rs` genuinely has none.

### The measurement that actually answers the parent's question

Neither count alone is the gap. The gap is *certificate-carrying modules that no
fact names*, which needs both sides joined per module. Joining the masked
certificate-surface query against every fact's `artifact` and `checker_command`
strings:

| | naming fact | no naming fact |
| --- | --- | --- |
| **certificate surface** | 14 | **13** |
| **no certificate surface** | 6 | 22 |

The thirteen uncovered certificate-carrying modules are:

```
boolean_circuit  geometry_json  gf2_artifact  gf2_independent  gf2_search
gf2_shard  gf2_tensor  gosper  groebner_cert  lib  ratint  sos
telescoping_json
```

The six modules with a fact but no certificate surface of their own —
`cofactor_ansatz`, `geometry`, `geometry_corpus`, `linear_elim`, `mvpoly`,
`sturm` — are not an anomaly: they are consumed by a certifier that lives in a
sibling module, which is exactly the retrieval hazard this repository documents
elsewhere (general infrastructure filed under its first consumer). A
module-granular coverage metric will always misreport them, in either direction.

**So the honest statement of the deficiency is: thirteen certificate-carrying
modules with no ledger fact, not thirty-four.** That is a smaller number and a
more actionable one, and every module in it is named.

## Verdict table

TODO — per-module, filled in as each is read.
