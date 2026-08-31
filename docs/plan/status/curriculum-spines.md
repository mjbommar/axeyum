# Lane: curriculum-spines — re-measure the depth spine a third time, and the bucket bug recurred

<!-- plan-section: lane-status -->

**Re-measured `curriculum.toml`'s `kernel_decls` axis after ADR-1130/ADR-1150/
ADR-1155 landed real content, and found the SAME class of bug ADR-1140 had
just fixed, one layer over** (`COMPLETE`, curriculum-spines, 2026-08-31). The
`number-theory` bucket's only Gauss's-lemma alternative was the literal string
`gauss_fold_injective`, written when one declaration of that shape existed. The
29-declaration Gauss's-lemma-for-quadratic-reciprocity family that landed via
ADR-1130 (`Int.gaussLemmaSignCount`) and ADR-1150 (`Int.secondSupplementaryLaw`)
matched none of it — camelCase (`gaussSignNeg`, `gaussFold`, `gaussNegCount`,
...), snake_case (`gauss_neg_count_*`, `gauss_fold_*`, ...), and the
QR-specific names (`secondSupplementaryLaw`, `is_quadratic_residue*`,
`pow_neg_one_of_*`, `half_ceil_parity`, `leastResidue`) all fell through to the
`naturals`/`integers` catch-alls, invisible in the totals. A one-declaration
twin (`Rat.sumRange_matSkip`, ADR-1155's Laplace layer) did the same to
`linear-algebra`. Fixed both bucket patterns by name (deliberately NOT
matching bare `gauss_lemma`, an unrelated divisibility theorem correctly filed
under `divisibility-and-euclid`), re-measured (2,654 distinct declarations,
2,522 attributed, same 132 residual). Six `kernel_decls` values moved:
`propositional-logic` 64→65, `naturals` 516→518, `integers` 193→189,
`rationals` 204→206, `number-theory` 108→137, `linear-algebra` 81→90. All
drift verified BY NAME against the corrected patterns, not inferred from the
totals — the whole reason a second occurrence of this bug was findable at all.
[ADR-1205](../../research/09-decisions/adr-1205-the-bucket-bug-recurred-one-layer-over-the-depth-spine-stays-a-proposal.md).

**Did not apply `DEPTH-PROPOSAL-number-theory-and-linear-algebra.md`'s ~30-node
graph surgery — the third lane to reach this conclusion independently.**
Checked all real consumers (`grep -rl curriculum.toml scripts/ crates/ docs/`,
docs-only prose hits excluded): `graph_dispatcher.py`, `gen-import-backlog.py`,
`validate-foundational-concepts.py`, `check-curriculum-coverage.py`,
`check-graph-dispatcher.py`, `validate-claims.py` all read fields I did not
touch (`status`/`layer`/`area`/`title`/`family`/`prerequisites`/`unlocks`) and
ran clean. `gen-foundational-concepts.py` and `gen-foundational-dashboards.py`
were re-run for real (not grepped) and produced a **zero-byte diff** on both
generated artifacts — `kernel_decls` is read by neither, contrary to what
ADR-1140's consumer table implied. `mathtour.rs`'s `NODES` mirror has no
`kernel_decls` field at all; `cargo test -p axeyum-scenarios --lib mathtour::`
is 6/6 passing, 104.20s, including
`covered_nodes_have_a_family_realized_by_a_self_checking_scenario` (no status
flips were made). N11's frontier narrowed this pass — Gauss's lemma and the
second supplementary law are landed, general reciprocity across two distinct
primes is not — but narrowing a rung's content does not manufacture a `Family`
for it, and no proposed rung (N7′, N9, N11, L3, L9) has one. Landing any as
`covered` would still fail
`covered_nodes_have_a_family_realized_by_a_self_checking_scenario` on sight.
The five-script-plus-Rust-mirror consumer surface is unchanged real work,
separate from a measurement fix.

**Corrected the stale prose the drift exposed**, same pattern as ADR-1140:
`DEPTH-PROPOSAL-number-theory-and-linear-algebra.md` (a correction block, the
N11 table row, the linear-algebra attribution figure — left the ~30-rung
tables' unedited prose as a dated measurement rather than rewriting it, per
ADR-1140's own precedent for the sibling graded-families document),
`03-destinations/number-theory.md` (two new "proved in the kernel" rows, a
corrected "still Lean-horizon" bullet naming the narrower actual gap),
`03-destinations/linear-algebra.md` (a correction paragraph with the new
90-declaration count). `curriculum.toml`'s header measurement block is
re-dated with the mechanism of both bucket fixes and the new
`--expect-attributed 2522` command.

**One unrelated finding, reverted rather than committed**: re-running
`gen-import-backlog.py` produced a large diff (166→194 rows) from OTHER lanes'
fact-ledger landings in the interim, unrelated to curriculum-node content.
Reverted (`git checkout -- artifacts/import-backlog.json`) to keep this lane's
commit scoped to what it actually re-measured; that artifact's regeneration
belongs to whichever lane is tracking the fact ledger, not this one.

**Housekeeping**: `python3 scripts/gen-adr-index.py` run (ADR-1205 registered,
`--check` exits 0, 714 rows, same pre-existing 0166/0167 duplicate as every
prior run); `./scripts/check-links.sh` run and green (see below).

## Next

A fourth lane on this brief should re-run the measurement and check bucket
attribution BY NAME before touching anything else — this is now the second
time doing so found a real, previously invisible bug on a DIFFERENT node than
the one before it, and there is no structural reason to expect the pattern
table has stopped drifting. If a scenario family (`Family::...`) is ever built
for one of N7′/N9/N11/L3/L9, that is the point at which the graph-surgery
question should be revisited — not before, since `covered` without a family
fails the enforced test on sight regardless of how much kernel content backs
the rung.
