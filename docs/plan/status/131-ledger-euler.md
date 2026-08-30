# Lane: ledger-euler — register Spivak Ch.18/22-23 `e` and series facts; direct Definition checker

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, ledger-euler, 2026-08-27).** `CReal.e` had NO
fact, nor did `two_le_e`, `e_le_three`, or `e_le_four` — a real negative,
confirmed by `/usr/bin/grep -rl` across `artifacts/facts/` against a control
that found 180 `CReal` facts. Euler's number was constructed in this kernel
and entirely unrecorded in the product.

**Task 1 — the sibling lane's claimed blocker was real, and it is now
closed.** Eight examples do mention `Declaration::Definition`
(`kernel_declaration_projection.rs` among them), but none took a name and
asserted a `Definition` exists with a non-zero exit on absence —
`theorem_dependency_inventory` / `nat_theorem_inventory` /
`prelude_theorem_inventory` all filter to `Declaration::Theorem` by explicit,
documented contract. Added `--require-declaration <name> [--require-kind
<kind>]` to `kernel_declaration_projection`: it searches every constructed
prelude's environment for an exact display-name match (of the given kind,
when given) and exits non-zero when none is found; unfiltered invocations
(no new flags) are byte-identical to the prior behaviour (verified: 7,278
unfiltered rows, unchanged TSV shape — this is what
`gen-autogenesis-kernel-dependency-projection.py` still consumes).

Detail moved to [`../notes/131-ledger-euler.md`](../notes/131-ledger-euler.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | (uncommitted at status-file write time) | Added `--require-declaration <name> [--require-kind <kind>]` to `crates/axeyum-lean-kernel/examples/kernel_declaration_projection.rs`: a direct, fail-on-absence presence checker for `Declaration::Definition`s (and any other kind), mutation-tested against `CReal.integral`. Upgraded `F:creal-integral`'s `kernel-CReal.integral` evidence to use it. Registered 14 new `artifacts/facts/F-creal-*.json` entries for Spivak Ch.18 (`e`) and Ch.22-23 (series convergence tests): `creal-e`, `creal-e-converges`, `creal-two-le-e`, `creal-e-le-three`, `creal-e-le-four`, `creal-expterm-le-geom`, `creal-expdominantcauchy`, `creal-cauchyofpointwiseequiv`, `creal-geomcauchy`, `creal-sumrange-comparisontest`, `creal-sumrange-cauchy-of-dominated`, `creal-sumrange-converges-of-dominated`, `creal-sumrange-cauchy-of-abs-cauchy`, `creal-sumrange-converges-of-abs-converges`. `python3 scripts/validate-facts.py` green (722 facts, 0 errors). |
