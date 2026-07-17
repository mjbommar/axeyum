# QF_BV multi-oracle differential fuzz

- Date: 2026-07-17
- Axeyum revision: `8fae61adb04ce9ff735943e93c4c5128ea7e80a6`
- Report SHA-256:
  `fc4f60e4c213fbf416d6780633440dbbd28c379014a00ecf345de60bcee8b3d5`
- Generator: fixed seeds 0 through 3,999, width-correct terms, full scalar
  operator inventory, widths 1/4/8/16/32, depth at most 3
- Primary gate: Axeyum versus direct Z3 on every generated instance
- Neutral gate: every sixteenth instance through cvc5 1.3.4
- Model gate: every Axeyum SAT result replayed against every original IR
  assertion

The commit-bound run decides all 4,000 generated instances in both Axeyum and
Z3 with 4,000 agreements, zero Unknown, timeout, crash, or disagreement. All
1,487 Axeyum SAT models replay on the original terms with no indeterminate
evaluation. cvc5 decides all 250 preselected rows and agrees three ways on all
250; there is no neutral-oracle skip.

Four named controls preserve the Glaurung review history: normalized concat
halves, normalized extension source width, model-less UNSAT versus a legitimate
empty model for a closed SAT formula, and a 128-bit value with bit 100 set. The
W128 control crosses Axeyum's actual linked Z3 adapter and replays its full-width
model. Separate negative controls prove that malformed concat, extension, and
over-wide-constant contracts are rejected before solving.

This split is intentional. Glaurung's concat/extension failures were malformed
consumer metadata, and its empty-model failure was an exploration state-machine
bug; a well-typed formula generator cannot honestly claim to rediscover those
invalid states. The strict negative controls preserve those boundaries, while
the generated lane tests valid formula semantics and model lifting.

The fail-closed neutral runner found one harness defect before this accepted
run: seed 352 rendered disequality as nonstandard `!=`, which cvc5 rejected.
The earlier coarse helper had counted that process/parser failure as a neutral
skip. The renderer now uses SMT-LIB `distinct`, and the helper distinguishes an
explicit cvc5 `unknown` from a parser/process failure; the latter fails with the
complete standalone SMT-LIB reproducer.

Exact counters, resource limits, revisions, and binary hashes are in
[`report.json`](report.json). This is a standing deterministic gate, not a
proof of solver correctness or a replacement for the four-driver trace oracle,
end-to-end finding parity, or proof-coverage measurement.
