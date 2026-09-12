# SMT-LIB `FP` division, before and after the binder sort-alias fix

Lane `binder-alias`, 2026-09-11. This is **not** a `parity-run.sh` head-to-head
and deliberately did not append to `bench-results/PARITY.md`: it scores one
solver against itself across one commit. `scripts/parity-run.sh` has no `FP`
arm in its reference table, so a head-to-head here would fall through to
`/usr/bin/z3` 4.13.3, which did not compete in SMT-COMP 2025 — exactly the
"weaker reference" knob that script's header warns about. Adding an `FP` arm is
a separate decision and was not made here.

## Population

`bench-results/parity-lists/FP.txt`, sha256
`991452febd42927d68076b98c1e0c82ced7075594a09c48ee024145de09cde31`, committed
in `35a912c01` **before** either run. Standard recipe, stride 13 over the
2,669-file division:

```sh
LC_ALL=C find <div> -name '*.smt2' | LC_ALL=C sort | awk 'NR%13==1' | head -200
```

185 of the 200 files carry BOTH a `define-sort` and a quantifier — the shape the
bug killed. 199 of the 200 carry `:status unknown`, so the declared statuses
cross-check almost nothing and the reference run below is what does.

## Protocol

Both arms: `release` `smtcomp_cli`, `--timeout-ms 24000`, `MEM_LIMIT_GB=8`
through `scripts/mem-run.sh`, `timeout 29`. Identical in every respect except
the one commit. Parse rate measured separately with
`crates/axeyum-smtlib/examples/parse_rate.rs`, because `smtcomp_cli` reports a
parse failure as `unknown` — the same word it prints for a reasoned give-up and
a timeout — so a scored run cannot distinguish a division decided badly from one
never read.

| | parsed | decided | sat | unsat | unknown | timeout | other |
|---|---|---|---|---|---|---|---|
| before (`1446a809c`) | 15/200 | 0/200 | 0 | 0 | 200 | 0 | 0 |
| after (`7777570d0`) | 193/200 | 46/200 | 0 | 46 | 154 | 0 | 0 |

The 185 files recovered at parse are exactly the 185 carrying both features. The
7 that still fail are `fp.rem` on the (3,5) format, declined by
`axeyum-fp` as not differentially validated — unrelated to this change.

## Disagreements: zero

Every one of the 46 `unsat` results was re-run against two reference solvers at
a 60 s budget:

* **z3 4.13.3**: `unsat` on 45, undecided on 1. No disagreement.
* **cvc5**: declines all 46 at parse — `"FP term … with type whose size is 3/5
  is not supported, only Float32 (8/24) or Float64 (11/53) … Try
  --fp-exp"`. An explained refusal, not a broken invocation; recorded as a
  non-result rather than as agreement.

The single file declared `:status sat` came back `unknown`, which is not a
disagreement.

## What the 46 are, and what they are not

All 46 are the (3,5) float format. Of the list's 62 `3_5` files we decide 46
(74 %); of its 62 `8_24` and 61 `11_53` files we decide **none**. So this is not
"we now do 23 % of `FP`" — it is "we do most of the smallest format and none of
the two real ones", on the format cvc5 refuses outright. Quote it that way.

## Files

* `before-summary.txt` / `after-summary.txt` — the run summaries, each carrying
  the list sha it scored.
* `before-verdicts.tsv` / `after-verdicts.tsv` — per file: verdict, why-not (a
  reasoned `unknown` vs a `timeout` vs an OOM abort vs a crash, read from the
  exit status — the runner has to notice, instrumentation cannot log through a
  SIGABRT), and path.
* `before-parse-summary.txt` / `after-parse-summary.txt` — `parse_rate` output.
