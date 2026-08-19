# First bounded source-delta trace

Date: 2026-08-19

## Result

The exact pinned Mathlib `Int.gcd` definition now passes a bounded structural
source trace:

```text
before: Int.gcd
rule:   unfold exactly the selected transparent definition once
after:  the exact stored body containing Nat.gcd
```

The checker consults `Int.gcd` only. It substitutes no universe arguments,
preserves the empty application spine, performs no normalization or recursive
delta step, and leaves `Nat.gcd` opaque. Separately, the proof-free generalized
contract contains neither `Int.gcd` nor `Nat.gcd` as a constant and still
specializes exactly.

The external observation has semantic identity
`3c0d8500917fd4f39058a3603d3358bcdeef4adb9d4b60cd1603bca30e3dfd5c`
and file identity
`41064c4840d7724f97f07235546e09b740e10eccd2ba09dd7110b06dc4695878`.
It is sealed read-only under the content-identified `/nas3` archive. No held-out
row or proof body was inspected.

## What changed from the failed witness

| Evidence path | Source declarations consulted | Theorem closure | Receipt credit |
|---|---:|---:|---:|
| Reflexivity theorem witness | complete transitive closure | 52 | no |
| Selected structural delta step | `Int.gcd` only | not walked | not yet |

This is not a whitelist. The theorem witness remains rejected under ADR-0490.
The trace proves a narrower fact through a different checker: the `after` term
must be exactly the selected definition's stored body after universe
substitution and preservation of the application spine.

## Controls

The reusable checker rejects:

- a theorem or opaque declaration used as the source;
- an input headed by a different constant;
- an output differing from the exact instantiated body; and
- a wrong universe arity.

The exact artifact checker additionally rejects held-out access, a widened
consulted-declaration list, any hidden recursive delta step, or retention of the
generalized source/residual functions in the proof-free template.

## Remaining boundary

The current semantic function-contract receipt requires a theorem-valued source
witness. The trace is therefore eligible evidence but the `Int.gcd` contract is
still not receipt-eligible. The next increment is a trace-backed receipt version
that rechecks the exact source, template, bounded delta step, and specialization
without constructing or admitting a source witness theorem.

## Reproduction

```sh
cargo test -p axeyum-lean-import --test source_delta_trace
cargo test -p axeyum-lean-import --example int_gcd_source_delta_trace
python3 -m unittest scripts.tests.test_check_autogenesis_int_gcd_source_delta
python3 scripts/check-autogenesis-int-gcd-source-delta.py
```
