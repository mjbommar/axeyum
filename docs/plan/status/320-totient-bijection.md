# Lane: totient-mul — two more pieces toward `Nat.totient_mul_of_coprime`, the bijection route still not attempted

<!-- plan-section: lane-status -->

**DONE for this dispatch (`totient-mul`, 2026-08-30).** Landed two small,
fully-verified building blocks from `docs/plan/status/301-totient-
multiplicative.md`'s plan. Did NOT attempt `Nat.totient_mul_of_coprime`
itself, and did NOT attempt the CRT-bijection route `316-queue-sweep.md`
identified as the correct fix for `301`'s false `count_range_row_major`
claim — that remains the real remaining work, sized by `316` as several
more dispatches, and nothing in this session's budget changes that sizing.

## What already existed (did not need to build)

Before writing any code, ran `shape_search --include-constructed
--name-like coprime` (fresh build, `declarations=2301`) and `--name-like
gcd_mod`/`gcd_succ`. Confirmed landed by prior lanes and reused directly:

Detail moved to [`../notes/320-totient-bijection.md`](../notes/320-totient-bijection.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | totient-mul | `Nat.gcd_mod_left_eq_gcd` and `Nat.coprime_mul_iff` (both new, axiom-free, `301`'s Steps 1 and 3 toward `totient_mul_of_coprime`) landed and verified in a new file `nat_prelude/totient_mul_coprime.rs`. Did not attempt `totient_mul_of_coprime` itself or the CRT-bijection route `316-queue-sweep.md` correctly identified as replacing `301`'s false `count_range_row_major` claim — sized as several more dispatches (a new "`countRange` invariant under a domain bijection" primitive is the largest missing piece, on top of the already-existing `nat_prelude/crt.rs` self-map). |
