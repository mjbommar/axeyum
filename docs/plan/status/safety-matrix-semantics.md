# Lane: safety-matrix-semantics

**Status:** ACTIVE — auditing what each of S0's nine safety-matrix columns
actually measures, against every centrally-run gate that provides the same
protection by another route.

## Why

`artifacts/safety-matrix/safety-matrix.tsv` is the S0 census that the whole
L0 trusted-library programme is graded against. Its `circularity` column reads
38 / 2,117 while `scripts/check-trust-closure.py` enforces the same protection
centrally over 1,956 of 2,041 kernel-route facts on every merge. Both numbers
are right about their own question; the column NAME fits neither. The census
measures *per-fact evidence* (a regex over each fact's own `checker_command`
strings) and is being read as *coverage*.

## Landed changes

_(none yet — audit in progress)_

## Notes

Conclusions land in ADR-0795.
