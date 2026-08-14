# Lean Rado sharpness factorization result

Date: 2026-08-13

Status: **implemented locally; publication and hosted CI recorded separately**

Authority: [requirements](lean-kernel-requirements-2026-08-13.md), R4.6 / R7.1;
[ADR-0396](../research/09-decisions/adr-0396-rado-sharpness-factorization.md).

## Result

The dedicated `rado_sharp_factorization` development checks, with `n=k-3`,

```text
a * (1 + (2 * sumRange (fun i => a^(i+1)) n + a^(n+1)))
  = a + (2 * sumRange (fun i => a^(i+2)) n + a^(n+2)).
```

This is the exact subtraction-free algebra behind the paper's `u=a*u'`
factorization. It uses the generic finite-sum prelude rather than the older
test-local `geo`/`geo1` recurrences and adds no axiom.

Two integration controls pass: the universal theorem covers the empty `n=0`
corner and the nonempty `a=3,n=2` instance reduces to 156 on both sides; a
false `6=4` target formed by dropping the leading right-hand `a` rejects and
is not inserted.

All 213 kernel library tests, every integration suite and doctest, strict
all-target/all-feature Clippy, strict rustdoc, the unchanged 65-row axiom
ledger and eight controls, foundational resources, plan authority, and links
pass locally.

## Boundary

This is a checked dependency of `thm:sharp`, not the theorem. Truncated
subtraction/cancellation, the `N/b` witness connection, range bounds, and the
three colour computations remain. The existing 14-theorem readable export is
unchanged and remains rejected by Lean and unchecked by an independent kernel.
