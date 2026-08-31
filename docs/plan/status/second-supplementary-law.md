# Lane: second-supplementary-law

**Status:** in progress (started 2026-08-31)

## Target

The second supplementary law of quadratic reciprocity, over
`Int.gaussLemmaSignCount` (ADR-1130) and `Nat.gaussNegCountTwoClosedForm`.

## Parity table (verified, re-runnable)

```sh
python3 -c "
import collections
agg=collections.defaultdict(set)
for m in range(0,200):
    p=2*m+1; N=m-(m//2)
    agg[m%4].add((p%8, N%2))
for k in sorted(agg): print(k, sorted(agg[k]))
"
# 0 [(1, 0)]   1 [(3, 1)]   2 [(5, 1)]   3 [(7, 0)]
```

## Route

`N = m - div m 2`. Writing `m = 2*j + s` (`s in {0,1}`) gives `div m 2 = j`
and `N = j + s`; splitting `j = 2*i + t` again gives `N = 2*i + t + s`, so the
parity of `N` is the parity of `t + s`. A DOUBLE even/odd split, not mod-4
arithmetic.
