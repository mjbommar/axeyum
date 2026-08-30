# Notes: 214-int-build-time

Detail moved out of [`../status/214-int-build-time.md`](../status/214-int-build-time.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The evaluation tests are non-vacuous, verified by mutation.** Changing the
`(-3, 2)` row's expected `gcdA` from `-1` to `1` in
`int_gcd_ab_compute_in_every_sign_branch` kills **exactly one** test
(36 passed, 1 failed) and no other. The tests were left unchanged — they cost
0.21 s combined and are the only thing that pins the algorithm rather than the
identity.

**Method note for whoever measures next.** Use `int_prelude::` with the colons.
The bare `int_prelude` filter silently drags in a `creal_point` test that costs
36x the entire Int prelude suite, and the test count (35 vs 34, 38 vs 37) is the
only visible tell.
