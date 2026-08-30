# Lane: int-build-time — the `int_prelude` regression is a filter artifact; the cost is `CReal`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, int-build-time, 2026-08-28). The flagged regression
is NOT in the Int prelude and NOT caused by `bezout_witnesses`.** The reported
`cargo test -p axeyum-lean-kernel --lib int_prelude` going 8.65 s -> 148.28 s is
real as a wall-clock fact about that command, and the cause is entirely outside
`int_prelude/`.

`int_prelude` is a **substring** filter, and
`creal_point::creal_point_tests::cpoint_prelude_builds` matches it —
`cpo` + `int_prelude` + `_builds`. That one test is the whole cost. Measured
with `--report-time --test-threads=1` on the prebuilt
`target/debug/deps/` binary (no cargo lock), `RUST_MIN_STACK` confirmed unset:

| tree | `cpoint_prelude_builds` | all 34/37 `int_prelude::` tests |
| --- | --- | --- |
| `77b71bf10` (08-26, the 34-match "before" tree) | 54.70 s | ~3.0 s |
| `e94d8d080` (parent of the first Bézout commit) | 160.08 s | 3.82 s (34 tests) |
| HEAD (`335da8ba5` + Bézout) | 148.55 s | **4.11 s (37 tests)** |

**The Bézout work costs +0.29 s.** Parent 34 tests / 3.82 s -> HEAD 37 tests /
4.11 s, filtering `int_prelude::` (with the colons, which excludes the
`creal_point` test). Serialized per-test: the two evaluation tests are 0.136 s
and 0.070 s, and the new namespace-inventory test is 0.179 s. **Every one of the
37 `int_prelude::` tests is under 0.72 s.** Nothing in `bezout_witnesses.rs`
approaches the magnitudes that trip the unary-numeral cost documented in
`CLAUDE.md`; the largest `Nat` formed anywhere in the two evaluation tests is 6.

**Where the time actually went, bisected by prelude layer at HEAD:**

- `creal::creal_tests::creal_prelude_builds` — **12.19 s (08-26) -> 108.40 s
  (HEAD)**, an 8.9x growth in two days.
- `cpoint_prelude_builds` is that 108 s plus ~40 s of CPoint layer. The CPoint
  layer itself is flat (42.5 s -> 40.1 s); **all** the growth is in `CReal`.

So the thing to watch is the `CReal` prelude build, which is already a tracked
cost with its own retrospective in `CLAUDE.md` (18.7 s -> 92.6 s from one
declaration, fixed back to 18.4 s). It is now at 108 s again, and no single
`int_prelude` change is involved.

Detail moved to [`../notes/214-int-build-time.md`](../notes/214-int-build-time.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | int-build-time | measured: the flagged `int_prelude` regression is `cpoint_prelude_builds` caught by substring; Bézout costs +0.29 s, `CReal` prelude build went 12.2 s -> 108.4 s in two days |
