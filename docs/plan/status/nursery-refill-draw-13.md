# nursery-refill-draw-13

<!-- plan-section: lane-status -->

**Status: DECLINED.** Decision record:
[ADR-1075](../../research/09-decisions/adr-1075-draw-13-is-declined-two-constructions-are-not-four-families.md).

Dispatched against ADR-1060 (both of draw 12's named unblocks --
`Nat.avg`/`Nat.pair` and `Max.max`/`Min.min`/`Nat.instMax`/`instMinNat` --
built, construction-only). `check-dispatchable-frontier.py` reads 4
dispatchable against the floor of 10, unchanged from the brief.

Refreshed the environment snapshot (2572 -> 2583 declarations via a fresh
`shape_search --release` build -- eleven more lanes landed since ADR-1060)
and re-ran the real `select()`/`guard()`/`screen_family` against both named
families, exactly as a draw would. Both reproduce ADR-1060's own
post-declaration screen on a larger tree: `natural-avg-pair` 10 candidates,
R9 0/10, R11 clean (one advisory `avg` self-hit, non-blocking); `natural-
minmax` 10 candidates, R9 0/10, R11 fully clean.

**Both are genuinely held-out-safe, and the draw is still refused --
by R5, mechanically, not by contamination.** `assign_partitions`'s cycle
(`held-out, development, train`, restarting per draw over the fresh family
set sorted by first module name) puts held-out only at indices `i % 3 == 0`.
With exactly 2 fresh families that is index 0 alone -- confirmed empirically,
not just by reading the code: `guard()` reports `R5 the refill adds 1 held-
out families; the blind population is already down to two capabilities`.
Reaching R5's 2-held-out minimum needs `ceil(n/3) >= 2`, i.e. at least 4
fresh families -- which is also why draw 11 (ADR-0925) registered exactly
4 and draw 9 (ADR-0830) needed two below-floor combinations.

**Searched for 2 more viable families to reach n=4; found at most 1.**
`propose-nursery-refill.py --remeasure` gives the complete list of un-owned
modules with >= 10 HYGIENE-screened survivors (its own exhaustive sweep over
85 modules-with-survivors): `Mathlib.Data.Nat.Log` (37), `Mathlib.Data.Nat.
Fib.Basic` (22), `Mathlib.Data.Int.Fib.Basic` (21), `Mathlib.Data.Nat.
Bitwise` (18). None is independently viable against the REAL `select()`,
which additionally excludes anything already drawn into nursery-v1's own
catalog -- and v1 already owns `natural-logarithm`, `natural-fibonacci`,
`integer-fibonacci`, `natural-bitwise` as its own train/dev/held-out
families, so most of each module's rows are already spent. Measured real
pools: Log 0, Nat.Fib.Basic 8, Int.Fib.Basic 6, Bitwise 6 -- all under the
10-row floor individually. Combining any two of the three non-Log modules
into one family reaches exactly 10 (three ways checked: natfib+intfib,
natfib+bitwise, intfib+bitwise), but that consumes the only real content
in the set -- no second, disjoint combination also reaches 10 (Log
contributes ~0 everywhere it appears). So at most ONE additional family is
constructible, for 3 fresh families total, not 4. Verified directly: with
avg-pair + minmax + a combined Fib+Bitwise filler, `guard()` still reports
`R5 the refill adds 1 held-out families` (avg-pair -> held-out, minmax ->
development, the filler -> train, by the same alphabetical-sort cycle).

**Declined.** No held-out-safe, floor-clearing draw exists in the currently
reachable statement space; the elementary-number-theory territory this
generator can express is now claimed or exhausted across thirteen draws'
worth of attempts, reproducing and sharpening ADR-0900/ADR-1045's finding.

Kept: the environment snapshot refresh to 2583 (accurate state for the next
lane). One documented, harmless side effect: `Max.max`/`Min.min` becoming
admissible also makes two rows of the ALREADY-PREREGISTERED `train` family
`natural-basic-arithmetic` newly admissible, displacing two already-`proved`
facts from that family's PER_FAMILY=10 window (their fact files are
untouched on disk, still valid and `proved`, just no longer named in the
manifest's `entries`). No held-out or development row is touched; held-out
count is 146 before and after (`check-autogenesis-holdout-isolation.py`).
Reverted: the `FAMILY_MODULES`/`FAMILY_ROUTES` edit (it cannot pass `guard()`
as authored, so it does not belong in the tree).

**Next draw needs:** a genuinely NEW held-out-safe construction (a fourth
family, or a bigger single one) -- not a bigger search over the CURRENT
un-owned-module space, which is now measured exhausted at the `>= 10 hygiene
survivors` bar. `propose-nursery-refill.py`'s ready list (4 modules) is the
complete candidate space and none of the 4 is independently viable.
