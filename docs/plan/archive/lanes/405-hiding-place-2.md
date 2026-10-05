# Lane: hiding-place-2 — the inline proof steps no shape index can see, measured and unified

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, hiding-place-2, 2026-09-02).** The retrieval audit
(`docs/research/11-design-review/2026-09-02-retrieval-audit-for-2026-09-01.md`)
counted hiding place 2 by hand. This lane built the instrument that count
should have come from, then removed the four families it named.

**The instrument.** `scripts/private-helper-census.py` groups private `fn`
items in `crates/axeyum-lean-kernel/src/` by name AND by normalized body
(receiver name and carrier type normalized; comments dropped; **string
literals kept**, because masking them merges every `declare_theorem` script in
the crate into one group). `--check` exits 1 on a stale or missing artifact,
and eight controls in `scripts/tests/test_private_helper_census.py` prove it
can go red — including the negative the normalizer needs (a different proof
step must give a different digest) and the `<'_>`-is-not-a-char-literal case,
whose failure mode is silently blanking the rest of every file. Registered as
the third `GUARDED` entry in `check-generated-artifact-ownership.py`, which
that gate's own COVER note asked for: CTRL now rejects a planted second writer
over three producer sets instead of one.

**What the census found that the hand count could not.** Grouping by body is
blind to the name, so it unites `dvd_elim` (`nat_prelude`, `&mut NatDev`) with
`dvd_elim_nat` and `nat_dvd_elim` (`int_prelude`, `&mut IntDev`) — one group
of 12 that no name search joins. And the four named families are **not the
largest**: `cmul` 22, `czero`/`rzero` 22, `cneg`/`lneg` 22, `echain` 21,
`csymm`/`esymm` 13, `ex_falso`/`from_false` 13 — all `IntDev`, all still
standing. That is the next lane's queue, and it is bigger than what was named.

**What was removed.** 50 private items became 4 `pub(crate)` generic helpers in
`nat_prelude/steps.rs`: `dvd_elim` 15 copies, `absurd` 14, `dvd_intro` 11,
`or_cases` 10; 186 call sites dropped the now-redundant `&NatPrelude`
argument. Census moves 9,076 → 9,030 private fns, 370 → 364 duplicated body
groups, 1,402 → 1,357 sites in them.

**The genericity question is answered and needs no ADR.** One `NatOps` bound
covers both carriers, because `IntDev`'s `Int`-carrier operations are all
`i`-prefixed and its `impl NatOps` supplies only `kernel` and `nat_state` — so
`mul`, `eq`, `dvd`, `dvd_predicate` on an `IntDev` already ARE the
`Nat`-carrier trait defaults. Checked explicitly: none of the twelve methods
these helpers call is shadowed by an inherent method on any implementor, which
is the trap that makes `NatOps::congr` and `IntDev::irefl` carrier-specific.

**The invariant, and why the zero is evidence.**
`kernel_declaration_projection` (15,269 rows) diffed 0 lines after each of the
four families and again at the final commit. A zero diff proves nothing unless
the projection can move, so one was planted: `False.rec` at level 1 instead of
0 in the shared `absurd`. The Nat prelude then fails to build —
`TypeMismatch { expected: ExprId(2), got: ExprId(0) }` — the binary exits 101
and the diff is 15,191 lines. Reverted, rebuilt, re-diffed at 0.

**Gates.** `nat_prelude::` 365 passed, `int_prelude::` 74 passed, whole kernel
lib 1,378 passed in 391 s, all nonzero. Clippy clean on the crate,
`--all-targets --all-features -- -D warnings`.

**A sized negative on the build time.** No regression, and the measurement
cannot say more. Nat cold build was 754 ms before and 692 / 1,595 / 677 /
731 ms across four runs after, on a box whose load average moved 11 → 5 during
the work. The spread is 2.4x; a change smaller than that is not resolvable
from this host and this lane did not try to claim one.

**One thing to know for a bisect.** 357bccd93 and 98dfb5aef are ONE change
split in two because the path list handed to `lane-commit.sh` was truncated at
22 of 44 paths. 357bccd93 alone does not compile.

<!-- plan-section: landed-changes -->

| 2026-09-02 | hiding-place-2 | `scripts/private-helper-census.py` + controls + ownership-gate entry; 9,076 private fns, 370 duplicated body groups measured (43b16059f) |
| 2026-09-02 | hiding-place-2 | 50 private copies of `dvd_elim`/`absurd`/`dvd_intro`/`or_cases` unified into 4 `NatOps`-generic helpers; projection 0-line diff, mutant control at 15,191 (357bccd93 + 98dfb5aef, one change) |
