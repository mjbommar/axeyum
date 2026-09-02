# Retrieval audit for 2026-09-02

Lane `retrieval-audit-0902`, run 2026-09-02. Second of the daily audits
[ADR-0608](../09-decisions/adr-0608-retrieval-is-by-shape-and-absence-is-distinct-from-unanswerable.md)'s
structural remedy calls for. Method is `retrieval-audit-0901`'s, repeated
without change: the wide phrase family over commit subjects **and bodies**,
hand judgment of each candidate by reading the full commit message (diffs
were not separately pulled where the message already quotes the relevant
declarations and search commands), then `scripts/check-shape-duplicates.py
--prebuilt` and `shape_search --duplicates` against a freshly rebuilt
`shape_search` (`scripts/cargo-serialized.sh build --release -p
axeyum-lean-kernel --example shape_search`, 1 m 17 s — no prebuilt binary
existed in this worktree).

**Headline: zero literal duplicates, zero confirmed rederivations. The L0
duplicate gate is green (15 groups, all allowlisted, unchanged from
yesterday's baseline), and it is now wired into `check-merge-hygiene.sh`
with a no-cargo `--prebuilt` route — a same-day structural fix built by lane
`shape-dupes-at-merge` in direct response to yesterday's finding that the
gate sat red for ~25 hours with nobody running it.** Seven candidates from
the phrase sweep, all read in full; every one is either correct reuse, an
absence check performed and passed, or a genuine promotion of a private
helper into a named theorem (the CLAUDE.md remedy for hiding place 2, taken
rather than declined). This is the first clean day since the ledger opened.

## 0. Window

This worktree branched from `origin/main` and then merged local `main`
(landing at `dae09582d`). Commits with a 2026-09-02 committer date, reachable
from `main`:

| | count |
|---|---|
| all refs, 2026-09-02 committer date | 85 |
| local `main`, 2026-09-02 committer date | **81** — matches the brief |
| of those, touching `crates/axeyum-lean-kernel` | **28** |

Fourteen `Agent:` trailers appear in the window: `nat-factorization` (9),
`det-mul-general-n` (8), `nat-multiset` (7), `det-mul-2` (6),
`retrieval-audit-0901` (5), `eisenstein-lattice` (5), `eisenstein-2` (5),
`shape-census` (4), `testbit-codomain` (3), `shape-dupes-at-merge` (3),
`ownership-invokers` (3), `obstruction-producers-red` (3),
`nursery-draw-19` (2), `coordinator` (1) — matching the brief's eight named
lanes plus "the gate lanes" (`shape-dupes-at-merge`, `ownership-invokers`,
`obstruction-producers-red`, `nursery-draw-19`).

**A methodological note the previous audit did not have to make: three of
the 28 kernel-path commits (`feee209c6`, `690b3e199`, `a766acdce`) and one
more (`b4fb008d8`) are `retrieval-audit-0901`'s OWN landed work** — that lane
ran on 2026-09-02 (auditing 2026-09-01) and its commits, including the
literal-duplicate dedupe it performed, carry today's committer date. These
are **excluded from today's candidate judgment** below: `b4fb008d8` is the
SAME commit already read and reported in
[2026-09-02-retrieval-audit-for-2026-09-01.md](2026-09-02-retrieval-audit-for-2026-09-01.md)
§2.1, not a new finding, and the other three are that audit's status/docs
commits with no code content to judge. Counting them here would double-count
yesterday's dedupe as today's.

## 1. Candidates (7, after excluding yesterday's audit's own 4 commits)

Same phrase family as `retrieval-audit-0901`: (`already exist`,
`already prov`, `already had`, `already covers`, `not new`,
`instead of re-deriv`, `duplicate`) plus (`turns out`, `rederiv`,
`re-deriv`, `found .* existing`, `promote`, `hoist`, `unexpose`) plus
`was already` / `is already` / `were already`, `redundan`, `dedup`,
`no need to`, `did not need`, `unnecessary`, `verbatim`, `same proposition`,
`two proofs`, `second proof`, `existing (lemma|declaration|theorem|helper)`
— matched over subject and body, case-insensitive.

Over the 28 kernel-path commits: **8 raw matches, 7 after excluding
`b4fb008d8`** (yesterday's dedupe, above). Over all 81 commits: 24 raw
matches — the same "judge the kernel-path set, use the wider count only for
context" split as yesterday.

| # | commit | subject | matched | verdict |
|---|---|---|---|---|
| 1 | `4b4680234` | the count laws, and four general lemmas the uniqueness proof needs | `already had` | **no** — "`Nat.valuationAt` ... this prelude already had, with no uniqueness lemma"; the new declaration is the uniqueness lemma, not a re-derivation of `valuationAt` |
| 2 | `4b4e90490` | `sumRange_permute`, the additive half of Gauss's bijection | `already exist` | **no** — "Gauss's lemma already runs that bijection MULTIPLICATIVELY (`Int.prodRange_permute`); nothing ran it additively" — an explicit twin check, see §3 |
| 3 | `68f452c23` | `Rat.prodRange` and `Rat.sumMaps`, the two aggregates obligation 1 needs | `already exist` | **no** — absence measured with `shape_search --name-like` against a fresh 2,048-declaration index BEFORE building, `Int.sumMaps`/`Int.prodRange`/`Rat.sumRange` as positive controls in the same run |
| 4 | `7daa70b27` | the additive Gauss bijection, instantiated (ADR-1540 residue 1) | `not new`, `verbatim` | **no** — "Assembly, not new mathematics: the same three steps `int_prelude/gauss_assembly.rs` already runs MULTIPLICATIVELY ... with `Nat.sumRange_permute` in place of the product" — deliberate reuse of #2's result |
| 5 | `94373af8a` | the SELECTION lemma, whole — ADR-1440 obligation 2 closed | `already exist`, `duplicate` | **no** — the near-miss avoided, see §3 (`Nat.lnp_bounded_search`) |
| 6 | `dedab9764` | the transposition's pointwise facts as kernel THEOREMS | `existing helper` | **no** — a promotion, see §3 |
| 7 | `fa87f0320` | the selection lemma's INJECTIVE half, at symbolic n | `duplicate` | **no** — "the free non-injective half (`Rat.det_row_selection_of_duplicate`)"; reuses `Nat.transposition_injective`, the theorem #6 promoted |

**Every candidate today reads as correct retrieval, not a miss.** That is
itself the finding worth stating plainly: on 2026-08-25..27 and again on
2026-09-01, this method found real rederivations in every window it was run
against; today it found none. One day is not a trend, and the gate having
just been wired into the merge path (§4) may be doing real work already —
lanes that would have rederived silently instead read the phrase family's
own vocabulary back at the auditor because they had already done the check.

## 2. Confirmed (0) / literal duplicates (0)

**No dedupe commit was made.** `scripts/check-shape-duplicates.py
--prebuilt` against the freshly built binary:

    OK: 15 duplicate group(s), all allowlisted with a reason. (route: prebuilt)

Unchanged from yesterday's post-dedupe baseline (15 groups). Direct
`shape_search --include-constructed --duplicates` confirms the same 15
groups, byte-identical to the allowlist, with
`coverage: groups=[logic,nat,axreal,integer,ipc,rat,characterization,string,creal,complex,cpoint]
declarations=2964` (up from yesterday's 2,875 — 89 new declarations across
the day's eleven lanes, none of them a duplicate group by shape).

`kernel_declaration_projection`: **15,269** rows (up from yesterday's
post-dedupe 14,665). No dedupe means no before/after diff to show for a
deleted pair; this number is the baseline for tomorrow's audit.

## 3. Near-misses (the day's good retrieval outcomes, not counted as findings)

* **`94373af8a` (det-mul-general-n) avoided rebuilding a pigeonhole search.**
  ADR-1470 had recorded `Nat.injective_on_or_duplicate`'s decision procedure
  as "genuinely new, general-purpose infrastructure" after grepping
  `pigeonhole` / `exists_dup` / `not_injective`. The lane instead found
  `Nat.lnp_bounded_search` (`least_number.rs`) — a bounded search for a
  pointwise-decided predicate is exactly "search `[0,n)` for a collision"
  once you see it as such — and built the selection lemma from two nested
  instances of it rather than a new search primitive. Hiding place 1: filed
  under the least-number principle, not under anything a
  pigeonhole/injectivity search would guess.

* **`dedab9764` (det-mul-general-n) is the hiding-place-2 remedy taken
  rather than declined.** ADR-1470 had recorded that `nat_prelude`'s five
  pointwise transposition facts could not be reused from `rat_prelude`
  because they are Rust helpers over `&mut NatDev<'_>` and the consumer runs
  on `IntDev` — the same carrier-typed-helper wall
  `finding-existing-lemmas.md` names. Rather than building a second private
  swap (the designed-but-not-built alternative from yesterday's §2.2 near
  miss), the lane declared the three reusable facts as `Nat.transposition_*`
  THEOREMS at a bare `NameId`, which nothing about the carrier restricts.
  `fa87f0320` then consumed `Nat.transposition_injective` directly. This is
  the promotion CLAUDE.md's hiding-place-2 entry recommends and
  `cfb7014dc` (yesterday's §3) took only half of — here it was taken whole,
  and the very next commit used it.

* **`4b4e90490` / `7daa70b27` (eisenstein-lattice / eisenstein-2) is a
  correctly-executed instance of hiding place 6** (the design review's "same
  argument over a different aggregate in a different prelude"): the
  multiplicative bijection (`Int.prodRange_permute`,
  `gauss_assembly.rs`) was recognised as the skeleton to reuse
  additively over `Nat.sumRange`, built once (`Nat.sumRange_permute`), and
  then the SAME assembly module was reused verbatim with the new lemma
  substituted for the old one — exactly the "ask which other aggregates this
  development folds over, and in which other preludes" discipline
  `finding-existing-lemmas.md` §6 asks for, executed without the file being
  quoted at the lane.

* **`68f452c23` (det-mul-2) ran the absence check as a command, not a
  memory**: `shape_search --name-like Rat.sumMaps` / `--name-like
  Rat.prodRange` against a fresh index, with `Int.sumMaps` (FOUND 5) as a
  same-kind positive control in the same run before declaring anything
  absent. It also found and used `Rat.mul_sumRange` — an existing lemma
  with the LEFT pull in the opposite direction — and built a new one only
  because the direction did not compose with the induction, not because it
  missed the existing one.

## 4. The structural fix that landed today

`63f887b89` (`shape-dupes-at-merge`) gave `check-shape-duplicates.py` a
`--prebuilt` route (no `cargo`, reads `target/release/examples/shape_search`
directly) and wired it into `scripts/check-merge-hygiene.sh` as point 7,
defaulting ON — directly in response to yesterday's finding that the gate
had been red on `main` for ~25 hours because it needed the ~10-minute
`cargo run --release` route and so lived only in the full gate. Measured
cost on `s4`: 60.9 s / 70.0 s unpinned, 41.7 s pinned (`taskset -c 0-7`) — an
order of magnitude over the merge-hygiene baseline, so it carries a
documented `AXEYUM_SKIP_SHAPE_DUPLICATES=1` escape that the summary line
reports when used, and a staleness check (`fact-frontier.py`'s
`kernel_projection_is_stale`, imported not copied) so an absent-or-stale
binary answers `SHAPE-DUPLICATES|UNAVAILABLE`, never a false pass.
`c0b82cf766` is the ADR-1511 amendment recording this cost and why the gate
still defaults ON. This lane's own `--prebuilt` run above used exactly this
route and confirms it: 15 groups, exit 0.

This is the daily-audit process working as ADR-0608 intended — not just
finding yesterday's duplicate, but producing a same-day fix that changes
whether tomorrow's audit can find a live red gate at all.

## 5. The `Int`/`Nat`/`Rat` twin check (deliverable-specific)

Independently of what the lanes' own commit messages claimed, every new
declaration under `Nat.prodRange_*`, `Rat.prodRange_*`, `Rat.sumMaps_*`,
`Nat.sumRange_*` was checked against `shape_search --include-constructed
--name-like` for its likely twin:

| family | this prelude | `Int` twin | note |
|---|---|---|---|
| `Nat.prodRange_*` | 11 (no `_permute`) | `Int.prodRange_*` 23 (has `_permute`, `_swap`, `_swap_adjacent`) | no new `Nat.prodRange_*` landed today; unchanged |
| `Rat.prodRange_*` | 5 | `Int.prodRange_*` 23 | ported in shape from `int_prelude/prod.rs`, per commit; no shape-level duplicate reported |
| `Rat.sumMaps_*` | 7 (has `_mul_right`) | `Int.sumMaps_*` 5 (no `_mul_right`) | the extra `Rat.sumMaps_mul_right` is confirmed genuinely new — `Int.sumMaps` has no `_mul_right`, matching the commit's own claim that it "has no `Int` counterpart" |
| `Nat.sumRange_*` | 15 (has `_permute`, `_point_change`) | `Int.sumRange_permute` — **ABSENT** | `Nat.sumRange_permute` has no `Int`-side twin at all (the multiplicative analogue lives at `Int.prodRange_permute`, a different aggregate, not a duplicate by shape) |

**No duplicate found in this family.** `shape_search --duplicates` (§2) is
the authoritative check and reports zero new groups touching any of these
names; the per-family `--name-like` counts above are corroborating detail,
not a separate verdict. The near-misses in §3 are exactly this check,
already performed by the lanes before landing — this section repeats it
independently rather than trusting the self-report, and gets the same
answer.

## 6. Tool usage on the day

Status docs touched by today's window commits (deduplicated across a rename,
`ownership-invokers.md` → `404-ownership-invokers.md`): **14**.

| population | denominator | `shape_search` | `brief-step0` / `just brief` |
|---|---|---|---|
| commit messages, kernel-path, 2026-09-02 | 28 | 0 (0.0%) | 0 |
| commit messages, all paths, 2026-09-02 | 81 | 0 | 0 |
| lane status docs touched on 2026-09-02 | 14 | **7 (50.0%)** | **3 (21.4%)** |
| lane status docs, all time (reference, 2026-08-31 measurement) | 429 | 30 (7.0%) | 10 (2.3%) |

**The 50%/21.4% figures are not directly comparable to yesterday's
7.4%/0%** and should not be quoted as a six-fold jump without the
composition: of the 14 docs, 2 (`retrieval-audit-0901.md`,
`shape-dupes-at-merge.md`) are ABOUT the retrieval tooling itself, not a
lane using it to check its own work, and would mention `shape_search` by
subject regardless of discipline. Excluding those two: **5 of 12 (41.7%)**
working-lane docs mention `shape_search`
(`det-mul-2`, `eisenstein-2`, `nat-factorization`, `nursery-draw-19`,
`testbit-codomain`), and **1 of 12 (8.3%)** mentions `brief-step0`
(`testbit-codomain`; `shape-census` also mentions `just brief` but its own
subject is the census tool, similar caveat). Even on the conservative
reading, both rates are well above yesterday's 7.4%/0% and above the
all-time reference rate (7.0%/2.3%) — the first day this ledger can report
that. One day is not a trend; report it as a data point, not a claim that
the rate has permanently moved.

## 7. Verification run in this lane

- `scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel --example shape_search` — 1 m 17 s, no prior binary.
- `python3 scripts/check-shape-duplicates.py --prebuilt` — exit 0, 15 groups.
- `scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel --example kernel_declaration_projection`, run — 15,269 rows.
- `scripts/check-source-freshness.sh --gate test --touch` — no prior manifest for this target dir, touched all 12,657 build inputs (one full rebuild, once, for this worktree).
- `scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel --lib -- nat_prelude:: --test-threads=4` — **365 passed, 0 failed**.
- `scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel --lib -- rat_prelude:: --test-threads=4` — **169 passed, 0 failed**, 179.48 s.
- `scripts/cargo-serialized.sh clippy -p axeyum-lean-kernel --all-targets --all-features -- -D warnings` — clean.
- `python3 scripts/validate-facts.py` — exit 0, 2,606 facts checked, 0 errors, 2,373 settled.
- No declaration was deleted, so `crates/axeyum-py/src/kernel/prelude_fields.rs` was not regenerated.
- No dedupe commit was needed, so no consumer/fact repoint and no projection before/after diff for a deleted pair — §2's row count is a baseline, not a delta.

## 8. Baseline for tomorrow

* Duplicate groups: **15**, unchanged, all allowlisted
  (`scripts/shape-duplicates-allowlist.json`).
* `shape_search --include-constructed`: **2,964** declarations across
  `[logic, nat, axreal, integer, ipc, rat, characterization, string, creal,
  complex, cpoint]`, index build 35.9 s in `--release`.
* `kernel_declaration_projection`: **15,269** rows.
* Ledger: 2,606 facts checked, 0 errors, 2,373 settled
  (`validate-facts.py` exit 0).
* The L0 duplicate gate now runs in `check-merge-hygiene.sh` (point 7,
  `--prebuilt`, defaulting ON) — **check its colour in that gate's own
  output first**, before running anything else. If a merge already ran it
  today, tomorrow's audit inherits a live answer instead of a 25-hour-old
  unknown.

One thing to do differently next time: this lane spent real effort
disentangling `retrieval-audit-0901`'s own commits (dated today because that
lane ran today) from today's actual candidate set. **Whoever writes
tomorrow's brief should state the previous day's audit lane's commit SHAs
explicitly as excluded**, rather than leaving the next lane to discover the
overlap by reading `Agent:` trailers.
