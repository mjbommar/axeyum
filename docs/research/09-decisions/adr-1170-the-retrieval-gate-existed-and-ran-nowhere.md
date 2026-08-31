# ADR-1170: The retrieval gate existed and ran nowhere

Status: accepted
Date: 2026-08-31
Index-summary: Retrieval was identified as the binding gate on marginal cost
per theorem, and the diagnosis of *why* it stayed open was structural:
mutation testing has a harness and a registration gate and is followed 42% of
the time; `shape_search` had prose and is followed 7.0%. This ADR does not
build a third tool. Both halves already existed and neither was reachable:
`scripts/brief-step0.py` (`just brief`) is the harness and is named nowhere in
CLAUDE.md's retrieval section, and `scripts/check-shape-duplicates.py` is the
gate — complete, bidirectional, unit-tested — **named by no gate at all**,
because `check.sh` registered only its unit tests. Its first automatic run
reported five unadjudicated duplicate groups accumulated in the four days
since the last hand run; four were deliberate Mathlib-name aliases and one was
a genuine independent re-derivation (`Rat.int_right_distrib` re-proving
`Int.add_mul`), now forwarding to a single proof term. The checker is wired
into `local-ci.sh`, `ci.yml` and `check.sh` and added to `L0_GATES` so it
cannot drift back out. Break/restore proven both directions through the real
`cargo run` path. What the gate does **not** cover is stated explicitly: an
inline step inside a larger declaration has no type to compare, so no
type-based or name-based tool can ever see it re-derived.
Index-status: accepted

## Context

`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md` names
three gates on marginal cost per theorem — contracts, retrieval, sharding —
and identifies retrieval as the binding one. CLAUDE.md's *"THE LEMMA YOU NEED
USUALLY EXISTS"* section documents thirteen-plus recorded instances of a lane
re-deriving something already in the tree, and says in bold that **prose has
not fixed this and the count kept climbing after the section was written.**

ADR-1165 re-measured adoption over 272 lane status documents: mutation testing
46%, `shape_search` 4.8%. Re-measured here over the current **429** documents
in `docs/plan/status/`, with `/usr/bin/grep -l` (GNU grep, not the interactive
`ugrep` wrapper) and a positive control in the same sweep:

| pattern | files | share of 429 |
| --- | --- | --- |
| `shape_search` (fixed string, `grep -lF`) | 30 | **7.0%** |
| `mutation` or `mutant` (`grep -lE`) | 180 | **42.0%** |
| `brief-step0` (fixed string, `grep -lF`) | 10 | **2.3%** |
| `cargo` — positive control (`grep -lF`) | 238 | 55.5% |

The denominators differ from ADR-1165's (429 vs 272 documents) and the ratio
does not: retrieval tooling is referenced roughly one-sixth as often as
mutation testing. The control rules out a broken query.

The structural difference between the two practices is the whole finding.
Mutation testing has **both** a harness (`scripts/tests/mutation_controls.py`,
4 references in `check.sh`) and a registration gate
(`scripts/check-control-registration.sh`, 3 references). Compliance tracks
mechanization, not emphasis.

## What was actually missing

Nothing. Both halves existed; neither was reachable.

**The harness exists.** `scripts/brief-step0.py` (1,181 lines, `just brief`,
landed 2026-08-29) derives the conclusion and hypothesis heads from a target's
`formal.statement`, runs the `shape_search` query, and adds the three things
the raw query cannot: whether a declaration with these constants is already in
the environment *by rendered type rather than name*; every module basename the
target could mean, **both paths** when a basename lives in two preludes (the
`crt.rs` hazard); and whether the target is held-out, a mutation control, or
divergence-blocked. It exits 3 when its own control probe fails — so no ABSENT
in that run means anything — and 4 on a stale snapshot. It is the answer to
"is this already done", packaged so the dispatcher runs it once instead of the
lane running it never.

It is named in the `justfile` and in `check.sh`'s controls step. It is named
**nowhere** in CLAUDE.md's retrieval section, which is the several-thousand-word
passage every lane and every brief-writer actually reads about this exact
problem. That section argues at length for `shape_search` and never mentions
that a command exists which assembles the query for you.

**The gate exists too, and had never run.** `scripts/check-shape-duplicates.py`
(282 lines, 2026-08-27) consumes `shape_search --duplicates`, which groups
declarations whose admitted **types are identical up to binder naming** — not a
coarse signature; `ShapeIndex::shape_of` erases only binder names, binder info
and universe levels. Two declarations in a group state the same proposition.
That is precisely what failed retrieval produces: two proofs of one fact that
must stay in sync while the kernel happily verifies both.

The checker is well built. It fails in **both** directions — an unadjudicated
group fails, and an allowlist entry that `shape_search` no longer reports fails
as stale — and it refuses an allowlist entry with no reason, on the stated
grounds that an allowlist without reasons is how a gate becomes decoration. It
distinguishes exit 1 (a finding) from exit 2 (the tool could not run), and it
cross-checks the tool's own `verdict: DUPLICATE-GROUPS N` line against the
number of `DUPLICATE` lines it parsed, so truncated output cannot read as a
clean run.

And it was named by exactly one line in any gate:

```
scripts/check.sh:347:step shape-duplicates-tests python3 -m unittest scripts.tests.test_check_shape_duplicates
```

Its **unit tests**. Not the checker. Zero references in `scripts/local-ci.sh`
— the file `ci.yml`'s own comment calls the authoritative gate for `main` —
zero in `.github/workflows/ci.yml`, zero in `hooks/pre-push`, zero in the
`justfile`. So the guards were tested against synthetic fixtures on every run
and the real environment was examined only when a human typed the command.

This is the checker-that-cannot-fail defect in a form none of the existing
guards cover, and the quietest one yet: nothing is vacuous, nothing exits 0 on
completion alone, the step name even contains the checker's name. The suite
passes. The subject is never looked at.

## What the first automatic run found

Run against a **freshly built** index (2,623 declarations, built from this
lane's HEAD; the shared checkout's prebuilt binary was four hours stale at
2,577 and was not used for the finding):

```
FAIL: 5 duplicate group(s) not on the allowlist:
  NEW/UNADJUDICATED  Int -> Int -> Int -> Eq                       Int.add_mul Rat.int_right_distrib
  NEW/UNADJUDICATED  Nat -> Nat -> Nat -> Eq -> Nat.dvd -> Nat.dvd Nat.dvd_of_dvd_mul_left Nat.gauss_lemma
  NEW/UNADJUDICATED  Nat -> Nat -> Nat -> Nat.dvd -> Eq -> Eq      Nat.coprime_dvd_left Nat.coprime_of_dvd_left
  NEW/UNADJUDICATED  Nat -> Nat -> Nat -> Nat.le -> Nat.le         Nat.clog_mono_right Nat.clog_monotone
  NEW/UNADJUDICATED  Nat -> Nat -> Nat -> Nat.le -> Nat.le         Nat.log_mono_right Nat.log_monotone
```

Five groups in the four days since the 2026-08-27 adjudication. Each was read
at its declaration site — statement and proof body, not shape — as the
checker's own failure text demands:

- **Four are deliberate Mathlib-name aliases whose bodies already forward.**
  `declare_dvd_of_dvd_mul_left`'s entire result is
  `d.lemma(p.gauss_lemma, &[k, m, n, cop_hyp, dvd_hyp])`;
  `declare_coprime_dvd_left` forwards to `primes.rs`'s `coprime_of_dvd_left`,
  which carries the real `gcd_dvd_left`/`dvd_trans`/`dvd_gcd` argument; and
  both `_monotone` lemmas forward to their `_mono_right` partner, because
  Mathlib states them as `Monotone (log b)` and `Monotone f` **is** Mathlib's
  own name for the pointwise form, so the two core renderings coincide.
  Allowlisted with that reason.

- **One is a genuine independent re-derivation.** `Int.add_mul`
  (`int_prelude/add_basics.rs`) and `Rat.int_right_distrib`
  (`rat_prelude/laws.rs`) state right-distributivity over `Int` and ran the
  *same* chain — `mul_comm` to swap onto `left_distrib`'s shape, `left_distrib`
  once, `mul_comm` back on each summand — in two preludes under two names. The
  Rat-side name stays (20 call sites across `rat_prelude/` and `creal/sqrt.rs`)
  and its body is now `d.lemma(int.add_mul, &[a, b, c])`. One proof term, two
  names. Verified: `cargo test -p axeyum-lean-kernel --lib rat_prelude::`,
  **151 passed, 0 failed**, 376 s; the statement is unchanged, so no downstream
  prelude is affected.

Note what the ratio says about the gate's value and about its cost. Four of
five findings were benign, and that is the normal state of a healthy ratchet —
it is not evidence the gate is noise. The gate's job is that the fifth one
cannot land unread.

## Decision

1. **`scripts/check-shape-duplicates.py` becomes an L0 gate.** Wired in
   `scripts/local-ci.sh` (`run … || rc=$?`, in the L0 block after
   `check-proposition-duplication`), in `.github/workflows/ci.yml` inside the
   `l0-trust-closure` job — the only job that already does a `--release` build
   of `axeyum-lean-kernel`, so it reuses that build — and in `scripts/check.sh`
   beside its existing tests step. Not in `hooks/pre-push`: at ~110 s it is
   well above that hook's three sub-two-second gates.

2. **It joins `L0_GATES` in `scripts/check-l0-gate-enforcement.py`** (seven →
   eight), which asserts every L0 gate appears in `ci.yml`, carries no
   `continue-on-error`, does not swallow its status, appears in `local-ci.sh`
   and feeds `rc` there. This is what stops the wiring drifting back out, which
   is exactly how it was lost the first time. `verdict=PASS`, `gates=8`,
   `local_ci_gates=8`; `--self-test` still kills all 9 cases and
   `scripts.tests.test_l0_gate_enforcement` is 15/15 green.

3. **CLAUDE.md's retrieval section names `just brief`**, states the three
   things it adds over a raw `shape_search` query and its two self-reported
   failure exits, says the step belongs to the brief-writer rather than the
   lane, and carries the re-measured 7.0% / 42.0% / 2.3% numbers. No new
   script: the brief for this work said explicitly that building a second tool
   doing what the first already does is the very failure this lane exists to
   address, and that is the right call.

4. **The allowlist's exact-length pin is replaced by a floor plus structure.**
   `test_the_committed_allowlist_is_itself_valid` asserted `len == 10`; that
   number measured nothing the gate does not already measure — the gate fails
   on any group not on record, so the list cannot grow silently — and it broke
   on the first legitimate adjudication (10 → 15). It is now
   `assertGreaterEqual(…, 10)` plus a per-entry requirement that `reason`,
   `source` and `adjudicated` are all non-empty, which the count never checked.

## What this gate asserts, and what it does not

**Asserts.** Every group of declarations in the built environment whose types
are identical up to binder naming is on record with a written reason, a date,
and a document reference; and every entry on that record still names a group
the tool reports. Both halves fail the build.

**Does not assert.** Three things, stated because a gate implying coverage it
lacks is worse than no gate:

- **Hiding place 2 is structurally out of reach.** A reusable step built
  *inline* inside a larger declaration has no declaration of its own, therefore
  no type, therefore cannot appear in any duplicate group. `powsq.rs`'s
  even/odd split and `convergence.rs`'s `Within` → `close_within` step are the
  documented instances. No name-based or type-based tool can ever see one
  re-derived; only reading proof bodies finds it.
- **Same shape is not same content across carriers.** `Int.add_mul` and
  `Rat.int_right_distrib` shared a shape *and* a proposition, but the tool
  groups by type key, and a human must read the two declarations before
  deciding. The gate forces the reading; it does not perform it.
- **It says nothing about the 7.0%.** Duplicate declarations are the *outcome*
  of failed retrieval, which is why gating them is worth more than gating a
  mention of `shape_search` in a status document (trivially gameable, measures
  nothing). But an outcome gate is lagging: a lane that spends four hours
  re-deriving a lemma and then *finds* it has cost the same four hours and
  produced no duplicate for this gate to see. The harness half — item 3 — is
  what addresses that, and its effect is not yet measurable.

## Verification

Break/restore was run through the **real** `cargo run --release --example
shape_search -- --include-constructed --duplicates` path against the real
environment, using the checker's `--allowlist` flag so no tracked file was
mutated (mutating a tracked file in a shared checkout breaks sibling lanes'
builds, and the failures look like their bug):

| subject | result |
| --- | --- |
| committed allowlist | exit **0** — `OK: 15 duplicate group(s), all allowlisted with a reason.` |
| one adjudicated entry dropped | exit **1** — `NEW/UNADJUDICATED  Int -> Int -> Int -> Eq  Int.add_mul Rat.int_right_distrib` |
| one entry added naming a group nothing reports | exit **1** — `STALE  Nat.no_such_lemma_a Nat.no_such_lemma_b` |

And the strongest evidence is not synthetic: the gate's **first** run on its
true subject exited 1 and named five real groups, one of which was a real
defect that is now fixed.

The four assertions in the rewritten allowlist test were each verified to be
killed by exactly one mutated copy of the allowlist, with the baseline clean —
truncate below the floor kills the floor assertion, drop `source` kills the
`source` assertion, drop `adjudicated` kills that one, blank the `reason` kills
that one. No new guards were added to the checker itself, so nothing new was
registered in `scripts/tests/mutation_controls.py`; the checker's own guards
already carry a self-contained mutation loop (`MutationTests`, run under
`python3 -B` so the stale-`.pyc` hazard cannot apply).

## Consequences

- A duplicate declaration can no longer reach `main` unread. Five reached it in
  four days while the checker existed.
- Adjudicating a group is now a required step with a cost: read both
  declarations, write a reason, cite a document. That cost is the point.
- The 42% / 7.0% gap is a claim about *mechanization*, and this ADR mechanizes
  the outcome half. If the harness half works, `brief-step0`'s 2.3% should move
  and the count of recorded "the lemma already existed" incidents should stop
  climbing. Both are measurable; neither is measured yet, and this ADR does not
  claim them.
- **A gate on the retrieval-failure OUTCOME is the honest one to build.** The
  tempting alternative — assert that lane documents mention `shape_search` —
  would be satisfied by typing the word, which is the definition of a checker
  that cannot fail.

## References

- ADR-0608 — `shape_search`, shape-indexed retrieval over `kernel.environment()`
- ADR-1050 — the L0 trusted-library safety gates and their enforcement
- ADR-1165 — the cost model re-measured; the 4.8% / 46% figure this re-measures
- `docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md`
- `docs/research/11-design-review/2026-08-27-shape-search-duplicates-adjudicated.md`
- `docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md`
