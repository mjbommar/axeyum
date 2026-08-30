# Notes: 284-autogenesis-gate-rot

Detail moved out of [`../status/284-autogenesis-gate-rot.md`](../status/284-autogenesis-gate-rot.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

2. **`autogenesis-chain-catalog` — BROKEN, fixed; plus one independent stale
   fact found and fixed.** `theorem_index` raised on ANY kernel theorem named
   by two facts. Found 3 such pairs — `Int.modEq_add_left`,
   `Nat.coprime_of_lt_prime`, `Nat.descFactorial_of_lt` — all the ADR-0603
   "flip an `ml430` mirror onto an existing declaration" pattern CLAUDE.md's
   own gotchas document by name. `check-fact-depends-derived.py` already
   accepts this shape (`setdefault`, first-wins); `theorem_index` didn't.
   Fixed to resolve deterministically: a fact with `formal.kernel_theorem`
   PINNED wins over one resolved by regex fallback, ties break on fact id.
   Verified for all 3 real pairs that the winning fact's `depends_on` already
   covers every direct kernel dependency `theorem_dependency_inventory`
   reports (checked against the prebuilt binary, not assumed). Independently
   found `F:int-modeq-add-left`'s `formal.statement` was STALE — it still
   recorded the theorem's pre-generalization type (`0 < n` hypothesis, 6
   binders) after the `int-modeq` lane replaced the declaration in place with
   an unconditional 5-binder form; confirmed against the current kernel via
   `int_theorem_inventory` and corrected it. `depends_on` needed no change.
   Replaced the now-wrong rejection test with 3 tests covering the new
   resolution rule. Commit `ad130c478`.

3. **`autogenesis-bounded-induction-family` — genuine producer drift since
   2026-08-22, fixed the reproduction snapshot.** Of the operation's 4 covered
   targets, exactly one (`natOneAscFactorial`) replayed to a different
   `proof_sha256` than committed; the other 3 reproduced byte-identical.
   Verified the new value 3x (deterministic, not flaky). `goal_sha256`,
   `target_content_sha256`, binders/inductions used, `axioms=0`,
   `declarations=57` were all unchanged — only the producer's exact
   synthesized term differs. The manifest was frozen 2026-08-22 14:45;
   `e1f2133c0` (16:42 same day) explicitly re-verified this same hash
   byte-identical, so the drift is in one of ~40 later commits to
   `crates/axeyum-lean-import`. Did not bisect further — `crates/` is out of
   scope for this lane and nothing soundness-relevant changed. Regenerated the
   one drifted `proof_sha256` in
   `mathlib-bounded-induction-family-one-ascfactorial-v1.json`. The underlying
   fact's admitted kernel term is untouched; this manifest is a
   reproduction-capability snapshot, not evidence. Commit `df414fe8c`.

4. **`autogenesis-reflexivity-coverage` — BROKEN (half-pinned), fixed.**
   `validate()` already pins nursery MEMBERSHIP to the census commit
   (`pinned_nursery`, with a comment explaining exactly why a live re-read
   goes red for a population change it predates) but read fact CONTENT live
   — `lambda fact_id: generator.load(generator.fact_path(fact_id))`. Once
   `F:ml430-int-fib-of-odd-66560495` was later proved, its `formal.language`
   flipped `lean4-surface` -> `lean4` (ADR-0601 again) and the generator,
   which embeds `formal.statement` verbatim into a real Lean module, rejected
   it. Added `pinned_fact(commit, path)` mirroring `pinned_nursery` exactly
   (`git show`, fails closed, no live fallback) and used it for fact content
   too. Added a fail-closed unit test. Commit `40a824f7e`.

5. **`autogenesis-nursery` — CAUSED BY THE REFILL, real, NOT fixed.**
   `237c1abdd` (this session, sibling lane) correctly re-derived 1054
   previously-MISSING `depends_on` edges from the actual kernel proof graph.
   That exposed 3 genuine dependency components that connect facts across
   `train`/`development` (none touch `held-out`) — e.g.
   `F:ml430-nat-descfactorial-le-2b8cc09a` (train) directly `depends_on`
   `F:ml430-nat-choose-le-choose-907b5042` (development); a third component
   bridges through the two `longitudinal` bootstrap facts
   (`F:nat-zero-add`/`F:nat-mul-one`), which I initially suspected of being an
   over-broad bridge — **wrong**: `check-autogenesis-nursery.py` has a
   SEPARATE, deliberate `evaluation_longitudinal_overlap` check for exactly
   that shape, so excluding longitudinal from the graph would silently
   disable an intentional safeguard, not fix a false positive. The nursery's
   own freeze doc
   (`docs/autogenesis/16-mathlib-frozen-nursery-split-result.md`) states the
   design goal in so many words: "no detected component, source-group,
   family, proof-shape, or longitudinal overlap" at freeze time (2026-08-18).
   These crossings are real and were always latent in the proof graph; they
   were only INVISIBLE because `depends_on` understated them until today's
   repair. The correct remedy (ADR-0542-style: move a whole family, record an
   amendment) needs a real judgment call about which of 3 independent family
   pairs to move and in which direction, which I did not make under this
   task's time budget rather than guess. **Left open, with full component
   membership below for whoever picks this up.**

6. **`development-partition` — real violation, NOT fixed, and the standard
   remedy is BLOCKED by another gate.** `authoritative-mathlib-nat-modeq-remainder-family-v1`
   (registered `9943ae6bd`, 2026-08-26 — 4 days after this gate's own
   2026-08-22 inception) covers 3 `development`-only facts
   (`natural-modular-equivalence` family) with no train fact — exactly the
   "producer authored against the evaluation set" shape this gate exists to
   catch. The gate's own docstring says exemptions come from nursery
   amendments; I checked whether that route applies and it is HARD-BLOCKED:
   `create-autogenesis-mathlib-nursery-split.py`'s `validate_amendments`
   asserts `amendment["from"] != "held-out"` -> raise
   `"only a held-out spend needs an amendment record"`. The amendment ledger
   (`mathlib-nursery-split-policy-v1.json`, copied into `nursery-v1.json` by
   that script) is held-out-only by explicit design (ADR-0542's actual scope);
   hand-editing `nursery-v1.json`'s copy directly would immediately fail that
   OTHER gate's `--check` (verified: it recomputes the expected nursery from
   the policy and requires an exact match), and it's not one of my six.
   Checked whether the SAME producer route could honestly be extended to a
   train fact instead: the parallel `Int.ModEq` facts in `train`
   (`integer-modular-equivalence` family) are already closed, but by a
   DIFFERENT, hand-authored operation
   (`authoritative-kernel-int-modeq-shift-family-v1`, not the imported
   `bounded-type-directed-application-v1` route) — adding those fact ids to
   THIS operation's `applicability.fact_ids` without re-running the actual
   transaction against them would be fabricating coverage, which is worse
   than the violation it would silence. **Left open.**

Both open items are genuine, evidenced findings, not gate bugs papered over —
see the full write-up below for the exact component memberships and the
blocking mechanism, so the next lane does not have to re-derive either.

**Non-negotiable checks, before and after (unchanged by this lane's work):**

```
BEFORE: AUTOGENESIS_HOLDOUT_ISOLATION|held_out=67|files_scanned=1105|settled=0|references=0|verdict=PASS
AFTER:  AUTOGENESIS_HOLDOUT_ISOLATION|held_out=67|files_scanned=1105|settled=0|references=0|verdict=PASS
```

Also run clean at the end: `python3 scripts/validate-facts.py` (2034 facts, 0
errors), `python3 scripts/check-dispatchable-frontier.py` (non-empty, OK),
`python3 scripts/gen-plan.py --check` (exit 0), and
`python3 scripts/create-autogenesis-mathlib-nursery-split.py --check`
(unaffected by this lane, confirmed still green: `amendments=2`).

## Detail for the two open items

### `autogenesis-nursery` — the 3 leaking components

Reproduced with a throwaway script walking the same `components()`/adjacency
logic the checker uses, restricted to `EVALUATION_PARTITIONS` membership for
the leak *report* (matching the checker) while the *graph* still includes
every nursery entry including `longitudinal` (also matching the checker —
this is deliberate, see `evaluation_longitudinal_overlap`).

```
component A (bridges through longitudinal bootstrap facts):
  F:nat-zero-add                              longitudinal  nat-bootstrap
  F:nat-mul-one                               longitudinal  nat-bootstrap
  F:ml430-nat-descfactorial-self-899fc0e0     train         natural-factorial
  F:ml430-nat-self-le-factorial-cfdffc69      train         natural-factorial
  F:ml430-nat-factorial-*  (5 more)           train         natural-factorial
  F:ml430-nat-mod-lcm-ee6bdd41                development   natural-modular-equivalence

component B (direct train -> development proof edge):
  F:ml430-nat-descfactorial-le-2b8cc09a       train         natural-factorial
  F:ml430-nat-choose-le-add-9c463139          development   natural-binomial
  F:ml430-nat-choose-le-choose-907b5042       development   natural-binomial
  F:ml430-nat-choose-le-succ-62ae968b         development   natural-binomial
  F:ml430-nat-choose-mono-a1af9c18            development   natural-binomial

component C (direct train -> development proof edge):
  F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82   train        integer-gcd
  F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222  train        integer-gcd
  F:ml430-nat-coprime-of-dvd-18fcd09f                            development  natural-gcd
  F:ml430-nat-coprime-of-dvd-left-b0e2aa94                       development  natural-gcd
  F:ml430-nat-coprime-of-dvd-right-a640bd56                      development  natural-gcd
```

All three edges causing the crossing were ADDED by `237c1abdd` (confirmed by
`git show 237c1abdd -- <each fact file>`); before that commit each of
`F:ml430-nat-mod-lcm-ee6bdd41`, `F:ml430-nat-descfactorial-le-2b8cc09a`, and
the `natural-gcd` trio had an understated `depends_on` that hid the crossing.
The repair itself is correct and independently verified (round-trips through
JSON, only `depends_on` grew, checked key-by-key across all 306 files by the
sibling lane that made it). Whoever resolves this needs to decide, per
component, which family moves and in which direction (ADR-0542 whole-family
discipline), update `mathlib-nursery-split-policy-v1.json` (the authoritative
source `create-autogenesis-mathlib-nursery-split.py` copies from), and
re-verify no NEW crossing appears after the move.

### `development-partition` — why the standard remedy doesn't apply here

`scripts/check-development-partition.py`'s `amended_fact_ids()` reads
`nursery.get("amendments", [])` from the SAME `nursery-v1.json` that
`create-autogenesis-mathlib-nursery-split.py` treats as a generated copy of
`mathlib-nursery-split-policy-v1.json`. That generator's own
`validate_amendments` hard-rejects any amendment whose `from` is not
`"held-out"`. So the amendment array these two gates share is, by the OTHER
gate's explicit design, held-out-only (ADR-0542's actual scope) — it cannot be
used to exempt a train/development-only violation without either weakening
that validator's own rule (not this lane's gate, not touched) or hand-editing
`nursery-v1.json` out of sync with its generator (which fails
`autogenesis-mathlib-nursery-split --check`, verified: it recomputes the
nursery from the policy and requires exact match).
