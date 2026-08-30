# Session audit, 2026-08-30 — adversarial review of the coordinator's reported results

Lane `session-audit`, working from its own worktree at `main` = `e7496c44c`.
**Nothing here edits a fact, a proof, or a gate.** Where something is broken it
is reported; the repair belongs to another lane.

The brief was to refute, not to confirm. What follows is ordered by damage.
Every number below was produced by a command quoted beside it. Where a claim
survived attack I say so plainly and say what I ran, because "I checked" is not
evidence either.

**Instrument freshness.** The shared checkout's prebuilt
`target/release/examples/*` were stale — 24 kernel sources newer than
`nat_axiom_inventory` (04:02), and `shape_search` older still. Every kernel
measurement in this document was taken from binaries **built fresh in this
lane's own worktree** (255 s, `BUILD_STATUS=0`), for the reason CLAUDE.md gives:
a stale binary describes an older tree in every direction — absent, present, and
how big.

---

## Part 1 — refuted, or could not be verified

### 1. `natural-parity` (10 held-out rows) was never blind, and nothing records it

`F:ml430-nat-even-iff-024826e9` is held-out; its source is Mathlib's
`Nat.even_iff : ∀ {n : ℕ}, Even n ↔ n % 2 = 0`.
`crates/axeyum-lean-kernel/src/nat_prelude/parity.rs:616` declares

```
Nat.even_iff_mod_two_eq_zero : ∀ n, Iff (Even n) (Eq (mod n 2) 0)
```

with `Even n := ∃ k, n = k + k` — Mathlib's definition. Same proposition,
different name, so the R9 exact-name screen reports `natural-parity 0/10`.

```
git log -S 'even_iff_mod_two_eq_zero' main -> 414eef0a2  2026-08-29 12:10:13
git log -S 'natural-parity'          main -> 94b3e61e0  2026-08-29 17:22:14
```

**Five hours after the declaration landed.** This is byte-for-byte the shape of
the `natural-divisibility` amendment made *today*, whose own text says "these
rows were NEVER blind… a NAME screen such as R9 is structurally blind to a
proposition already proved under a different name." The same diagnosis applies
here and nobody has run it. Seven of the other nine rows are one carrier
transport away, with `Int.even_add`, `Int.even_add'`, `Int.even_add_one`,
`Int.ediv_two_mul_two_of_even`, `Int.odd_of_mul_left`, `Int.odd_of_mul_right`
and the bridge `Int.even_iff_nat_abs_even` all in the environment — and
`int_prelude/parity.rs:200` says in its own module doc that it builds the
*Nat-level* content of two of those rows inline, which no name screen can see.

No held-out row was attempted, and no determination about provability is
recorded here or by the sub-lane.

### 2. Three of ten `fermat-numbers` rows were established in-tree 21 minutes before draw 7 preregistered them

`nat_prelude_tests.rs:19039`, `fn fermat_number_evaluates_correctly`, asserts by
kernel `def_eq` that `fermatNumber 0 ≡ 3`, `fermatNumber 1 ≡ 5`,
`fermatNumber 2 ≡ 17`. The three held-out rows are
`F:ml430-nat-fermatnumber-{zero,one,two}-*`, whose entire content is those three
equations — and the test's own doc comment names the Mathlib lemmas it is
matching.

```
0065c83b1  2026-08-30 06:48:10  feat(nat_prelude): declare Nat.fermatNumber
29d51bd0b  2026-08-30 07:09:52  feat(autogenesis): draw 7
git merge-base --is-ancestor 0065c83b1 29d51bd0b   -> YES
```

ADR-0653 declined draw 6 over `Nat.dist` at R9 **2 of 10**. Draw 7 shipped
`fermat-numbers` at an effective **3 of 10**, because ADR-0653's own exemption
says "the evaluation-test requirement for a new `Definition` is safe here
precisely because a test is not a declaration." That exemption is what fails:
R9 sees declaration names, and blindness is about whether the mathematics is
written down here. For these three rows it is.

`natural-nth-selector`, the other draw-7 family, is clean by the same test.

### 3. "IVT dominant" overstates the audit document, and that document applies its own Pareto criterion inconsistently

I reported IVT as *dominant*. `08-ivt-and-evt-measured-against-mathlib.md` does
not say that, and cannot: its own §4 IVT table records **three** axes where
Mathlib wins.

| axis | the document's own verdict |
| --- | --- |
| Exact conclusion `∃x, f x = t` | "**Mathlib dominates** … **This loss is real and permanent**" |
| Generality of statement | "**Mathlib dominates, but reachably**" |
| Generality of structure | "**Mathlib dominates; not reachable here** … **Report it as a loss, not as 'not meaningful.'**" |

The document then applies a strict test to EVT and concludes against it:

> Pareto dominance requires being no worse on every axis and better on one. …
> it is a strict improvement on one axis with a strict regression on another,
> which is the definition of *not* dominating.

**Applied consistently, that test fails IVT too.** IVT has a strict regression
on the exact-conclusion axis, which the same document calls real and permanent.
And `07-the-cost-model-and-pareto-position.md` — the claim being tested — says
"**On every statement we ship, strictly dominate**," not "hold a good position
on the frontier." Yet §4 concludes "Net for IVT: the Pareto claim holds as
`07-…` states it."

The honest verdict for IVT is **mutually non-dominated**: neither library's IVT
dominates the other. We win trusted base, boundary statement and computational
content; Mathlib wins exactness, generality of statement and generality of
structure. That is a real and defensible position — it is simply not dominance,
and the difference matters because dominance is the word `07-…` uses.

Note which way the asymmetry runs, because it is the opposite of the narrative:
**IVT's dominance failure is permanent; EVT's is fixable.** §5 items 1–2 name
`CReal.supOn` and `CReal.evt_approx_max` as ordinary work.

To be clear about what I could *not* break: I read Mathlib myself at the pinned
commit rather than inheriting the quotes, and they are verbatim.

```
git -C /data0/axeyum/lean-import-toolchain/mathlib4 log -1 --format=%H
  c5ea00351c28e24afc9f0f84379aa41082b1188f
Mathlib/Topology/Order/IntermediateValue.lean  intermediate_value_Icc   -- verbatim
Mathlib/Topology/Order/Compact.lean            IsCompact.exists_isMaxOn -- verbatim
Mathlib/Order/Filter/Extr.lean                 IsMaxOn                  -- verbatim
```

That lane did not grade its own homework on the Mathlib side. It graded it on
the criterion.

### 4. `references=0` is true of what the gate scans and misleading as a claim about the tree

`AUTOGENESIS_HOLDOUT_ISOLATION|held_out=136|files_scanned=1107|settled=0|references=0|PASS`
re-derives exactly. But `check-autogenesis-holdout-isolation.py:scan_targets()`
is the whole scan set:

```python
targets = list(ARTIFACTS.glob("*.json"))          # artifacts/autogenesis, NON-recursive
if EPISODES.is_dir():
    targets += EPISODES.rglob("*.json")
    targets += EPISODES.rglob("*.json.snapshot")
```

Excluded: `crates/`, `docs/`, `scripts/`, `PLAN.md`, `artifacts/facts/`, and
`artifacts/autogenesis/producer-contracts/` (a real subdirectory the
non-recursive glob drops — 2 JSON files). A `grep -rnoF` of all 136 ids over the
excluded tree, verified working by its non-empty result, finds at least eight
distinct held-out ids present today. Most are benign by intent (a
`not_elaborable` exemption set, a refusal-test fixture). Two are not:

- `nat_prelude/sqrt.rs:55` reasons in a source comment about
  `F:ml430-nat-sqrt-eq-79ae8eae` and states that `sqrt_zero`/`sqrt_one` are its
  `n ∈ {0,1}` instances, landed as theorems.
- `docs/plan/generated/autogenesis-baseline.json` publishes a
  premise→consequent graph over held-out sqrt rows (mitigated: those edges come
  from the facts' own preregistered `depends_on`).

So the line should be read as "no reference in the autogenesis artifacts," which
is what it measures, and not as "the held-out set is untouched by the tree."

### 5. Seventeen `proved` facts carry no `checker_command` at all, and three gates each decline to enforce it

All seventeen are `ml430` Nat mirrors, all `kernel-lean`, all
`axiom_footprint: []`, all `check_status: "checked"`, with an evidence row that
has no `checker_command` key: `F:ml430-nat-{bitwise-bit, bitwise-comm,
bitwise-swap, choose-self, choose-succ-self, choose-succ-succ, choose-zero-right,
choose-zero-succ, even-xor, factorial-pos, land-assoc, land-bit, land-comm,
ldiff-bit, lor-assoc, lor-bit, lor-comm}-*`. Two more facts mix empty and
non-empty rows.

- `close-fact.py:127` **does** refuse this — so these were written by a path
  that bypassed it.
- `check-fact-evidence-replay.sh` prints `UNCOVERED` and exits 0:
  `sys.exit(1 if (failed or timed_out_facts or not_run) else 0)` — `skipped` is
  absent, with a comment saying "validate-facts.py owns that rule."
- `validate-facts.py` does **not** own that rule. Its 21 `checker_command`
  mentions are shape checks on `ev.get("checker_command") or ""`.
  `validate-claims.py:85` requires the key; the fact ledger does not.

Fair framing: the underlying mathematics *is* checked by sibling native facts.
What has no checker is the mirror's own claim — that our theorem's proposition
matches Mathlib's — which is the only thing a mirror exists to assert.

### 6. `check-mirror-statement-fidelity.py` is RED in the shared checkout right now

```
$ cd /home/mjbommar/projects/personal/axeyum && python3 scripts/check-mirror-statement-fidelity.py
MIRROR_STATEMENT_FIDELITY|facts=2265|mirrors=514|hash_verified=502|unpinned=12|violations=11|verdict=FAIL
REAL EXIT=1
```

Two `proved`, `kernel-lean`, `axiom_footprint: []` facts have had
`formal.statement` overwritten with `Kernel::render_lean` output, so the pinned
Mathlib proposition is no longer in the fact claiming to mirror it:
`F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7` and
`F:ml430-nat-totient-dvd-of-dvd-9622e44a`.

**Control, same script, same 2265 facts, committed state:** in this lane's
worktree it prints `violations=0|verdict=PASS`, `REAL EXIT=0`. Shared-checkout
mtimes are 09:16 today. **So this is live in-flight lane work, not a `main`
regression** — but `just check` is red in the shared checkout as of this
writing, and `validate-facts.py` exits 0 on the same tree because it has no
statement-fidelity rule. `2265 facts checked, 0 errors` is a true statement
about a validator that structurally cannot see this.

### 7. The v2 nursery manifest still declares itself pristine after being amended

`artifacts/autogenesis/nursery-v2-extension.json` has
`preregistered_family_partitions.natural-divisibility = "held-out"` and
`family_partitions.natural-divisibility = "development"` — amended — with **no
`amendments` key** and `state: "preregistered-before-target-outcomes"`, the
pristine string. ADR-0542 decision point 2 requires the state become
`…-with-recorded-amendments` "so no reader can take the artifact for pristine."
The v1 script does this correctly; `gen-autogenesis-nursery-refill.py:1407`
hard-codes the pristine string unconditionally, so the v2 generator can never
mark its own manifest as amended. The amendment record itself is fine and lives
elsewhere; the file a reader opens is the one that misdescribes itself.

### 8. The R9 screen reads a stale snapshot, and the snapshot's own note has the direction backwards

`artifacts/autogenesis/kernel-environment-snapshot-v1.json` was last written at
06:55; seven commits landed on `main` after it, including 805 lines of
prime-divisibility mirrors carrying parity content while `natural-parity` is
held-out. The snapshot's `notes` field asserts it "can only go stale in the
fail-closed direction (a declaration that landed after it reads as absent)."

**For R9 that is backwards.** R9 *refuses* a family when a held-out name is
already declared, so a declaration missing from a stale snapshot means R9 does
**not** refuse — a contaminated family is admitted as blind. Stale is fail-OPEN
for the screen that protects the blind population.

### 5b. Five gate guards are survivors — a guard deletable with every registered control still green

The instruction was: for each gate "fixed" today, delete a guard and confirm
exactly one test dies. Five did not die.

**`check-merge-hygiene.sh` has no registered mutation controls at all.**

```
ls scripts/tests/ | /usr/bin/grep -c merge-hygiene            -> 0
ls scripts/tests/ | /usr/bin/grep -c check-aggregate-scope    -> 1   (positive control)
```

A gate landed today with zero controls, so every guard in it is a survivor by
definition. Its behaviour is mostly right when exercised by hand — conflict
markers fire on `.rs` at root, on `artifacts/facts/*.json` (the documented
incident), on a bare `=======`; the stale-generated-file check discriminates
cleanly (fresh `PLAN.md` → exit 0, hand-edited → exit 1). Two gaps: the
pathspec **excludes `scripts/tests/*`**, which is where every control suite
lives, and the header still says "the four things" while the body gives a
reasoned explanation for not enforcing the fourth.

**`check-aggregate-scope.sh`'s fail-on-new-divergence guard is deletable.**
Replacing `if [ -s "$new" ]; then` with `if false; then` leaves the registered
suite green — `AGGREGATE_SCOPE_CONTROLS|guards=5|negative_controls=2|PASS`,
exit 0. All five registered guards test the *normalizer*, none tests the gate's
own failure path. The gate does still detect a genuine divergence when run for
real (adding a step to one side → exit 1; deleting one → exit 1), so it is not
blind — but "13 phantom divergences → 0" is not the current state: it reports
**66** accepted divergences and at least two are still phantom, from a live
normalizer bug. `strip_wrappers` *tests* with a quote-aware regex and *strips*
with a quote-blind `line.split(" ", 1)`:

```
RUSTDOCFLAGS="-D warnings" cargo doc …  ->  'warnings" cargo doc --workspace …'
```

which is visibly what produced the baselined pair where `cargo doc` appears on
both sides under two different spellings.

**`check-cas-substance.py`'s headline count is derived but not ratcheted.** All
12 registered mutants die and the 14 does move under mutation, so it is not a
literal. But:

```
strip kernel reconstruction AND the cas_substance block  -> exit 0, "OK: 13 ..."
strip the reconstruction but KEEP the block              -> exit 1, G12 fires
delete the fact file outright                            -> exit 0, "OK: 13 ..."
```

It catches an *inconsistent* downgrade and passes a *consistent* one. A
cas-certificate fact can lose its kernel reconstruction, or vanish, and the gate
stays green with a quietly smaller headline. Compare `--expect-axioms 26`, which
is what a pinned expectation looks like elsewhere in this ledger.

**`check-generated-artifact-ownership.py` enforces ADR-0652 for one artifact.**
All 11 registered mutants die, and an owner naming a nonexistent artifact is
caught. But `GUARDED` is a hand-written literal and the gate reports
`artifacts=1` against 82 tracked `scripts/gen-*.py` and 3,889 tracked
`artifacts/**/*.json`. There is no tree enumeration, so a *zero-owner* artifact
is structurally invisible. This is exactly the "any test named every X must
derive its X from the authority" rule applied one level down and not at the top.

**`check-shell-antipatterns.sh` is correct and under-scoped.** Both directions
verified: a genuine `grep -q`-in-pipeline and an `echo "exit=$?"` after a
pipeline are each flagged; a bare `a || b` is not (the `||` fix works); and a
new violation appended to an already-baselined file is caught by a rising count.
But the scan is `git ls-files '*.sh'`, and two tracked bash scripts with
`pipefail` are never scanned — **both currently violating**:

```
hooks/commit-msg:36  head -1 "$msg_file" | grep -qiE '^(merge|revert|fixup!|…)'
hooks/pre-push:249   printf '%s\n' "$out" | grep -qE '^running [1-9]'
```

The second is the nonzero-test-count guard this repository insists on
everywhere, built from the exact idiom that reads a SIGPIPE as "no match". It is
fail-closed — a spurious push block, not an admitted bad push — but unscanned.
Separately, `cmd 2>&1 > file` is not detected at all, and a count-based baseline
cannot see a swap (one violation removed, another added).

### 5c. The ADR-0623 timeout claim is CONFIRMED, and the mechanism is sharper than I stated

Measured with `timeout (uutils coreutils) 0.8.0`:

```
timeout 2      bash -c 'trap "" TERM; sleep 30'   elapsed=30s  status=124
timeout -k 1 2 bash -c 'trap "" TERM; sleep 30'   elapsed= 3s  status=137
timeout 2      bash -c 'sleep 30'                 elapsed= 2s  status=124   (control)
```

So `timeout N` without `-k` really does not bind, and the fix does. The part I
had not said: the unbounded case **still returns 124**, so a caller testing for
the timeout status gets a correct-looking verdict after an unbounded wait.

The fix is applied without a bypass: all **399** `step` invocations route
through the capped runner (`check.sh:297`, `check-fast.sh:158`, both with
`--kill-after` plus a `pgid == pid`-guarded group kill), and a grep for a
top-level bypass is empty against a positive control of 399. Six hand-built
mutants were each killed by exactly one case. One cosmetic defect: the
group-kill mutant is killed by an assertion whose message blames
`--kill-after` — right kill, misleading diagnostic.

### 9. 166 `proved` facts assert in their own provenance that they were not established here

`provenance.established_by == "not established in this ledger"` on 166 of the
2,086. Only 11 overlap with §5. Nothing gates it.

---

## Part 2 — attacked and survived

### The excluded middle is not intuitionistically derivable — I could not break it

This was the one place a wrong answer would be a confident false claim about
foundations, so it got the most effort.

The kernel checks that `ipc_excluded_middle_not_provable` proves
`Not (Provable nil (p ∨ ¬p))`. It cannot check that `Provable` faithfully
encodes IPC, and — this is the direction that matters — a relation **weaker**
than IPC would make the theorem true and the headline claim unwarranted. So I
read the eleven constructors **out of the kernel environment**, not out of the
source:

```
./target/release/examples/ipc_soundness_inventory --require-axiom-free
  | /usr/bin/grep 'Provable\.'      -> 12 rows (11 constructors + Provable.rec)
```

They are exactly `ax_head, weaken, and_intro, and_elim1, and_elim2, or_intro1,
or_intro2, or_elim, imp_intro, imp_elim, bot_elim`, each with the standard
natural-deduction type. That is the complete IPC rule set for this signature,
and the signature has no gap: `Formula` is `var | bot | and_ | or_ | imp`
(`ipc_heyting.rs:227-242`), with no `top`, so no missing `⊤I`.

The lane's list-context argument holds under my own reading. `ax_head` gives
`Provable (φ::Γ) φ` for any `Γ` and `weaken` prepends, so every list member is
derivable; a set-context derivation replays by induction onto any list whose
elements cover the context, with `imp_intro` and `or_elim` pushing onto the head
in exactly the position they need. No derivation is lost, so `Provable ⊇ IPC`,
which is the inclusion the headline claim requires.

I also checked the one structural way a bogus inductive could poison this:
`inductive.rs` does run a pinned Lean-4.30 strict-positivity check
(`check_group_constructor_positivity`, `NonPositiveInductiveOccurrence`).

Measured, on a freshly built binary:

```
ipc_soundness_inventory ipc_excluded_middle_not_provable --require-axiom-free
  -> exit 0;  axioms=0
     Not (Provable FormulaList.nil (Formula.or_ (Formula.var AxNat.zero)
          (Formula.imp (Formula.var AxNat.zero) Formula.bot)))
     -- verbatim what the fact publishes as formal.statement
… ipc_excluded_middle_not_provable_FABRICATED --require-axiom-free  -> exit 1
… --require-axiom-free --expect-count 50   -> exit 0, "50 declarations checked"
… --require-axiom-free --expect-count 49   -> exit 1, "drift in either direction"
```

The checker discriminates in both directions, and the whole 50-declaration
package is axiom-free. **Not refuted.** The residual limit is the one the fact
already states: faithfulness of `Provable` is a meta-level judgement, checkable
by reading eleven types and not by the kernel.

### `Nat.totient_mul_of_coprime` — statement correct, coprimality load-bearing and pinned

Read from the kernel, not from the fact:

```
./target/release/examples/nat_theorem_inventory Nat.totient_mul_of_coprime
Nat.totient_mul_of_coprime  3  ((x0 : AxNat) -> ((x1 : AxNat) ->
  ((x2 : Eq.{1} AxNat (AxNat.gcd x0 x1) (AxNat.succ AxNat.zero)) ->
   Eq.{1} AxNat (AxNat.totient (AxNat.mul x0 x1))
                (AxNat.mul (AxNat.totient x0) (AxNat.totient x1)))))
```

`Nat.totient` is pinned by evaluation (`totient 1 = 1`, `totient 6 = 2`,
`totient 9 = 6`, with `≠ 3` and `≠ 5` negative controls), so it is Euler's
totient and not something trivially multiplicative. Coprimality is load-bearing
and the test says so: `totient_mul_of_coprime_computes_at_coprime_pairs_with_a_non_coprime_control`
carries the `m = n = 2` case where the identity is **false** (2 against 1) and
asserts `!def_eq`.

Following CLAUDE.md's own rule — re-run a plan's numeric checks, do not inherit
them — I ran the numerics rather than reading them:

```
python3 scripts/tests/check-totient-mul-coprime-numerics.py   -> all checks passed
  NEGATIVE CONTROL: the permute step FAILS at all 26 non-coprime pairs
  NEGATIVE CONTROL: the identity fails at ALL 26 non-coprime pairs
  NEGATIVE CONTROL: smallest counterexample is m=n=2 -- totient(4)=2 vs 1*1
```

**Not refuted.**

### The prelude axiom table, measured on a fresh binary, and its checker discriminates four ways

```
./target/release/examples/nat_axiom_inventory --include-constructed --require-axiom-free creal
logic 0 | nat 0 | integer 0 | rat 0 | string 0 | creal 0 | complex 0 | cpoint 0
axreal: axiom=30 opaque=0 quotient=0 total_trusted=30      -> exit 0
```

All 30 rows are the `AxReal` namespace. Fail directions, each run bare:

```
--require-axiom-free axreal        -> exit 1  "axreal trusted surface = 30, expected 0"
--require-axiom-free NOT_A_PRELUDE -> exit 1  "not a prelude this tool knows about at all"
                                              (a distinct message from a known-but-unbuilt prelude)
```

That second one matters: it is the coverage trap closed explicitly, by a tool
whose evidence 1,045 facts depend on. **Not refuted.**

### The ledger histogram

Re-derived twice independently by `json.load` over all 2,265 files, once by me
and once by a sub-lane, in two different checkouts:

```
computed 2 | conjectured 3 | open 170 | proved 2086 | refuted 4 | TOTAL 2265
```

Matches the published line exactly. The 2266-vs-2265 gap is
`artifacts/facts/smt2/`, a directory of 27 `.smt2` instances that `ls | wc -l`
counts and the validator's `*.json` glob does not. Benign.

The validator's semantic rules also hold, verified by reading `validate-facts.py`
and by independent count: 0 established facts with zero evidence, 0 with no
`checked` row, 0 `proved` facts carrying a non-`checked` row, 0 `open` facts
carrying evidence. All 4,294 evidence rows are `check_status: checked`.

### Evidence-shape census — the 40-of-162 failure has not recurred at scale

Over all 2,086 proved facts (4,282 evidence rows), first-match-wins:

| shape | rows |
| --- | --- |
| `grep -c` consuming the pipe with a tested count | 2,079 |
| `--require-axiom-free` | 1,831 |
| `test` / `[[ ]]` assertion | 275 |
| `python3` gate script | 40 |
| **no discriminator found** | **29** |
| `--expect-*` / `--require-*` | 17 |
| plain `grep` (exit status) | 6 |
| bare `cargo run` | 5 |

And the vacuous-filter question was answered empirically, not by shape: all 116
distinct `cargo test` positional filters were resolved against a workspace index
of 9,194 `#[test]` functions, and twelve were run against a fresh prebuilt
lib-test binary. Every one matched a nonzero count; a deliberate
`ZZZ_this_filter_matches_nothing` control matched 0. **No vacuous filter found.**

### The `generated-unreviewed` population — the coordinator's reading holds, with one caveat worth stating

My worktree measures **1,045**, not 1,035; the difference is exactly the ten
`CReal` IVT/EVT rows curated after my merge base. All 1,045 are `proved` and all
are `kernel-lean`. Each carries exactly two evidence rows (2,090 = 1,045 × 2),
and both halves discriminate:

```
theorem_dependency_inventory CReal.abs_add_le 2>/dev/null \
  | /usr/bin/grep -cE '^CReal\.abs_add_le[[:space:]]'            -> 1, exit 0
theorem_dependency_inventory CReal.abs_add_le_FABRICATED … same  -> 0, exit 1
```

(Note these use `[[:space:]]`, not the `\t` that silently broke 68 checkers in
August.)

`formal.statement` really is the kernel's own render. Over a seeded random
sample of 40 generated facts with a `Nat.*` declaration, compared against
`nat_theorem_inventory` one name per invocation:

```
sample=40 statement_matches_kernel_verbatim=39 differs=0 missing=1
```

The one miss was **my probe, not the fact**: `Nat.Peano.surjective` is a nested
namespace that `nat_theorem_inventory` will not resolve, while the fact's actual
checker resolves it and exits 0, and the declaration is present in
`prelude_theorem_inventory` (1 row, against a positive control of 7 for
`Nat.totient_mul_of_coprime`). I nearly filed that as a finding.

**The caveat.** One of every generated fact's two evidence rows is a
*prelude-wide* command shared by up to **317** facts
(`nat_axiom_inventory --require-axiom-free creal`). It discriminates about the
prelude and says nothing about the individual theorem. All the fact-specific
weight is carried by the other row. That is not vacuous — but "two independent
checks" would be the wrong way to describe it, and the axiom-freedom half of
1,045 facts stands or falls on one command.

---

## Part 3 — what I could not check, and why

- **Mathlib's own axiom footprints.** Inferred from routing through
  `IsPreconnected` / `by_contra`, never measured. A `#print axioms` needs a
  Mathlib build, which no lane has run.
- **The three `creal_tests` IVT/EVT tests** cited as row-2 non-vacuity evidence
  were read, not executed — by the original lane and by me.
- **`check-fact-evidence-replay.sh`** — the only thing that would empirically
  confirm the 4,282 checkers still exit 0. It shells out to cargo across the
  whole ledger with a 9,900 s budget and would contend with five live lanes. Its
  *code* is what I read, and the `skipped`-not-in-exit-status defect in §5 is
  visible statically.
- **A fresh `shape_search` derivability sweep** over the two new held-out
  families. The shared prebuilt is stale (04:02, predating `Nat.fermatNumber` at
  06:48) and a false ABSENT is the one verdict that would matter. Findings 1 and
  2 came from the committed snapshot plus source reading instead.
- **Held-out provability.** By constraint, no held-out proposition was attempted
  and no determination about one is recorded.

## Disclosure

A sub-lane of this audit briefly violated read-only. Its mutation mirror
symlinked each *entry* of `artifacts/autogenesis/` into scratch;
`producer-contracts` is a directory, so a `mkdir -p` wrote through the symlink
into the real checkout. One file
(`artifacts/autogenesis/producer-contracts/session-audit-E-contract.json`, 123
bytes) existed for about three minutes and was removed; no tracked file was
modified, and the gate re-reports its exact baseline line. The generalizable
lesson: **a symlink mirror is not a sandbox.**
