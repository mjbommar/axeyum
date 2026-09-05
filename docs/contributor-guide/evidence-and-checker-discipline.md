# Evidence and Checker Discipline — a checker that cannot fail

At N lanes the ledger IS the product, so a checker that cannot fail is worse
than no checker: it does not slow the flywheel, it makes it manufacture
unfalsifiable claims at full speed.

Two rules carry most of the weight, and both are in
[CLAUDE.md](../../CLAUDE.md#hard-rules) as standing obligations:

- When you attach evidence, **make the exit status depend on the finding**.
- When you touch a checker, **delete one guard and require that exactly one test
  dies**. Six of seven guards in one suite were removable with everything still
  green, because they all rejected through one shared check.

## The two audits, and why they do not share a denominator

**2026-08-15.** 40 of 162 checker runs across 36 settled facts exited 0 on
completion alone — nothing in the command made the exit status depend on what
the run found — and that set included the inventory asserting axiom-freedom,
this project's headline claim.

**2026-08-25, re-measured over the whole ledger, and the picture is better.**
Across 488 facts and 590 `checker_command`s: 464 carry an explicitly
discriminating shape (`grep -c` consuming the pipe and a tested count,
`--require-axiom-free`, `--expect-axioms`, `--check`, `diff`), and the remaining
126 are `cargo test` / `cargo run` whose status depends on the suite passing.

**Those 126 are NOT the failure mode**, and I nearly reported them as such. A
`cargo test --test X` exits nonzero when a test fails, so it does depend on the
finding — the real vacuity risk is a suite that compiles to ZERO tests behind a
feature gate and prints `running 0 tests ... ok`. All 5 distinct
`(crate, --test suite)` pairs the ledger names are UNGATED, verified by reading
each file's head for `#![cfg(feature`, so none can pass vacuously that way.

The lesson is the one this document already teaches, aimed at its own author: **a
crude classifier that flags a whole shape is not a measurement.**

## What mutation testing cannot see

Mutation deletes guards that EXIST and asks whether a test dies. A guard that was
never written has nothing to delete. Nine guards in `nra_monomial_bound_cert.rs`
were each killed by exactly one test, and the module was still unsound. The
technique measures the strength of the guards you have; it says nothing about the
ones you are missing. The entries below name what does find them.

## An "every X" test that iterates its own list

**AN INVENTORY TEST THAT ITERATES ITS OWN LIST CANNOT SEE WHAT IS MISSING
FROM IT, AND ITS NAME WILL SAY OTHERWISE.** Measured 2026-08-26.
`every_creal_declaration_is_checked_and_axiom_free` looped over a
hand-maintained `expected` array, checking each entry's declaration kind and
`axiom_footprint`. Its name promises *every* `CReal` declaration; its
behaviour was *every declaration someone remembered to add*. Green on every
run, for as long as it has existed.

**The pinned length does not catch this.** It constrains the list against
itself -- 294 entries declared, 294 entries present -- and says nothing about
what the prelude actually declared. Both numbers can be right while the test
covers a fraction of the environment.

The fix is one assertion, checked against the ENVIRONMENT rather than the
list: enumerate `kernel.environment().iter()`, filter to the namespace the
file owns, and fail naming anything absent from `expected`.

It found **twelve** unchecked declarations on its first run. Five were that
session's. The other seven had been unchecked far longer -- `lt_cotrans` and
`apart_cotrans` (Ch12 cotransitivity) and the entire `limit` family
(`RegularSeq`, `limitSeq`, `limitSeq_regular`, `limit`, `limit_dist`), which
is **Bishop completeness**, this project's constructive substitute for the
least-upper-bound property. None had a `Theorem`-kind or axiom-footprint
check from this test.

All twelve passed once listed, so nothing rested on an axiom; the gap was in
the checking. And the headline axiom-freedom figure was never affected,
because `prelude_theorem_inventory` reads the environment directly -- which
is precisely why this file insists on reading metrics from the kernel and
never from a list or from source text.

Generalize it: **any test named "every X" must derive its X from the
authority, not from a literal.** If the list is maintained by hand, the test
measures the maintainer's memory. `nat_prelude_tests.rs`'s `theorem_names`
and the `complex` `named` array have the same shape and deserve the same
assertion.


## A certificate must carry every distinction its producer makes

**A CERTIFICATE MUST CARRY EVERY DISTINCTION ITS PRODUCER MAKES, or the checker
cannot re-derive the refutation — and mutation testing will not find the gap.**
Measured 2026-08-20 in `nra_monomial_bound_cert.rs`. The producer distinguished
`M < k` from `M <= k` (the first is refuted by `M >= k`, the second only by the
strictly stronger `M > k`), but the certificate recorded only the CONSTANT `k`.
So `check_monomial_bound_refutation` could not tell them apart and returned
`true` for a certificate refuting `a >= 1 ∧ b >= 1 ∧ a*b <= 1` — **satisfiable
at a = b = 1**. No wrong `unsat` shipped, because the producer declines that
query; but the *independent re-validator*, whose entire job is to catch a
producer that is wrong, would have accepted a forged refutation of a SAT query.

**Mutation testing could not have caught this, and it is important to see why.**
Mutation deletes guards that EXIST and asks whether a test dies. A guard that
was never written has nothing to delete. Nine guards in that module were each
killed by exactly one test, and the module was still unsound. The technique
measures the strength of the guards you have; it says nothing about the ones
you are missing.

What does find them: for every case the PRODUCER distinguishes, write an
adversarial fixture over a **satisfiable** query in which every other guard
passes. If the certificate cannot express the distinction, that fixture is
impossible to write — and the impossibility is the finding.


## An operation registry where every entry names one target

**AN OPERATION REGISTRY WHERE EVERY ENTRY NAMES ONE TARGET IS A DISPATCH
TABLE, NOT A PRODUCER — and it cannot fail to "produce".** Measured
2026-08-22: 24 registered operations, 23 facts covered, **0 naming more than
one fact, and 0 of 144 dependency-ready facts covered**. Coverage was 23-of-23
on theorems already proved and 0-of-144 on anything unproved. Nine capsules
landed in the ten hours before that was measured, each with a plan, a receipt
and a gate; the shape of the output had stopped changing and nothing was
watching that.

This is the checker-that-cannot-fail defect moved one arrow upstream, so the
same discipline applies: `scripts/gen-production-provenance-ledger.py` derives
generality from `applicability.fact_ids` — never from a label a fact carries —
and gates both counters. Before writing an operation for one theorem, ask what
the next three targets share with it; `applicability.fact_ids` is a list and
nothing ever required length one. Full retrospective:
`docs/autogenesis/228-capsule-lane-retrospective.md`.


## A traced plan's "verified numerically" is itself a claim

**A TRACED PLAN'S "VERIFIED NUMERICALLY" IS ITSELF A CLAIM, AND ONE OF THEM
WAS FALSE.** The tracer/executor split — one lane writes a hand-traced,
Python-checked plan and deliberately writes no code, the next executes it —
closed this repository's two hardest bitwise targets and three successive
totient refinements. Its stated strength is that every non-obvious step is
checked numerically first.

Measured 2026-08-30: a plan asserted a `count_range_row_major` identity was
coprimality-INDEPENDENT and "verified numerically at non-coprime pairs
(4,6),(6,9)". It is false at **26 of 26** non-coprime pairs with
`1 <= m,n <= 9` — the smallest counterexample is `m = n = 2`, where
`totient(4) = 2` against `totient(2)*totient(2) = 1`. The identity is exactly
CRT bijectivity and needs `gcd(m,n) = 1`, which that plan explicitly said was
"not needed".

Nothing catches this. An executor finds a *structural* error by running the
proof — that has happened every time — but a false NUMERICAL claim survives
until someone re-runs the numbers, and the plan's confidence is the reason
nobody does.

**So: re-run a plan's numeric checks, do not inherit them.** They are ten
lines of Python and the plan already tells you which pairs to try. And when
writing a plan, state the check you ran as a command that can be re-executed,
not as a sentence claiming it passed.

## A generated artifact nobody compared against its source

- **A generated artifact's own `--check` existing is not the same as anyone
  running it.** `artifacts/autogenesis/kernel-dependency-projection-v1.json`
  is a sidecar over the constructed kernel with a real freshness check
  (`gen-autogenesis-kernel-dependency-projection.py --check`), but that check
  needs a debug kernel build costing tens of minutes, so it lived only in
  `scripts/check.sh` / `just check` — the aggregate gate nobody runs per
  merge — and in no pre-push hook. It drifted for **ten days** (2026-08-26 to
  2026-09-05) while `scripts/check-merge-hygiene.sh` printed
  `generated=current` on every merge in between, because that gate never
  asked: the committed projection indexed **1,644** declarations against
  **4,260** live on 2026-09-05, missing every `Nat.Finset.*`, `Nat.Hall.*`,
  `Nat.Subsets.*`, `CatS.*`, and `IntSpace.*` declaration. The fix (lane
  `kernel-projection-regen`) was not to run the expensive check more often —
  it stayed exactly as expensive — but to compare two numbers the gate
  already had on hand for free: the committed `census.declarations` against
  the live `declarations=N` count `shape_search` already prints for the
  duplicate-declaration guard, reused rather than re-measured. A cheap proxy
  comparison is not the real check, but an artifact with NO comparison at all
  is the failure mode this whole document is about, one arrow further
  upstream.



## A green summary line with a guard that has no subject

- **A gate that prints `PASS` and exits 0 can carry, inside that same line, a
  guard reading `skipped(tool-failed)` or `not-answerable`.** Measured
  2026-09-05 by the `incidence-geometry` lane: `check-merge-hygiene.sh` printed
  `...|shape_duplicates=skipped(tool-failed)|kernel_projection=not-answerable|PASS`
  with exit 0 while `shape_search --include-constructed` was panicking on its
  own coverage assertion (a prelude group indexed but not declared). Two guards
  had no subject, so neither could fail, and the aggregate verdict inherited
  their silence. The lane caught it by reading the summary fields, not the
  exit status.
- **Rule:** a guard whose subject did not load must set the aggregate verdict
  to FAILED, not to a field value the aggregate ignores. Until the script is
  changed, read every `=` field of the summary line before believing `PASS`;
  the coordinator's post-merge pass now greps for `skipped|not-answerable` and
  treats either as red.
