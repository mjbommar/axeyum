# Two gaps the aggregate-gate sweep exposed (2026-08-29)

Running `scripts/check.sh` in full — for the first time in a while, after a day
of narrow re-verification — found **16 failed steps**. Twelve were fixed. Two of
the remainder are not gate bugs at all; they are real defects the gates were
correctly reporting.

## 1. A 96 MB Lean module for a trivial unsat query

`scripts/check-lra-hypothesis-binding.py` crashes deterministically on
`artifacts/examples/math/number-theory-v0/smt2/diophantine-gcd-obstruction-conflict.smt2`
— the query `14x + 21y = 5`, unsat because `gcd(14,21) = 7 ∤ 5`.

`crates/axeyum-solver/src/int_reconstruct/diophantine.rs`'s Lean-module
renderer emits **96 MB** for it, over the checker's 64 MB safety cap. Confirmed
pre-existing (`crates/` and the query byte-identical at `HEAD` vs `origin/main`)
and reproduced standalone.

**Why this matters more than a crashed gate.** The obstruction here is one
divisibility fact. A proof that "7 does not divide 5" should be bytes, not
megabytes. Whatever the renderer is doing, its output size is not tracking the
argument's difficulty — and this is the *reconstruction* path, the trusted side.
The lane that found it deliberately did not raise the cap or reclassify the pin,
because either would make the gate pass by hiding the defect. That was right.

## 2. `depends_on` drift recurs on every fact landing, and nothing emits the edges

`scripts/check-fact-depends-derived.py` verifies that a fact's `depends_on`
names every fact whose theorem its own proof term directly uses. Its own error
text states the principle: *"The dependency is in the proof term; the ledger
should not have to be told separately."*

But nothing derives them. A lane lands a fact, writes `depends_on` by hand or
omits it, and the gate goes red later:

- earlier today: **1054 missing edges across 306 facts**, 182 fact-touching
  commits since it was last green on 2026-08-25;
- and again within the hour: **109 more edges across 25 facts**, purely from the
  Int and Nat families landed since that repair.

Both repairs were mechanical — parse the checker's own error output, add the
named edge. Neither needed judgment. That is the signature of work that belongs
in a producer rather than in a periodic cleanup.

**The cost is not just the cleanup.** `create-autogenesis-chain-catalog.py`
consumes the same graph, so it went red for the same reason and had to be
re-run after the repair. Any consumer of the fact DAG inherits the drift.

**The fix is a `--fix` mode, not a lint.** The checker already computes exactly
the edges that are missing and prints them in a parseable form. Emitting them
should be one flag away, and then wired so a lane cannot land a fact without
them.

One constraint learned today: patch the `depends_on` array by **surgical text
substitution**, never a JSON re-dump — a lane found the re-dump reformats
unrelated compact arrays across the file, and reverted it before committing.

## Also left open, and NOT mechanical

- `autogenesis-nursery`: today's `depends_on` repair **exposed 3 real
  train/development dependency crossings** that were always latent and
  invisible. Fixing needs an ADR-0542 family move — judgment, not mechanics.
- `development-partition`: a real operation-authored-against-development
  violation whose only sanctioned remedy, the nursery amendment ledger, is
  hard-blocked by another gate's explicit held-out-only rule. **Two gates in
  genuine conflict.** The lane correctly refused to fabricate train coverage;
  this needs an ADR, not a patch.
