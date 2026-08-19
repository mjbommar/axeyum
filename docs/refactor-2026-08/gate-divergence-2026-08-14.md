# The two aggregate gates have diverged

Measured 2026-08-14, coordinator lane. Hand-off for task #4 (gate scope).

> **RE-MEASURED 2026-08-19. Two of this document's conclusions no longer hold,
> and one of them inverted.** The numbers below (112 / 61) are five days stale;
> the parity check this document proposed is built; the omission it called "the
> worst possible" is closed. But the *completeness* ordering it implies —
> `just check` broad, `check.sh` narrow — reversed, for a reason nobody here
> anticipated. The corrections are at the foot of the file; the reasoning in
> between still holds and is why the fix took the shape it did.

## What CLAUDE.md promises

> `just check` — fmt + clippy + test + doc + foundational resources + docs link check (**preferred**)
> `./scripts/check.sh` — **same aggregate gate** without `just` (fresh-machine fallback)

`scripts/check.sh`'s own header repeats it: *"Mirrors the `check` recipe in the
justfile; keep the two in sync."*

## What they actually run

Authoritative expansion — `just -n check` (note: `just -n` writes the expanded
command list to **stderr**, so `2>/dev/null` makes it look empty; that cost one
wrong measurement before this one):

```sh
just -n check 2>&1 | grep -oE 'scripts/[^ ]+\.(py|sh)|scripts\.tests\.[a-z_0-9]+' | LC_ALL=C sort -u
```

| gate | script steps |
|---|---|
| `just check` | **112** |
| `scripts/check.sh` | **61** |

They are not the same gate, and the difference is not a rounding error.

**2026-08-19, from `scripts/check-aggregate-scope.sh` — the parity check this
document asked for, now built:** `check.sh` runs **203** steps, `just check` runs
**278**, and **97** steps exist on one side only. The gap grew; the shape did
not.

## Each is missing something the other has

**53 steps run by `just check` and skipped by `check.sh`.** The ones that matter
most, given what this project claims:

| skipped by `check.sh` | what goes unchecked |
|---|---|
| `gen-lean-axiom-ledger.py --check` | the **axiom ledger** — SHA-256-bound canonical types for all 30 prelude axioms, and since ADR-0465 every published count, including the citations in ten documents. Axiom-freedom is the headline metric; on `check.sh` nothing binds it. |
| `check-parity-docs.py` | Z3/Lean parity claims vs. measured evidence |
| `gen-proof-gap-matrix.py`, `gen-proof-gap-shape-census.py` | the proof-gap inventory |
| `gen-scoreboard.py`, `gen-measurement-provenance.py` | published numbers vs. their provenance |
| `check-qfbv-profile.sh`, `check-glaurung-qfbv-regular.sh`, `check-reflection-semantics-gate.py` | performance and semantics gates |
| `cargo test -p axeyum-cas --lib -- --ignored` | the CAS ignored-test tier |
| 17 `test_glaurung_*` / `test_analyze_*` suites | the benchmark analysis layer |

**2 steps run by `check.sh` and skipped by `just check`** — and one is the worst
possible omission:

| skipped by `just check` | what goes unchecked |
|---|---|
| `check-gate-liveness.sh` | **the gate-liveness ratchet.** The check that proves the other gates still execute something. It exists precisely because the corpus `:status` sweep sat inert for 15 days, printing `running 0 tests ... ok` and exiting 0. It is absent from the command CLAUDE.md calls *preferred*. **Closed:** `gate-liveness` is dependency #20 of `just check`'s 41 as of 2026-08-19 (`justfile:58`, `:410`) and `scripts/check.sh:237`. |

Also divergent, unrelated to scripts: `just check` pins `cargo +stable clippy`,
`check.sh` uses the ambient toolchain (nightly here); `just check` wraps the
memory-hungry Lean steps in `MEM_LIMIT_GB=4 ./scripts/mem-run.sh`, `check.sh`
does not.

## Why this is the same defect class the repo already documents

CLAUDE.md's own Gotchas: *"Tools in this repo have lied more often than the
solver has been weak."* This is that, one level up. An agent told to run the
fallback gate believes it ran "every gate CI runs" — the file says so — while
skipping 53 steps including the one binding the axiom inventory. An agent told
to run the preferred gate skips the ratchet that detects inert gates.

Neither command is wrong about its exit status. Both are wrong about their
scope, and scope is what a gate's user is actually relying on.

## Suggested shape of the fix (task #4 owns the call)

Do not hand-sync two lists — that is what produced this. Make one authoritative:

1. Define the step list **once** (a data file, or make `check.sh` the single
   implementation and have the justfile recipe call it).
2. Whichever survives, have it **print its own scope**: the step count it is
   about to run, and a failure if that count drops below a committed floor.
   A gate that reports scope cannot silently shrink.
3. Add a parity check between the two entry points so divergence is a gate
   failure, not a discovery.

Point 2 generalizes the existing `check-gate-liveness.sh` idea from "does a
suite run any tests" to "does the aggregate gate run all its steps.

## What happened to points 1–3 (measured 2026-08-19)

**Point 3 was built and is doing its job.** `scripts/check-aggregate-scope.sh`
compares the two entry points step by step against a pinned
`check-aggregate-scope.expected`, and divergence is now a gate failure rather
than a discovery. It runs in both gates.

**Point 1 was not taken, and the divergence is larger, not smaller.** The step
list is still defined twice. `check-aggregate-scope` currently exits 1 on **32**
steps that `main` ships and that are recorded as accepted in *neither* gate. The
deliberate decision is to wire those 32 into both gates rather than re-pin the
expectation file — re-pinning is the move that turns a ratchet into a rubber
stamp.

**Point 2's premise turned out to be the smaller half.** A gate that reports its
scope still cannot report the scope of a *chain* it is a link in:

> **`just` aborts the whole dependency chain at the first failure.**

`aggregate-scope` sat at **#18 of `just check`'s 41 dependencies** and is red
(the 32 above). So `just check` died at #18 and **23 gates never ran** — `test`,
`frontier`, `gate-liveness`, `lean-gate`, `doc` among them. `scripts/check.sh`
does not abort; it accumulates `fail=1` and runs all of its steps.

**That inverts this document's implied ordering and CLAUDE.md's.** For as long as
`aggregate-scope` was red and early, the no-`just` **fallback was the more
complete gate**, and an agent that ran the *preferred* command got 17 of 41
links. The step counts above (278 vs 203) measure what each gate *would* run, not
what `just check` did run.

Fixed in `51fdc0ae6` by moving the three gates whose red state is expected and
slow to clear — `aggregate-scope`, `adr-remote-collisions`, `local-ci-freshness`
— to positions #39–#41. The chain still fails and each still reports; it stops
one expected-red gate hiding the other 23.

Two lessons this document did not have:

- **Ordering is part of a gate's scope.** A gate's position in an aborting chain
  determines how much of the chain is observable, and nothing in a step count
  shows it. Expected-red gates belong at the tail.
- **A tail position is not self-maintaining.** `adr-remote-collisions` was
  *believed* to be last and was #40, so `local-ci-freshness` behind it was masked
  whenever it failed. That was found by expanding the recipe and counting, not by
  reading it.

The full 2026-08-18/19 gate findings, including the three that are still open,
are in [`04-gates-and-truth.md`](04-gates-and-truth.md) G4–G8 and T1/T2/T5."
