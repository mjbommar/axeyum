# The two aggregate gates have diverged

Measured 2026-08-14, coordinator lane. Hand-off for task #4 (gate scope).

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
| `check-gate-liveness.sh` | **the gate-liveness ratchet.** The check that proves the other gates still execute something. It exists precisely because the corpus `:status` sweep sat inert for 15 days, printing `running 0 tests ... ok` and exiting 0. It is absent from the command CLAUDE.md calls *preferred*. |

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
suite run any tests" to "does the aggregate gate run all its steps."
