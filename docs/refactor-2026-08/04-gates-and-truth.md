# 04 — Gates that prove their scope, documents that match the code

**The finding.** In one day, three gates were found reporting success over work
they were not doing, and one whole class of guard was found to exist only in
prose. **None was found by running the gates.** Every one surfaced because
somebody measured something adjacent.

**Re-measured 2026-08-18/19: five more, and the class had climbed.** The three
below are gates blind to *files*. The five added since are gates blind to their
own *findings* — the ADR-identity check printing a duplicate and exiting 0, a
mutation harness scoring a non-compiling mutant as a kill, the axiom-freedom
measurements run by no gate at all, the "authoritative" CI script that had never
executed on any host, and `just check` aborting at dependency #18 so that 23
gates never ran. Same shape, and the last two mean the *aggregate* gates were
themselves in scope. Not one of them was found by running the gates either.

This is the cheapest item in the folder and it protects the other three: a
refactor guarded by gates that cannot say which files they examined is not
guarded. The 2026-08-19 corollary: **a gate that cannot say what it found is not
a gate**, and a green aggregate is worth exactly the fraction of its chain that
ran.

## The gate-scope holes

Three on 2026-08-14 (G1–G3); five more on 2026-08-18/19 (G4–G8), by which
point the class had reached the gates over this project's headline claim.

### G1 — `cargo fmt --all --check` was blind to 44% of the workspace's files

`mod reconstruct;` sits inside `macro_rules! full_modules`, and **rustfmt does
not expand macros**. So `axeyum-solver`'s module tree — **156 modules /
221,445 lines, including the entire trusted proof-reconstruction layer** — was
outside the formatting gate for the life of the crate. Fourteen source files had
never been formatted while `just check` reported success.

Reproduced both directions, appending a malformed function to
`crates/axeyum-solver/src/reconstruct/resolution.rs`:

```
cargo fmt --all --check         EXIT=0   file never mentioned
rustfmt --check <that file>     the probe, twice
```

**Fixed** by `scripts/check-fmt-complete.sh`, which enumerates from the
filesystem (881 files) rather than from the module graph, wired into
`scripts/check.sh` and `just check`. Both gates are kept deliberately: they fail
for different reasons, and a disagreement between them is itself a finding.

### G2 — `cargo clippy` exited 0 over a **cached** example carrying a warning

Found during another lane's final verification. **Fixed since this was written**,
and the "Unfixed" here was stale by 2026-08-19: `scripts/check-clippy-complete.sh`
is now the gate in *both* entry points (`justfile:326`, pinned
`--toolchain stable`; `scripts/check.sh:179`), and it reports how many workspace
targets it examined instead of exiting 0 over a cache.

The underlying mechanism is not fixed and cannot be — cargo decides freshness by
mtime — so it still bites anything that reads a warm `target/`. That is what
`scripts/check-source-freshness.sh` and `scripts/lane-snapshot.sh` are for; see
[`06`](06-scratch-and-snapshots.md).

### G3 — the claims validator collapsed 228 errors into one message

`novelty` was missing from the schema, so 62 claims failed on a single message
that **masked 228 real errors underneath** — malformed generator paths, refs
asserted `resolved: true` with no `graph_pin`, and stray CNF files no evidence
row named. Fixed; the 228 were then repaired.

The detail worth keeping: the masking field was `novelty`, added *that same
session* to stop a label going unchecked. **The fix and the failure were the same
commit.** Two gates disagreeing about a schema is not something either can detect
alone, which is the entire argument for running both.

### G4 — the ADR-identity gate printed the defect and exited 0 (2026-08-19)

`python3 scripts/gen-adr-index.py --check` emitted

```
ADR_INDEX|rows=523|curated_summaries=445|duplicate_numbers=0166,0167,0455
```

and **exited 0**. The field was printed and the exit status ignored it, so
`duplicate_numbers=none` and `duplicate_numbers=…,0455` were indistinguishable to
every gate that ran it. Found by planting a second `adr-0455-*` file — i.e. by
attacking the checker, not by running it.

Fixed in `f63b94191`: any duplicate outside `GRANDFATHERED_DUPLICATES` (`0166`,
`0167`, which predate the check on both sides of every branch) fails, and
**repairing a grandfathered one without delisting it also fails**, so the
allowlist can only shrink deliberately. Both directions were demonstrated, not
asserted. Re-measured here 2026-08-19: real tree, `duplicate_numbers=0166,0167`,
exit 0.

### G5 — the mutation harness scored a mutant that never compiled as a kill (2026-08-18)

The harness that enforces T2's rule ("delete one guard, require exactly one test
dies") classified **a mutation that failed to build** — and a suite that executed
**zero tests** — as deaths, because both present as "the run was not clean".
Every `exactly one test died` in this repository's history rested on the mutant
having been built and run, and nothing checked either.

`scripts/tests/mutation_controls.py` now reports a closed set of outcomes, of
which only the first two are measurements: `killed N`, `SURVIVED`,
`DID NOT BUILD`, `DID NOT RUN`, plus `NOT APPLIED` / `AMBIGUOUS ANCHOR` /
`INCONSISTENT`. Each is demonstrated live by `mutation_controls.py self-demo`
rather than described. Survivors and unmeasured mutations are counted
**separately**, because "the guard is not tested" and "the harness could not
tell" are different failures with different fixes.

It immediately found one: the `lean-axiom-ledger` control — the SHA-256 binding
of every prelude axiom type, i.e. the evidence for the axiom-freedom claim — was
recorded as **11 guards, no survivors** and is really **10**. The eleventh
deleted a flag the fixture needs, so the suite died at `setUpClass`, printed
`Ran 0 tests`, and the old classifier read the nonzero exit as a death
(`445750aee`).

### G6 — the axiom-freedom measurements were run by no gate at all (2026-08-18)

`real: axiom=30` is the whole remaining trusted surface, and the claim that the
shipped front door no longer reaches it rested on three examples. Grepped across
`scripts/`, `justfile` and `.github/workflows/`: **zero invocations**, while
ADR-0480 and ADR-0486 both cited them as evidence. They were lane-run commands
that had happened to be run once, by the lane that wrote them.

This is [`README`](README.md) finding 8 arriving at the gate layer: the ledger's
checkers were audited and repaired, and the *gate* over the same claim did not
exist. Now four steps in `scripts/check.sh:214-220` and a `just check`
`axiom-freedom` recipe at dependency #7 (`justfile:38-`):

```
front_door_carrier      --require-axiom-free
ring_interface_pin      --require-identical
ordered_ring_refutation --require-empty
ordered_ring_refutation --constructed-reals
```

Each `--require-*` flag is what makes the exit status depend on the finding —
gating a command whose status does not is the defect, not the remedy. Verified by
pointing `lra_ctx()` back at the axiomatized package in an isolated snapshot:
exactly one of the four verdicts flipped, the one asking about the *shipped*
route. Three staying true under that mutation is the check being well aimed, not
weak.

### G7 — the gate hosted CI calls authoritative for `main` had never run (2026-08-18)

`scripts/local-ci.sh` could not run on any fleet host: `cargo nextest` exit 101
(no such command) and `rustup run 1.88.0` exit 1 (toolchain not installed). It is
now runnable, with a preflight that **refuses rather than limps** — the failure
mode a missing-tool fallback produces is the inert gate, G1 through G6 all over
again — and `--record` writes a tracked per-(sha,host) JSON under
`artifacts/local-ci-runs/`.

The first completed run failed with four real defects. The second, read from its
own record rather than from prose:

| | |
|---|---|
| `artifacts/local-ci-runs/57af69142-s4.json` | `verdict PASS`, `rc 0`, finished `2026-08-19T01:02:02Z` |
| steps | 5, summing **6,656 s** |
| `cargo nextest run --profile local --workspace --all-features` | **7,561 tests**, 6,588 s |
| `cargo test --workspace --all-features --doc` | **179 doctests**, 20 s |

`scripts/check-local-ci-freshness.sh` is ENFORCING in both aggregate gates on
that record: stale (>48 h), failing, vacuous or unreadable reds the gate. That is
the cadence a full battery deserves — daily, not per git round.

**Still open, measured 2026-08-19 while writing this.** The record the gate
enforces has **five** steps; `scripts/local-ci.sh` has had a **sixth** since
`69f2cffb8` (07:55, the capability frontier ratchet, which left `hooks/pre-push`
precisely *because* local-ci runs it). The record predates the step. So
`check-local-ci-freshness.sh` reports `PASS -- fresh, ancestor, all-pass` over a
run in which the ratchet did not execute. Freshness of a record is not coverage
by it, and the freshness checker cannot currently tell the difference.

### G8 — one red gate at #18 was stopping 23 gates from running (2026-08-19)

`just` aborts the whole dependency chain at the first failure. `aggregate-scope`
sat at **#18 of 41** and is red, so `just check` died there and 23 gates —
including `test`, `frontier`, `gate-liveness`, `lean-gate` and `doc` — never ran.
`scripts/check.sh` does not abort; it accumulates and runs every step.

**So the no-`just` FALLBACK was the more complete gate, which is the inverse of
what CLAUDE.md says about the two.** Fixed in `51fdc0ae6` by moving the three
gates whose red state is expected and slow to clear to the tail; verified here by
expanding the recipe before and after:

```
before 51fdc0ae6:  #18 aggregate-scope … #40 adr-remote-collisions  #41 local-ci-freshness
after:             #18 test  #19 frontier  #20 gate-liveness …
                   #39 aggregate-scope  #40 adr-remote-collisions  #41 local-ci-freshness
```

That also corrected a belief held while doing it: `adr-remote-collisions` was
*already* thought to be last, and was #40, so `local-ci-freshness` behind it was
masked whenever it failed. The intent had never been realized.

This hides nothing — the chain still fails and each gate still reports. It stops
one expected-red gate hiding everything else.

## Where the batteries run now (2026-08-19)

G7 is only worth having if something moved *into* it, and something did. Three
steps were 92% of a 545 s uncontended `hooks/pre-push`, and two of them are full
batteries `scripts/local-ci.sh` already ran. Both left the hook in `928baec78`:

| step | why it left |
|---|---|
| `cargo test --workspace --lib` | 218 s at its last honest measurement and **2,699 s** in a real push once `axeyum-lean-kernel`'s lib tests grew — and DOUBLE-CHARGED, because the kernel step ran `-p axeyum-lean-kernel` wholesale, which includes the same `--lib` tests |
| capability frontier ratchet | 200 s, and moving it makes it **stronger** |

The ratchet is the interesting one, and it is a gate-scope argument rather than a
performance one. It measures *the largest N decided within a fixed wall-clock
budget*, so contention does not slow it — it **corrupts** it. The same commit on
the same box has scored 35 (load 34), 39 (load 5.4) and 40 (idle). It self-marks
NOT COMPARABLE or ADVISORY ONLY when the frame moves, so in a hook running beside
several lanes it paid full price for a verdict it then declined to enforce. In
`local-ci.sh` it runs serialized with `--test-threads=1`, which is what makes its
numbers comparable at all.

**Neither became optional; both moved from every-push to must-have-run-recently**
— which is the cadence a full battery deserves, and which is exactly why
`check-local-ci-freshness.sh` had to become enforcing rather than advisory, and
exactly why the coverage gap noted under G7 matters.

Both vacated places carry the reasoning: what the step caught, why it existed,
and where it runs now. That is not politeness. **A reader who finds a gate simply
gone will re-add it**, and the comment is the only record of why it was there.

## The prose-guard class

A guard that exists in a comment and not in code. Four instances, four crates,
one day:

| where | form |
|---|---|
| `axeyum-lean-kernel` `lean_pp.rs:214-216`, `:420-421` | a "defensive guard" documented twice, **never implemented** — `render_real_inductive` performs no flatness test at all |
| `axeyum-search` symmetry breaking | soundness condition (colour interchangeability) unstated in the interface → a demonstrated **wrong `unsat`**: `S(3;3,4,5)` at `n=41` is satisfiable and the stock encoding called it `unsat` |
| `axeyum-rewrite` manifest | `precondition` is a `String`, presence-checked only — 57 rules, and the prose field was the only per-rule field carrying applicability, and the only one nothing read |
| `axeyum-search` `colouring.rs:10` | cites `tests/encoding_parity.rs`, which **does not exist** |

**All four are now fixed.** The fourth — `colouring.rs:10` citing a
`tests/encoding_parity.rs` that did not exist — was closed on 2026-08-16 by
writing the test rather than deleting the claim, which is the direction
[`02`](02-composition.md) W3 required. Worth recording how it ended: the two
encoders agreed byte for byte on the very first run, and the Python generator of
record agreed with both. **The invariant was true the whole time; only the guard
was missing.** That is the good outcome, and it is also the one that makes a
prose-only guard so easy to leave in place — nothing was ever visibly wrong.

**The rule this yields**, and it is worth stating as policy: *if a comment
describes a check, either the check exists or the comment goes — in the same
commit.* A precondition in a doc comment is a wrong-`unsat` waiting for the first
caller that violates it.

## Documents that do not match the code

`docs/internals/architecture.md` is 82 lines and documents **11 of 23 crates**.
Undocumented: `axeyum-cas` (**47,472 lines, the second-largest crate in the
workspace**), `axeyum-verify`, `axeyum-strings`, `axeyum-fp`, `axeyum-search`,
`axeyum-scenarios`, `axeyum-bench`, `axeyum-evm`, `axeyum-property`,
`axeyum-property-macros`, `axeyum-verify-macros`, `axeyum-wasm`.

There were **455 ADRs** when this was written. Measured 2026-08-19,
`python3 scripts/gen-adr-index.py --check` reports `rows=523`. That is a
governance surface nobody can hold in their head; the ADR index README was also a
shared append point that two lanes clobbered on the same day.

The *file* no longer collides — it is generated from each ADR's own front matter
([`00`](00-parallel-work.md)). The **numbers** still do, three times in two days
across checkouts, and that is a different defect with no structural fix yet
(T5).

## The work

### T1 — Every gate reports its own scope

A gate should print what it examined, not only whether it passed.
`check-fmt-complete.sh` prints `checked 881 files`; the claims checker prints
`103 claims re-checked, 0 errors, 24 row(s) not re-checked here`. That last
clause is the model: **it names what it could not verify instead of passing it
silently.** Bring the clippy and test gates to the same standard, starting with
G2.

**Partly delivered, and the delivery exposed the next layer.** G2 is done
(`check-clippy-complete.sh` reports its target count) and `scripts/local-ci.sh`
records per-step test counts, which is how G7's `7,561` and `179` above are
numbers rather than adjectives. What T1 did not anticipate is that a gate can
report its scope honestly and still be enforced through a *record* that does not
cover it — G7's open item. Scope-reporting binds a gate to what it ran; nothing
yet binds a downstream check to which gate-version produced the record it reads.

The parity check that generalises this is built: `scripts/check-aggregate-scope.sh`
compares the two entry points step by step. Measured 2026-08-19 it reports
`check.sh runs 203 steps, just check runs 278; 97 step(s) exist on one side only`
and fails on the **32** that are recorded as accepted in neither. Those 32 are
inherited from `main` and are the reason G8 happened. **Still open**, and
deliberately: the fix is to wire them into both gates, not to re-pin
`scripts/check-aggregate-scope.expected`, which is a ratchet whose whole value is
that raising it is a deliberate act.

### T2 — Sweep the prose-guard class mechanically

`grep` doc comments on public API for "guard", "only", "must be", "assumes",
"ensures", and check each against the code. Generalise `axeyum-rewrite`'s
`PreconditionGuard` so a satisfiability-preserving transform carries its
precondition **where it is applied**, not beside it.

**The trap to respect:** one lane tried five candidate negative controls and
only one flipped; another found **six of seven guards removable with every test
still green**, because they all rejected through one shared check. A control
chosen carelessly passes while testing nothing. Delete one guard at a time and
require that each deletion kills exactly one test.

**That rule is now machinery, and G5 shows the rule alone was not enough.**
`scripts/tests/mutation_controls.py` does the deletions; `python3
scripts/tests/mutation_controls.py <suite>` runs one. But "a test died" is not
observable from an exit status, so the harness distinguishes `killed N` and
`SURVIVED` (measurements) from `DID NOT BUILD` and `DID NOT RUN` (not results) —
without which a mutant that broke the subject counted as coverage. Read the
outcome, never the exit status of the mutated run.

**Coverage, measured 2026-08-19:** six suites are registered — `adr-index`,
`plan`, `fact-derived-numbers`, `lean-axiom-ledger`, `lra-hypothesis-binding`
(each a Python generator/checker with its `unittest` module) and `fp-width-guard`
(`cargo test -p axeyum-fp --test width_guard`, the one Rust subject). **No
`axeyum-lean-kernel` suite is registered**, so the crate carrying the trusted
proof surface has its guards asserted rather than mutation-checked. That is the
next item here, and it is the crate where the rule matters most.

### T3 — Make the architecture document true, or shrink it to what is true

Twelve undocumented crates including the second-largest is not a documentation
debt, it is a map that would mislead a new contributor about where half the
system is.

### T4 — Stop the shared-append-point collisions — **done for the files**

`PLAN.md` and the ADR index README were clobbered by concurrent lanes **four
times** in one day. Pathspec discipline does not help: it prevents sweeping
files you did not touch, not two lanes legitimately touching the same file. The
session protocol *instructs* every lane to edit `PLAN.md`, so the instruction is
the defect. Either give status its own per-lane files with a generated index, or
accept collisions and make attribution recoverable — every commit in this
checkout carries the same git author, so `git log` attribution is currently
impossible without an `Agent:` trailer.

**Both were taken.** `PLAN.md` and the ADR index are generated views over
per-lane sources, and the `Agent:` trailer is enforced by `hooks/commit-msg`; see
[`00`](00-parallel-work.md) for the mechanism and for the three *further*
incident classes found on 2026-08-18/19, which the file-level fix does not
address.

### T5 — ADR **numbers** are still a shared append point, and this one is unbuilt

T4 removed the collision from the index *file*. The numbers underneath it
collided **three times in two days** across checkouts, each renumber moving the
collision rather than escaping it — twice because the renumbering side took the
local maximum, which is exactly the number the other checkout had also taken.

Two checks exist and neither subsumes the other:

- `--check-remote` detects a collision **pre-merge**. It is *structurally* blind
  afterwards: it flags a number only when EACH side has a file the other lacks,
  and after a merge the local tree holds both, so remote-only is empty.
- `--check` (G4) detects duplicates in the tree, which is the post-merge case,
  and until 2026-08-19 it exited 0 while printing them.

**The real fix is non-sequential allocation** — a number nobody can arrive at by
taking a maximum — and it is not built. Until it is, read
`git ls-tree -r --name-only origin/main docs/research/09-decisions/` for a free
number rather than taking the local maximum, which is what the error message now
says.
