# 04 — Gates that prove their scope, documents that match the code

**The finding.** In one day, three gates were found reporting success over work
they were not doing, and one whole class of guard was found to exist only in
prose. **None was found by running the gates.** Every one surfaced because
somebody measured something adjacent.

This is the cheapest item in the folder and it protects the other three: a
refactor guarded by gates that cannot say which files they examined is not
guarded.

## The three gate-scope holes

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

Found during another lane's final verification. Unfixed.

### G3 — the claims validator collapsed 228 errors into one message

`novelty` was missing from the schema, so 62 claims failed on a single message
that **masked 228 real errors underneath** — malformed generator paths, refs
asserted `resolved: true` with no `graph_pin`, and stray CNF files no evidence
row named. Fixed; the 228 were then repaired.

The detail worth keeping: the masking field was `novelty`, added *that same
session* to stop a label going unchecked. **The fix and the failure were the same
commit.** Two gates disagreeing about a schema is not something either can detect
alone, which is the entire argument for running both.

## The prose-guard class

A guard that exists in a comment and not in code. Four instances, four crates,
one day:

| where | form |
|---|---|
| `axeyum-lean-kernel` `lean_pp.rs:214-216`, `:420-421` | a "defensive guard" documented twice, **never implemented** — `render_real_inductive` performs no flatness test at all |
| `axeyum-search` symmetry breaking | soundness condition (colour interchangeability) unstated in the interface → a demonstrated **wrong `unsat`**: `S(3;3,4,5)` at `n=41` is satisfiable and the stock encoding called it `unsat` |
| `axeyum-rewrite` manifest | `precondition` is a `String`, presence-checked only — 57 rules, and the prose field was the only per-rule field carrying applicability, and the only one nothing read |
| `axeyum-search` `colouring.rs:10` | cites `tests/encoding_parity.rs`, which **does not exist** |

Three are fixed. The fourth is [`02`](02-composition.md) W3.

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

And there are **455 ADRs**. That is a governance surface nobody can hold in
their head; the ADR index README is also a shared append point that two lanes
clobbered on the same day.

## The work

### T1 — Every gate reports its own scope

A gate should print what it examined, not only whether it passed.
`check-fmt-complete.sh` prints `checked 881 files`; the claims checker prints
`103 claims re-checked, 0 errors, 24 row(s) not re-checked here`. That last
clause is the model: **it names what it could not verify instead of passing it
silently.** Bring the clippy and test gates to the same standard, starting with
G2.

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

### T3 — Make the architecture document true, or shrink it to what is true

Twelve undocumented crates including the second-largest is not a documentation
debt, it is a map that would mislead a new contributor about where half the
system is.

### T4 — Stop the shared-append-point collisions

`PLAN.md` and the ADR index README were clobbered by concurrent lanes **four
times** in one day. Pathspec discipline does not help: it prevents sweeping
files you did not touch, not two lanes legitimately touching the same file. The
session protocol *instructs* every lane to edit `PLAN.md`, so the instruction is
the defect. Either give status its own per-lane files with a generated index, or
accept collisions and make attribution recoverable — every commit in this
checkout carries the same git author, so `git log` attribution is currently
impossible without an `Agent:` trailer.
