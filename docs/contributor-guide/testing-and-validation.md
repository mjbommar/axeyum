# Testing and Validation

Validation in Axeyum is layered. A focused test answers whether the code you
changed behaves correctly; the pre-merge gate answers whether the complete
workspace contract still holds. Keep those evidence states separate.

## The validation ladder

Run the smallest useful gate while editing, then widen once at the integration
boundary:

| Stage | Purpose | Typical command |
|---|---|---|
| Single behavior | Fast regression feedback | `cargo test -p axeyum-solver --features full --test evidence` |
| Owning crate | Unit and crate integration behavior | `cargo test -p axeyum-solver --features full` |
| Changed scope | Map all touched paths to focused gates | `just check-scope origin/main` |
| Solving-path safety | Whole suite under a hard memory cap | `just test-guarded` |
| Pre-merge contract | All repository gates except `cargo deny` | `just check` |
| Dependency policy | Licenses, advisories, bans, sources | `just deny` |

Do not run `just check` after every edit. It includes workspace-wide Rust
checks, serialized capability frontiers, long CAS proof tests, generated
resources, parity checks, and documentation links. Use it once when the change
is ready to integrate.

## Rust changes

Choose a package and enable the feature surface that owns the code:

```sh
cargo test -p axeyum-rewrite
cargo clippy -p axeyum-rewrite --all-targets -- -D warnings

cargo test -p axeyum-solver --features full
cargo clippy -p axeyum-solver --features full --all-targets -- -D warnings
```

The solver's default feature set intentionally omits much of its multi-theory
surface. A solver test that is guarded by `feature = "full"` can otherwise
compile into an empty test binary and misleadingly exit zero. When selecting a
test directly, confirm its reported test count is nonzero.

Native Z3 differential tests require the `z3` feature and a usable native
library profile:

```sh
cargo test -p axeyum-solver --features z3 --test bv_differential_fuzz
```

An oracle agreement is evidence about verdicts, not a replacement for Axeyum's
own model replay or proof checker.

## Solver and dispatch changes

Solver, decider, admission, or dispatch changes must also run the serialized
capability frontier:

```sh
cargo test -p axeyum-solver --features full --test progress_frontier \
  --features full -- --test-threads=1
```

Run this test alone. Its ratchets are wall-clock-sensitive, so concurrent build
or test load can manufacture a false regression. It currently reports nine
tests; zero tests means the feature gate was omitted.

Use the guarded workspace suite when a new route could allocate aggressively:

```sh
just test-guarded
```

The default cap is 64 GiB and can be overridden with `MEM_LIMIT_GB`. A memory
limit, signal, or timeout is environmental/operational evidence—not a green
code result and not automatically a product regression.

## CAS proof changes

Ordinary `cargo test -p axeyum-cas` skips the order-255 certified moment proofs.
If you change moment, squared-binomial, or falling-factorial code, run:

```sh
just moment-proofs
```

The full `just check` chain includes this gate. Do not infer coverage from the
ordinary crate test alone.

## Documentation and generated resources

For Markdown-only edits, run:

```sh
./scripts/check-links.sh
python3 scripts/check-plan-authority.py
git diff --check
```

If documentation embeds or depends on generated foundational resources, also
run:

```sh
just foundational-resources
```

`docs/SUMMARY.md` is the mdBook navigation authority. A new public guide is not
complete until it is reachable from both its section index and `SUMMARY.md`.

## Deterministic and differential tests

Every new semantic or transformation surface should include the applicable
layers:

1. exact unit examples, including malformed and boundary inputs;
2. exhaustive small-domain checks where the domain is finite;
3. deterministic property/fuzz coverage with an explicit seed and bound;
4. differential comparison against an independent oracle where one exists;
5. satisfying-model replay against the original, pre-transformation query;
6. independent UNSAT proof/certificate checking, or an explicit trust-ledger
   limitation; and
7. a retained near-miss or satisfiable control so an always-rejecting route
   cannot appear sound.

For operators and rewrites, the [foundational DAG](../research/08-planning/foundational-dag.md)
lists the layer-specific obligations. For definitive results, use
[Proof and evidence obligations](proof-and-evidence-obligations.md).

## Formatting without taking another lane's work

In an isolated owned worktree, these are safe final checks:

```sh
cargo fmt --all --check
git diff --check
```

If a shared worktree contains another lane's edits, do not run a workspace-wide
formatter that could rewrite their files. Format only the Rust files you own,
then audit the diff. Never stage unrelated formatting.

## Pre-merge sequence

From a clean topic branch based on the intended integration ref:

```sh
git status --short --branch
just check-scope origin/main
just check
just deny
git diff --check
```

Then inspect what will be published:

```sh
git log --oneline origin/main..HEAD
git diff --stat origin/main...HEAD
```

The repository's pre-push hook may run an additional exact-pushed-SHA gate.
Do not call a push complete until that hook exits zero and the remote ref is
verified. Hosted CI is a separate evidence state; a queued or running workflow
is not green.

## Stop conditions

Stop and diagnose before merging when any of these occurs:

- `expected unsat, got sat` or any other wrong definitive verdict;
- a satisfying model does not replay against the original query;
- a proof or certificate fails its independent checker;
- a deterministic test changes across identical runs;
- a required test binary reports zero tests;
- generated output changes but its source or generator did not;
- a new unsupported/resource case crashes, hangs, or guesses instead of
  returning structured `unknown`/`Unsupported`; or
- the branch contains paths owned by another lane.

