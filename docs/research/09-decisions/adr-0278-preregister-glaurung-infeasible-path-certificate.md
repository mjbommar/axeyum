# ADR-0278: Preregister one proof-carrying Glaurung infeasible-path verdict

Status: accepted
Date: 2026-07-19

Result state: accepted bounded downstream certificate attachment and external
check; implementation isolated from the primary Glaurung worktree

## Context

The reviewer checklist asks for one concrete downstream use of Axeyum's proof
surface: a Glaurung `infeasible path` verdict that owns and rechecks a DRAT
certificate. Axeyum already exports a source-bound QF_BV `UnsatProof` and has
established bounded interoperability with pinned upstream `drat-trim`
(ADR-0254--0258). Glaurung already contains an off-trait `prove_unsat` prototype,
but its success variant retains only a DRAT line count. It discards the proof,
calls only the clausal `recheck()` entry point, and is not a certificate-bearing
path verdict a consumer can save or recheck.

This is a downstream integration gap, not a request for a new proof calculus.
It must not reopen concretization-policy coverage, symbolic memory, GQ5 clause
optimization, or the full Alethe/Lean reconstruction track.

## Decision

In an isolated Glaurung worktree rooted at `403a5c5`, replace the unused
size-only prototype with one concrete-type, off-trait path contract:

- `InfeasiblePathVerdict::Infeasible(InfeasiblePathCertificate)` owns the exact
  Axeyum `UnsatProof`;
- feasible, inconclusive, and translation/export failure remain distinct and
  cannot be mistaken for infeasible;
- the certificate exposes byte-preserving DIMACS/DRAT/LRAT access for artifact
  export; and
- `recheck_for_path(pool, assertions)` retranslates the supplied Glaurung path
  and calls `UnsatProof::recheck_for_bool_terms`, thereby checking both the DRAT
  and exact deterministic source-to-CNF binding.

Keep the generic Glaurung `Solver` trait, ordinary `SolveResult`, authoritative
backend selection, warm reuse, branch scheduling, and finding semantics
unchanged. Proof generation remains an explicit second pass requested only for
a definite path-infeasibility claim; it is not added to every pruning solve.

Add a small Glaurung example that constructs one deterministic path conjunction
in the real `ExprPool`/`Assert` representation, requests the verdict, rechecks
the attached certificate against that same path, and writes
`problem.cnf`, `proof.drat`, optional `proof.lrat`, and a manifest into a new
output directory. This is a reproducible consumer demonstration, not a solver
benchmark or a claim that whole-function unreachability is certified.

## Tests and acceptance gates

Tests begin red and must establish all of the following before the external
cell runs:

1. a contradictory Glaurung path returns only `Infeasible(certificate)`;
2. the attached certificate rechecks against the original Glaurung path;
3. the same certificate returns false against a weakened satisfiable path,
   proving source binding rather than only self-consistent CNF/DRAT bytes;
4. a satisfiable path returns `Feasible` with no certificate;
5. unsupported/failed translation and proof-search inconclusive remain typed
   non-infeasible outcomes; and
6. the exporter refuses an existing output directory and writes files whose
   hashes and byte counts agree with its manifest.

Run focused Glaurung tests with `solver-axeyum`, strict Clippy on the affected
targets/features, and documentation/link checks available in each repository.
The primary dirty Glaurung worktree is not an implementation surface.

After those gates pass from committed source, execute the example exactly once
on its fixed path. Require:

- the example's source-bound in-tree recheck to pass;
- pinned upstream `drat-trim` revision
  `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`, binary SHA-256
  `c0b9bd6a2369918f171a42d024aa2993d5eff4f597e019850c073d0aa08bd9db`,
  to exit zero and print an exact `s VERIFIED` line for the emitted pair; and
- the same proof against the fixed satisfiable CNF `p cnf 1 0\n` not to meet
  that accepted-verification condition.

Retain exact source revisions, commands, hashes, sizes, exit codes, and checker
streams. Report whether the proof is trivial/input-refutable; do not promote a
nontrivial-proof or performance claim from this cell.

## Evidence before execution

Current Axeyum `e34b4f1e` provides `UnsatProof::recheck_for_bool_terms` and the
already pinned external checker. Current Glaurung `403a5c5` has the exact
`ExprPool` translator and off-trait prototype, with no call sites outside its
two focused tests. The primary Glaurung worktree has unrelated edits, selecting
an isolated worktree before implementation.

No output bundle from the new Glaurung consumer example exists, and no external
checker has observed its fixed path through that example.

## Observed result

Glaurung branch `codex/adr0278-infeasible-proof` implements the contract at
`f01a057` from base `403a5c5`. Four focused verdict tests cover exact-path
attachment/recheck plus weakened-path rejection, feasible-without-certificate,
expired-budget inconclusive, and translation error. Two example tests verify
manifest/file hashes and existing-output refusal. All 45 Axeyum-backend tests
pass; the no-default
`solver-axeyum` example builds and rustdoc completes. Strict Clippy reaches the
affected targets but is blocked by 70 pre-existing warnings across unrelated
Glaurung modules; no new-target diagnostic is reported.

The committed release example (binary SHA-256 `a7998ca9...c628`) emits one
source-rechecked two-assertion verdict. The retained bundle is under
[`bench-results/glaurung-proof-carrying-infeasible-path-20260719/`](../../../bench-results/glaurung-proof-carrying-infeasible-path-20260719/):
32 variables, 34 clauses, a 202-byte DIMACS file, two-byte/one-line DRAT, and
13-byte/one-line LRAT. Rechecking the same certificate against only `x == 5`
returns false.

Pinned `drat-trim` (binary SHA-256 `c0b9bd6a...9db`) accepts the emitted pair
with exit 0 and exact `s VERIFIED`. The same proof against the fixed satisfiable
CNF exits 1, reports `no conflict`, and prints `s NOT VERIFIED`. The exact
stream hashes and base64 bytes are retained in
[`result.json`](../../../bench-results/glaurung-proof-carrying-infeasible-path-20260719/result.json).

The proof is an empty-clause proof over a CNF already refutable from
complementary input units. Accept this as a concrete downstream attachment,
source-binding, and external-consumption result only—not as a nontrivial proof
trace, whole-CFG unreachability certificate, lowering proof, or performance
result.

## Alternatives

- Add proof data to the generic `Solver` trait: rejected because only Axeyum
  produces it and the existing Glaurung ADR-006 explicitly keeps v1 proofs on
  the concrete backend.
- Generate a proof for every ordinary UNSAT pruning check: rejected because it
  changes exploration cost and the measured solver topology. This slice is an
  explicit evidence request after a definite verdict.
- Call only `UnsatProof::recheck()`: rejected because that checks the stored
  CNF/DRAT pair but does not prove that a later consumer supplied the same
  Glaurung path.
- Claim whole-target unreachability: rejected because one path-conjunction
  certificate does not certify exhaustive CFG traversal.

## Consequences

The reviewer can run one Glaurung-native path query, inspect its
attached standard proof, rebind it to the exact path constraints, and check it
with an independent tool. The bounded result demonstrates the latent
deployability feature without changing normal exploration or making a broader
proof-completeness claim. Failure remains useful evidence and must not be
hidden by falling back to bare `Unsat`.
