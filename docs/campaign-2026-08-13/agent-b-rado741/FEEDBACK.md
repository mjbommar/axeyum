# agent-b feedback to the axeyum roadmap

Written while closing `R_4(5(x-y)=4z) = 741` with `crates/axeyum-search`.
Self-contained: everything needed to act on an item is in the item, cited by
file. Line numbers are as of commit `9d85b067` (the adaptive-cover commit)
unless stated otherwise.

The two items the next phase is meant to consume are **1** (route A for tree
covers) and **5** (branch-point selection). Both are written as specifications,
not as complaints.

---

# 1. Route A composition does not survive an adaptive cover

## Why it matters

`R_4(5(x-y)=4z) = 741` currently rests on **four checked obligations plus a
meta-argument**: *checked refutations of every cube of a complete cover imply
`F` is unsatisfiable*. The argument is short and true, and all four of its
premises are machine-checked — but the implication itself is not a step any
checker verified. It is the last place in the result where a reader trusts an
argument rather than a certificate.

Route A removes it: one DRAT proof of the **original** formula, whose
acceptance by `check_drat`/`check_drat_backward` discharges the whole thing.
`compose::compose_cover_proof` already does this for a flat product cover.
The adaptive covers that can actually finish hard instances are trees, and it
does not handle them — so exactly the instances that need route A most cannot
have it.

## Where it breaks today

`crates/axeyum-search/src/compose.rs`, the collapse loop:

```rust
for level in (0..plan.depth()).rev() {
    for code in 0..plan.prefix_count(level) {
        let prefix = plan.prefix(level, code)?;
        ...
        composed.push(DratStep::Add(clause));
    }
}
```

It enumerates *every* prefix at *every* level, which is correct only if every
leaf sits at full depth. Given a tree cover it would emit `R(p)` for internal
nodes whose children are cubes at mixed depths, in an order unrelated to the
tree, and would also emit `R(p)` for nodes strictly below a leaf cube — nodes
that have no proof segment behind them. Some of those steps are not RUP, and
the composed artifact is rejected. (Rejected, note, not wrongly accepted: the
failure mode here is a useless proof, not an unsound one.)

## The generalization

Two halves, and only the second changes.

**Per-cube lift — unchanged.** For a cube `c` with literals `l_1..l_d`
(`d = c.depth()`, which may now be anything in `0..=plan.depth()`), let
`D_c = (~l_1 | .. | ~l_d)`. Re-emit every `Add(C)` of `P_c` as `Add(C | D_c)`;
drop deletions. The existing argument carries over verbatim because it never
used `d = plan.depth()`: falsifying `C | D_c` sets every `l_i` true, which is
exactly the assignment the cube's unit clauses forced, so unit propagation
reproduces the original conflict. `P_c` ends in `Add([])`, which lifts to
`Add(D_c)` — the cube's refutation lemma, derived in DRAT from `F` alone.

**Collapse — replaced.** Instead of "every prefix at every level, deepest
first", walk the actual trie **bottom-up over internal nodes only**:

```
for p in internal_nodes(cover), in order of decreasing depth
        (any post-order DFS works; children strictly before parents):
    emit Add(R(p))     where R(p) = (~l(p_0) | .. | ~l(p_{|p|-1}))
```

`internal_nodes(cover)` is the set of proper prefixes of the cubes — precisely
the `interior` set `cover::verify_cube_cover` already builds. The root `()` is
internal whenever the cover has more than one cube, and `R(())` is the **empty
clause**, so the composition still ends in a refutation.

**Why `R(p)` is RUP at that point.** Falsifying `R(p)` sets every `l(p_t)`
true. Consider group `L = |p|` and its `k` children `(p, i)`. Each child is
either

* a **cube**, in which case `D_(p,i)` is present — the lift emitted it — or
* an **internal node**, in which case `R(p, i)` was already emitted, because we
  process strictly deeper nodes first.

Either way the clause "negation of `(p,i)`'s literals" is in the database.
Under the assignment it reduces to the unit `~l_i` of group `L`. Propagating
all `k` of them falsifies every literal of group `L`'s at-least-one clause,
which is an original clause of `F` and is never deleted — conflict. This is the
same argument as the flat case; the only thing the flat case was using was that
each child's clause is present, and completeness of the trie is what supplies
that.

**Degenerate case.** A cover consisting of the single root cube (`d = 0`) has
`D_c` empty, so the lift is the identity and `P_c` is already a proof of `F`.
There are no internal nodes and nothing to collapse. Handle it explicitly
rather than falling through the loop.

## Preconditions to check before emitting anything

The current function checks one (`verify_branch_clauses`). The trie version
needs three, and all three already exist:

1. `verify_branch_clauses(formula, plan)` — the collapse is not RUP without the
   at-least-one clauses, at **every** level the trie actually uses;
2. `verify_cube_cover(plan, &paths)` — completeness and non-overlap. Without
   completeness a child clause is missing and `R(p)` is not RUP; without
   non-overlap a node is both a cube and internal, and the two halves disagree
   about what it contributes;
3. every `P_c` ends in `Add([])` — otherwise `D_c` is never derived and the
   cube contributes nothing. Today this is implicit in
   `ComposeNoEmptyClause` at the very end; for a tree it should be a per-cube
   error naming the cube.

## Negative controls it must ship with

The existing `compose.rs` tests are the model. Add:

* **forged cover of a satisfiable formula** — every cube's "proof" a bare
  `Add([])` over an `F` that is genuinely SAT: the final `check_drat` must
  reject. (The flat version has exactly this test; keep its comment, which
  explains why an accepted composition on an UNSAT formula with one forged
  segment is *correct* behaviour rather than a hole.)
* **incomplete trie** — drop one cube: `compose` must refuse before emitting,
  with `MissingCell`.
* **overlapping trie** — a cube plus its own children: refuse with
  `DuplicateCell`.
* **wrong collapse order** — this is the load-bearing one, and it has no
  analogue in the flat version. Emit `R(p)` for a parent *before* one of its
  children, then check the artifact: the checker must **reject** it. If that
  test passes trivially (i.e. the checker accepts anyway, because the child
  happens to be derivable independently), the test is worthless and must be
  built on a cover where it genuinely is not — the flat test's comment already
  warns that on small instances every cube negation is one propagation cascade
  away.
* **root-cube cover** — a single cube of depth 0 composes to `P_c` itself and
  must still check.
* **mixed depths, real** — take a genuine adaptive cover (`F_103` for
  `R_4(3(x-y)=2z)` produces one in 4.6 s: 928 cubes at depths 2-6, 304 splits)
  and require `check_drat_backward` to accept the composition.

## The part that is not free

Implementing the above is small. Making it *usable at `F_741` scale* is not:

* the cover is **699,572,027 proof steps**; at ~83 bytes per step the composed
  artifact is roughly **58 GB** of text DRAT;
* `compose_cover_proof` takes `&[Option<Vec<DratStep>>]` — every cube's proof in
  memory at once. At this scale that is tens of GB before composition even
  starts. The `compose_step_cap` lever exists precisely because it does not fit;
* `check_drat_backward` then has to consume 58 GB.

So the roadmap item is really two:

* **1a. Generalize the transform to a trie** (this section). Immediately
  useful: on `F_103` the flat route already produced a 649,183-step, 40 MB
  proof, and the trie version would work there today.
* **1b. Stream it.** The lift is per-cube and local, so composition can write
  through a sink (`TextProofSink`, ADR-0381) as each cube finishes, retaining
  nothing; the collapse tail is at most one clause per internal node. What that
  leaves is a checker that can verify a proof larger than memory — which is a
  separate and bigger piece of work, and is the real gate on route A for
  instances of this size.

Until 1b exists, the honest statement for large covers stays: route B, four
checked obligations, one meta-argument.

---

# 5. Branch-point selection is the whole game, and nothing chooses it

## The measurement

`ColouringFamily::branch_points` (`crates/axeyum-search/src/family.rs`)
defaults to `2, 4, 6, …`. The 2026-08-12 probe of `F_741` used exactly that and
concluded the instance needed fleet time. Head-to-head today — same budget,
same wall clock, same worker count, same depth-3 frontier, only the branch
integers differing:

| branch integers | cubes refuted in 218 s | proof steps |
|---|---:|---:|
| `2,4,6,8,10,12` (the default) | 27 — every one a trivial symmetry refutation | 27 |
| `5,10,15,20,25,30` | 362 | 34,816,616 |

Two further orderings, suggested by the structure of the extremal colouring,
were measured and **rejected**: 5-adic (`625,125,250,375,500,25,…`) covered
6.32% of the space, and shell boundaries (`625,125,25,5,621,620,121,120,…`)
covered 10.19% and produced *not one* non-trivial refutation. Structure of the
*solution* is not structure of the *search*.

## Why, exactly

For `a(x-y) = bz` with `g = gcd(a,b)`, `a' = a/g`, `b' = b/g`, the solutions are

```
x - y = b' t ,   z = a' t ,   t = 1, 2, 3, …
```

so a point `j` occurs as the `z` of a solution **iff `a' | j`**. Every point
occurs as an `x` or a `y` for many `t`; only the multiples of `a'` also occur as
a `z`, and a single `z = a't` participates in `n - b't` distinct triples at once.
Fixing `c(z)` therefore forbids `c(y) = c(y + b't) = c(z)` for every `y`, which
is an enormous amount of propagation. Fixing `c(2)` forbids almost nothing.

(Recorded because this write-up had it wrong at first and the error survived
several documents: the divisor is `a'`, not `b'`. For `(a,b) = (5,4)`, `b' = 4`
would have named the multiples of 4 — nearly the losing set. The empirics were
right and the explanation was wrong, which is the more dangerous way round.)

Measured on `F_741` (65,564 forbidden sets):

| point | occurs in |
|---|---:|
| 5 | **884** sets |
| 2 | 148 sets |
| 4 | 148 sets |

## The heuristic to implement

**Sort points by the number of forbidden sets containing them, descending;
break ties by point index ascending; take the first `depth`.**

* family-agnostic — it reads `ColouringProblem::forbidden`, so it works for
  Schur, off-diagonal Schur, Rado, and anything added later, with no per-family
  knowledge;
* deterministic, which the project requires of anything that reaches an
  artifact;
* `O(sum of set sizes)` to compute, i.e. free next to one cube solve.

Sketch, as a default implementation on the trait:

```rust
fn branch_points(&self, depth: usize) -> Vec<usize> {
    let problem = self.problem(/* points */);          // or take &ColouringProblem
    let mut degree = vec![0usize; problem.points() + 1];
    for set in problem.forbidden() {
        for &p in set { degree[p] += 1; }
    }
    let mut points: Vec<usize> = (1..=problem.points()).collect();
    points.sort_by_key(|&p| (std::cmp::Reverse(degree[p]), p));
    points.truncate(depth);
    points
}
```

Note the signature problem: `branch_points(&self, depth)` has no access to `n`,
so the degree cannot be computed. It needs `branch_points(&self, problem:
&ColouringProblem, depth)` or to move onto `ColouringProblem`. That is the only
non-trivial part of the change.

## Does it actually reproduce the winner?

Computed directly from the constraint sets (not from a solver run):

| instance | first 20 points by degree | top degrees |
|---|---|---|
| `(5,4)`, `n=741` | `5,10,15,20,25,30,35,40,45,50,55,60,65,70,75,80,85,90,95,100` | 884, 881, 878, 875, … |
| `(3,2)`, `n=103` | `3,6,9,12,…,60` | 134, 133, 133, 132, … |
| `(4,3)`, `n=313` | `4,8,12,16,…,80` | 387, 385, 383, 382, … |

The first sixteen for `(5,4)` are **exactly** the branch set that closed
`F_741`, in the same order, chosen with no knowledge of the equation. For the
two instances already computed, it selects the multiples of `a'` there too —
and it explains why the `2,4,6,8,10,12` default did not fail catastrophically
on `R_4(4(x-y)=3z) = 313`: `4`, `8` and `12` are multiples of `a' = 4`, so half
of that default was accidentally right.

## Recommended change

1. change the default `branch_points` to constraint-degree ordering, with the
   signature fixed so it can see the problem;
2. keep `2,4,6,…` available as an explicitly named alternative for
   reproducing older runs, and document it as *a reproduction aid, not a
   recommendation*;
3. add a test that the degree ordering on `(5,4,741)` returns the multiples of
   5 in ascending order — it is a cheap regression pin on the thing that made
   this result possible;
4. consider recording the chosen points in the cover ledger's header. Today
   they live only in the launch command, and a ledger whose branch integers are
   not recorded cannot be re-certified without them (the claim carries them in
   `parameters.branch`, which is the pattern to keep).

---

# 2. The backward checker has a large per-call fixed cost

Measured on `F_741` (2964 vars, 269,664 clauses): 27 cubes whose proofs were
**one step each** cost 15.8 s of `check_drat_backward` in aggregate — about
0.59 s per one-step proof, against 1.0 s of solving for all 27 combined. The
cost is preparing the clause database, not checking the proof.

Affordable per instance, ruinous per cube: this cover ran 6241 cubes, of which
16 were refuted by pure propagation, so the fixed cost alone is thousands of
core-seconds spent on proofs that are a single conflict. The natural fix is a
checker that can be **primed once per formula** and then run against many small
proofs — the augmented formulas differ from `F` only by a handful of unit
clauses.

**Roadmap item:** a reusable checker context in `axeyum-cnf`, or a documented
cheap path for proofs below some step count.

# 3. The cost ratio that is actually load-bearing: check ≈ solve

`crates/axeyum-search/src/lib.rs:57` says backward checking "turned the same
run from ~1460 s of checking into a fraction of it". True, but the ratio that
matters at scale is checking against *solving*, and on `F_741` it is **0.95**
(27,985.0 s of solving against 22,042.6 s of checking over the whole 6241-cube
cover; 1012.3 s against 957.8 s on the first 362 cubes measured separately).

Inline checking therefore roughly doubles a search. Deferring it is not a 2%
optimization but a 2x one — and paying it anyway was the right call here,
because it is what let the run retain **zero** proof bytes.

# 4. Budget exhaustion should be a scheduling event, not a failure

Before this campaign the harness had one response to a cube it could not
finish: record `resource-out` and move on. A cover with one such cell proves
nothing, so the operator had to guess a conflict budget no cell would exceed,
and guessing high wastes it on every easy cell. On `F_741` the flat depth-6
cover left **1132 of 1946 finished cells** resource-out at 200k conflicts while
746 fell to unit propagation instantly.

Fixed for the tree path by `run_adaptive_cover`. The general shape is worth
keeping: **a budget that runs out is information about where to split, not an
error.**

# 6. API friction, small but real

* `BranchPlan::literals_for` requires a full-depth choice tuple, so every
  shorter cube needed a parallel `literals_for_prefix`. Two nearly identical
  functions is the kind of pair that drifts.
* `CoverOptions::proof_dir` is all-or-nothing: setting it dumps *every* cube's
  proof. At `F_741` scale that is ~58 GB, so the choice is between no artifacts
  and filling the disk. A size-triggered dump ("dump proofs over N steps") is
  what `check_step_cap` already implies but does not do.
* `CoverCertificate.cells` now means two things — product size for a flat
  cover, leaf count for a tree cover. It should carry the cover shape rather
  than have a field's meaning depend on which constructor ran.

# 7. Process: the shared checkout is a shared *compile* state

Cost about 20 minutes. `cargo test -p axeyum-search --lib` failed on
`colouring.rs:113` because another lane was mid-edit in a file this lane must
not touch. The file-ownership map does not help with this; the fix (build from
a private snapshot) is now rule 7 of the campaign README and belongs in
`docs/contributor-guide/multi-agent-worktrees.md`.

Second-order trap found the same way: `rsync -a` of a **live** `.git` while
another process writes it produces a tree whose `HEAD` is unreadable
(`fatal: bad object HEAD`). Snapshot with `git archive` or `git show`, never by
copying `.git`.

Third, from the operations side: `pkill -f 'run=b4'` issued over `ssh` matches
the remote command line **doing the pkill** and kills its own shell — exit 255,
no message. Use a bracket so the pattern does not match its own text:
`pkill -f 'run=b[4]'`.

# 8. `crates/axeyum-search/src/colouring.rs:10` cites a gate that does not exist

> "a divergence between the two would silently invalidate every stored
> certificate, so `tests/encoding_parity.rs` compares them directly."

There is no `crates/axeyum-search/tests/encoding_parity.rs`. The real
differential gate is `crates/axeyum-cnf/tests/colouring_encoding_parity.rs`,
and it covers `axeyum_cnf::colouring` — a **different** encoder from the one
that comment is attached to. The encoder every Rado cover actually runs against
had no cited gate at all, while its own doc comment said it did.

Measured rather than assumed, on `F_741`: the `axeyum-search` encoder,
`scripts/gen-rado-instance.py`, and the encoder inside
`scripts/check-claim-certificates.py` produce identical bytes — 8,591,634 B,
sha256 `90f4e81cae0eaf2a64e681cb31ad81d625da95fb6710b7facaaa6725b562a697`.
The comment's claim is true; its citation is not. `rado_dump_cnf` (new example)
makes the check one command.

**Roadmap item:** point the comment at the real gate and extend that gate to
`axeyum_search::colouring`, or delete one of the two encoders. Two encoders for
one contract with a gate on only one of them is the shape of a defect that
surfaces as a wrong certificate years later.

# 9. No live queue depth in `run_adaptive_cover`

The census a monitoring operator needs is "how many cubes are still open", and
the only place it appears is the pending file, written at exit. Everything else
has to be inferred from the ledger. `rado_cover_gaps` closes it after the fact,
but a `queue=` field in the split note — or an `on_progress` observer callback
carrying (queued, in-flight, refuted, split) — would have saved two rounds of
guessing whether the tree was converging. Twice during this run the covered
measure appeared to stall (31.0741% to 31.0841% in ten minutes) purely because
the LIFO queue had dived into one deep branch; the branching census had to be
reconstructed offline to see that it was fine.

# 10. `scripts/check-claim-certificates.py` could not express an adaptive cover

`check_cube_cover` requires `k ** len(branch)` cells, each fixing every branch
integer. Any cover produced by budget-driven splitting is rejected outright, so
a finished `F_741` cover could not have been recorded as evidence at all.

Fixed additively (`cube-tree-cover` kind plus two negative fixtures, and the
matching entries in `artifacts/ontology/claim.schema.json` and
`validate-claims.py`, which cross-check each other). The general lesson is the
one worth carrying: **the evidence vocabulary and the search capability drifted
apart silently.** The harness could produce artifacts the ledger had no kind
for, and nothing failed until someone tried to record one. A periodic check
that every `CoverOutcome`-shaped artifact has a claim kind that accepts it
would have caught it earlier.

# 11. A concurrent double-`sat` can leave the model file disagreeing with the result

`run_cover` **does** stop on `sat` — finding B1 fixed that, and
`tests/harness_defects.rs` pins it. What is still open is narrower and worth
recording before someone hits it.

In `harness.rs::handle_sat` (and the same shape in the adaptive path):

```rust
if let Some(path) = path.as_deref() {
    write_durable(path, render_model(model).as_bytes())?;   // (1)
    self.observer.on_model_persisted(cell.index(), path, model);
}
*self.sat.lock()... = Some(SatFinding { cell: cell.index(), model, path });  // (2)
```

Two workers that find satisfiable cells before either sees the stop flag both
run (1) and then (2), and the two orderings are independent. Interleave them as
`W1(1), W2(1), W2(2), W1(2)` and the run reports cell **A** with model **A**
while the file on disk holds model **B**. Both models satisfy `F`, so nothing
unsound is claimed — but the persisted artifact does not correspond to the
reported cell, and the whole point of writing it inside the worker was that the
file is the thing that survives.

Fix: make (1) and (2) one critical section, or have the first writer win by
claiming through a `compare_exchange` on the stop flag before writing. Cheap
either way; it needs a test with two workers and a formula with several
satisfiable cells.
