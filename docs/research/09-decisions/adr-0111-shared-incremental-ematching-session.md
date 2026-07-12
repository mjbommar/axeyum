# ADR-0111: Shared incremental e-matching session

Status: accepted
Date: 2026-07-11

## Context

ADR-0110 makes clause scheduling selective, but the quantifier round loop still
rebuilds all matching machinery for every quantifier in every round. Each call
re-infers triggers, assigns bridge declarations, reconstructs the entire ground
e-graph, rebuilds a root-to-members class index, and rescans every application.
Multiple quantifiers over the same ground context multiply this identical work;
multi-round chains repeat it after appending only a few source instances.

Z3's MAM registers patterns in shared code trees keyed by their root symbol,
receives incremental `add_node` and `on_merge` notifications, and propagates
pending candidates. cvc5 likewise retains a term database indexed by match
operator, compiles linked match generators with shared sub-generators, and
deduplicates instantiation tuples in tries. Both architectures separate stable
pattern compilation and ground-term registration from per-round propagation.

Axeyum's current recursive [`Pattern`] matcher is already sound and handles
arbitrary nesting, repeated variables, and multi-pattern joins. Replacing it
immediately with a bytecode interpreter would add substantial correctness risk
before measuring how much of the cost is simply repeated construction.

## Decision

Introduce one internal e-matching session for the quantified refutation loop and
one reusable batched matching primitive in `axeyum-egraph`.

The session:

1. peels every universal and infers its triggers once;
2. translates and interns structurally identical trigger patterns once in a
   shared declaration namespace;
3. owns one `InstBridge` and extends it only with newly appended ground terms;
4. applies newly asserted top-level equalities to the retained e-graph and
   rebuilds canonical disequality roots after merges;
5. builds one class/application index per propagation round and executes every
   unique compiled pattern against it;
6. joins cached per-pattern substitutions for each quantifier and retains the
   existing deterministic source-term tuple order; and
7. bounds solver-internal substitution-join work to 8,192 successful merges per
   round across all quantifiers, declining over-budget quantifiers before
   instance materialization; and
8. feeds ADR-0110's classifier the admitted complete instantiated bodies.

The public `witness_tuples_via_egraph` and
`instantiate_forall_via_egraph` remain complete one-shot APIs for evidence and
external callers; the 8,192-tuple cap applies only to the search-only internal
session. `Unsat` still requires a QF refutation of original ground assertions
plus genuine complete universal instances. An over-budget join therefore loses
only search completeness and eventually returns `unknown`.

This is T2.6.1's shared-state/compiler slice, not the full MAM exit. The recursive
pattern representation remains the first compiled form, and each propagation
round still rematches the current index. Bytecode instructions, inverted parent
paths, relevance/generation filters, and direct `on_merge` delta propagation
remain follow-ups whose value must be measured against this baseline.

## Acceptance

- Batched matching is extensionally identical to independent `ematch` calls for
  simple, nested, repeated-variable, congruence, and multi-pattern cases, with
  deterministic output.
- A multi-quantifier stress target proves that one bridge, one match index, and
  one interned pattern replace repeated one-shot reconstruction while producing
  the same complete witness tuples and genuine instances.
- A genuinely multi-round chain extends retained state with new instances and
  reaches the same replayable `Unsat` verdict as the legacy loop.
- Optimized end-to-end matching time materially improves on the committed stress
  target; broader quantified-BV/LIA decisions, replay, and PAR-2 do not regress.
- Existing bounded-instance soundness, Alethe witness generation, MBQI, evidence,
  and direct Z3 differential gates remain green.
- Workspace tests, Clippy, warning-denied rustdoc, links, foundational resources,
  formatting, and generated matrices pass, subject to documented long-running
  aggregate exclusions.

## Alternatives

- **Implement Z3's complete bytecode MAM immediately.** Deferred: the current
  recursive matcher already supplies the semantic operations. Shared retained
  state is independently measurable and establishes the ownership boundary the
  bytecode interpreter will consume.
- **Cache only trigger inference.** Rejected: ground bridge and index rebuilding
  dominate the multi-quantifier shape and would remain multiplied.
- **Share one bridge but rescan it separately per pattern.** Rejected: both
  references organize terms by match operator, and one round-local application
  index is simple, deterministic, and directly reusable.
- **Change public witness APIs to return only fresh tuples.** Rejected: proof
  generation relies on their complete deterministic match-set contract.

## Consequences

- The solver loop gains retained, monotone search state without exposing it as a
  public solver lifetime or weakening replay.
- Solver-internal multi-pattern joins cannot allocate an unbounded Cartesian
  product before the accumulated-ground cap is observed. Every successful
  intermediate substitution merge, including duplicates later removed, charges
  the deterministic shared budget; the first over-budget merge declines.
- Shared pattern interning provides the first code-tree analogue and a natural
  insertion point for later bytecode compilation.
- A round-local index is invalid after e-graph mutation by construction; the
  batched API owns index creation and consumption so callers cannot retain stale
  indexes.
- The next T2.6.1 slice can replace round rematching with add/merge-triggered
  candidate queues and inverted parent paths, measured against this retained
  session rather than against the much weaker rebuild baseline.

## Validation

- The committed target has 256 distinct ground applications and 32 universals
  with the same inferred trigger. Independent one-shot matching and the shared
  session return exactly the same 8,192 ordered witness tuples; the session
  compiles one unique pattern, performs one ground extension, and executes one
  batched match round.
- A complementary 8,193-match regression confirms that the public one-shot API
  remains complete while the internal session declines before materializing an
  over-budget round.
- Five optimized repetitions measured one-shot matching at
  17.119/17.466/17.477/17.530/18.874 ms and shared matching at
  0.943/0.957/0.974/0.986/0.989 ms. Medians improve 17.477→0.974 ms, a 94.4%
  reduction or 17.9x speedup. Timing is informational; tuple equality and state
  counts are deterministic assertions.
- The retained ADR-0110 path classifies the 256-match clause target exactly like
  its one-shot baseline: 255 redundant, one all-false source instance, no
  deferred instance. A two-quantifier chain records two extensions/two match
  rounds, gains the newly asserted `g(a)` term, and independently refutes the
  accumulated complete source instances.
- `axeyum-egraph` passes 27/27 unit tests, including batched simple/nested/
  repeated-variable/congruence matching and deterministic duplicate-pattern
  output. The solver e-matching module passes 30/30; the all-feature solver
  library passes 834/834.
- The independent bounded-instance harness passes 900 deterministic seeds.
  Focused quantified evidence, instantiation, MBQI/model-finder, and direct-Z3
  quantified-BV differential suites pass with zero disagreement; evidence is
  69/69 and `axeyum-bench` is 7/7.
- The 54-row cvc5-derived quantified-BV slice is decision-identical to ADR-0110:
  29 SAT, 9 UNSAT, 5 unknown, 11 unsupported, zero errors or replay failures.
  PAR-2 changes 7.47145→7.47374 seconds (0.031%). Three isolated quantified-LIA
  runs are 0.11812/0.11878/0.12024 seconds; median 0.11878 differs 0.34% from the
  ADR-0110 0.11837-second run, with the same 4 SAT / 8 UNSAT and no failures.
- The 5-row Bitwuzla-derived slice remains four expected UNSAT plus the broader
  tree's pre-existing quantified-SAT model-replay rejection; the UNSAT-only
  session does not grant that SAT result. No clean whole-slice claim is made.
- All 26 reference checkouts are present; the design review used Z3 `efe5e94`
  MAM code trees/add-node/on-merge callbacks and cvc5 `490652c` retained term
  database/match-generator/instantiation-trie paths.
- Workspace all-target/all-feature Clippy, warning-denied rustdoc, links,
  formatting/diff, capability/support goldens (2/2 and 12/12), and the
  137-concept/174-pack foundational-resource gate pass. The 2,000-case UFLIA
  debug fuzz stopped in ADR-0110 was not rerun, and the known Sturm
  nontermination still precludes a whole-workspace aggregate claim.
