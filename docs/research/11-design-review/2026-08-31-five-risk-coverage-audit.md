# What the L0 safety programme bought, per risk

Date: 2026-08-31
Lane: `five-risk-coverage-audit`
Subject: the five risks in the threat model of
[`docs/plan/trusted-library-safety-roadmap-2026-08-30.md`](../../plan/trusted-library-safety-roadmap-2026-08-30.md)
(ADR-0717), audited against every L0 gate in the tree.

This is an audit. Nothing here was repaired; no gate, census, fact or
generator was edited by this lane.

## How to read the numbers

Two denominators appear and they are not interchangeable.

- **Committed census** — `artifacts/safety-matrix/safety-matrix.tsv`, 2,136
  proved facts, last regenerated 2026-08-30 18:41 (`285d13f56`).
- **Fresh** — the same generator's `classify()` run in memory over today's
  ledger, 2,167 proved facts. Nothing was written.

**The committed census is stale and its own gate is RED.** Executed here:

```
python3 scripts/gen-safety-matrix.py --check
SAFETY_MATRIX|DRIFT|artifacts/safety-matrix/safety-matrix.tsv is stale
SAFETY_MATRIX|DRIFT|artifacts/safety-matrix/safety-matrix-summary.md is stale
SAFETY_MATRIX|FAIL|regenerate with `python3 scripts/gen-safety-matrix.py`
                                                            exit 1
```

31 facts have landed since. The drift is additive and monotone — no column
fell — so nothing published is overstated by staleness. But the artifact the
entire L0 programme is graded against does not currently pass its own
freshness gate, and that gate lives only in `just check` / `scripts/check.sh`
(see "the wiring finding" below), so nothing forced anyone to notice.

| column | fresh | committed |
|---|---:|---:|
| `exact_statement` | 2167 | 2136 |
| `env_footprint` | 1907 | 1878 |
| `coverage_bearing_checker` | 1471 | 1458 |
| `kernel_theorem` | 1495 | 1482 |
| `semantic_falsification` | 100 | 96 |
| `per_theorem_footprint` | 59 | 59 |
| `mutation_control` | 15 | 15 |
| `circularity` | 14 | 14 |
| `independent_replay` | 7 | 7 |

## The gap, first

Six numbers, all measured today, in the order a referee would ask for them.

1. **Vacuity is covered for 8 facts of 2,167 — 0.4% — and all 8 are one
   topic** (`Nat.totient` multiplicativity and the CRT counting argument
   behind it). This is the thinnest real number in the programme and, unlike
   contamination, there is no central gate quietly covering the rest.
2. **434 facts (20%) hold exactly one protection, and it is `env_footprint`**
   — a prelude-wide `--require-axiom-free` sweep that does not name their
   subject. **105 more hold none at all.** So 539 of 2,167 proved facts (25%)
   are protected by a whole-prelude sweep or by nothing.
3. **440 facts read `env_footprint: yes` while `coverage_bearing_checker: no`.**
   Their axiom-freedom credit comes from a command that does not mention the
   declaration the fact is about.
4. **548 of S2's ~1,956 enforced contamination subjects (28%) are chosen by a
   regex the repository itself documents as unreliable.** Measured below.
5. **The 9 facts with the strongest independent-replay evidence in the ledger
   all read `independent_replay: no`,** and the 7 that read `yes` are a
   disjoint set that includes one crediting replay from an argument-less
   gate.
6. **No L0 gate runs in CI or in `hooks/pre-push`.** Every one is in
   `just check` and `scripts/check.sh` only.

## The wiring finding, because it applies to all five risks

```
/usr/bin/grep -n 'check-settled-fact-statements|check-statement-identity-mutations
 |gen-safety-matrix|check-semantic-control-fixtures|check-trust-closure
 |check-mirror-statement-fidelity|check-fact-evidence-replay
 |check-checked-interchange' justfile scripts/check.sh hooks/pre-push \
 .github/workflows/ci.yml
```

Eight gates, sixteen hits, **all of them in `justfile` and `scripts/check.sh`;
zero in `.github/workflows/ci.yml` and zero in `hooks/pre-push`.** The kernel
differential (S5) is the same: `just check` and `check.sh` only. CI runs a
different set of `real_lean_*_crosscheck` suites and never touches it.

So the whole L0 safety contract is enforced by a local aggregate battery that a
contributor chooses to run. Nothing about a push or a CI run blocks a change
that breaks any of it. That is also the most likely explanation for the census
being stale and red for seven hours without anyone tripping over it.

---

## Risk 1 — kernel unsoundness

*"substitution, conversion, universes, inductives, recursion, proof
irrelevance, or reduction accepts an invalid term"*

### Covered

**S5, the kernel differential.** 35 cases across all 8 roadmap-named
subsystems (conversion 4, universes 4, inductives 4, recursors 4, projections
5, literals 5, quotient 5, proof irrelevance 4), built at run time by
`full_corpus()` in `crates/axeyum-lean-kernel/tests/kernel_differential.rs`.
Each case is authored twice and independently: the Axeyum side through the
kernel term-builder API, the Lean side as surface syntax, because
`render_lean_module` can only walk an already-admitted closure and therefore
cannot express the *reject* half of the corpus.

It invokes a real pinned Lean binary (`kernel_differential.rs:2317`), not a
recorded expectation. **Zero Axeyum-accepts/Lean-rejects on the unmutated
kernel.** One disagreement is recorded and it is the safe direction:
`quotient::quot_sound_absent`, an Axeyum-*rejects*/Lean-accepts incompleteness,
pre-registered — and the registry is tight both ways, so an unregistered
incompleteness fails and a registered one that stops occurring also fails.

The skip trap is handled correctly, twice. `cargo test` alone returns green
when Lean is absent, but the *gate* sets `AXEYUM_REQUIRE_LEAN=1`
(`scripts/check-kernel-differential.py:166`), which turns the probe's skip into
an assert, and guard G4 independently fires when no
`AXEYUM-LEAN-CHECKED … checked=N>0` line was printed. A gate that cannot run
does not pass.

**S4, independent Lean replay — the bigger risk-1 instrument, and it is not
counted as one.** `crates/axeyum-lean-kernel/tests/real_lean_replay_census.rs`
exports the representable slice of the constructed real carrier and hands it to
`Lean.Environment.addDeclCore` from `mkEmptyEnvironment`, then reads the grade
back out of *Lean's* `env.constants` by exact `BTreeSet` membership — not a
prefix, family or module match. Measured 2026-08-30 on Lean 4.30.0
(`d024af09`): population 2,045, representable 1,972,
`checked=1972 expected=1972 missing=0 extra=0`; 73 non-representable = 48
`theorem_type_not_prop` + 25 `blocked_by_dependency`.

An independently-implemented kernel agreeing on 1,972 declarations is stronger
evidence about *our* kernel's soundness than 35 hand-built cases are. The
census records it as one fact.

### Verified how

- `python3 scripts/check-kernel-differential-mutants.py` → exit 0, "8 mutants,
  8 killed / 0 survived, all 8 subsystems covered".
- `python3 scripts/check-kernel-differential.py --self-test` → exit 0, G1–G6
  each firing on its own fixture.
- The differential itself and the S4 census were **not run** by this audit;
  both need a kernel build. Read, not executed.

### Not covered — say this before crediting the zero

**"8 of 8 mutants killed" is a pinned human measurement, not a re-derived
one, and the ratchet says so.** `check-kernel-differential-mutants.py`
deliberately does not re-run mutations (mutating tracked kernel source in a
shared checkout breaks other lanes' builds). It checks the artifact's internal
consistency: one entry per subsystem, every `KILLED` naming evidence, counts
matching. So it can detect a mutilated ledger and cannot detect a wrong
measurement.

**Positivity is implemented twice, and the honest reading is narrower than
"a hole".** Confirmed in source:

- `crates/axeyum-lean-kernel/src/inductive.rs:1917`
  `check_group_positive_occurrence` → `NonPositiveInductiveOccurrence`
- `crates/axeyum-lean-kernel/src/inductive.rs:2125`
  `open_group_recursive_field_shape` → routed at `:2076` to
  `classify_bad_group_recursive_field` (`:2225`) →
  `ReflexiveOrNestedNotSupported`

Same walk, sharing `mentions_group_family` (`:1995-2013`). The five-rebuild
measurement in ADR-0815 is decisive: with either guard alone disabled the
kernel still rejects; **with both disabled it admits a non-positive
inductive.** So neither copy is individually load-bearing and no corpus case
can separate them — but the pair is *jointly* load-bearing, and the shipped
mutation is aimed at the shared predicate, where it kills with exactly one
flipped case. The `inductives` kill is real; it is a kill of the predicate,
not of either call site.

The residual limitation is the one that should be quoted: **a defect in the
shared predicate that both copies inherit would be invisible**, and only
`mentions_group_family`'s `Const` arm is exercised by anything in the corpus.
The `Proj`, `Let` and `App` arms are covered by nothing.

Two further redundancies are recorded: R2 (a `tc.rs:3303` bounds check
redundant with `infer_projection`'s field walk) and R3 (`quotient.rs:137`,
"UNKILLABLE BY CONSTRUCTION").

**Corpus depth.** 35 cases over 8 subsystems is ~4.4 cases each: a smoke test,
not a fuzz. The uncovered list is stated in the test's own source and in
ADR-0780/ADR-0815 — mutual and nested inductives, indexed families beyond
0-index, Prop-restricted large elimination, structure eta beyond plain
projection, string literals, zeta reduction, well-founded recursion, longer
reduction chains.

**Stale counts in committed prose.** `justfile:1146,1157-1159` and
`docs/plan/status/390-l0-s5-kernel-differential.md` still describe the gate as
"32 cases" with "4 of 8 targeted guards killed outright". Nothing enforces
those numbers, so they drifted when ADR-0815 landed.

---

## Risk 2 — statement error

*"the proved type mistranscribes or weakens the intended proposition"*

### Covered

Three mechanisms, and only the third compares against anything external.

**(a) Drift pins — 2,167 of 2,167 (`exact_statement`).**
`artifacts/ontology/settled-fact-statement-pins.json` holds, per settled fact,
the SHA-256 of `formal.statement`, the SHA-256 of the reader-facing
`statement`, and the `kernel_theorem` named. Any of the three moving fails
unless an amendment names the fact, both digests and a reason. Executed:

```
python3 scripts/check-settled-fact-statements.py
SETTLED_FACT_STATEMENTS|settled=2169|pinned=2169|unpinned=0|identity_bound=1300
  |header_exempt=30|drifted=0|amendments=3|retracted=0                exit 0
```

**(b) The structural header bind.** For a `lean4` fact naming a
`kernel_theorem`, the statement's rendered `theorem <name> :` must be that
declaration's name. This is the sharpest guard here and the one a content hash
cannot express: it catches a statement replaced by a *different theorem's*
rendering. 30 facts are `header_exempt` (bare-type statements), ratcheted.

**(c) Mirror fidelity — 582 facts bound to an external authority.** Executed:

```
python3 scripts/check-mirror-statement-fidelity.py
MIRROR_STATEMENT_FIDELITY|facts=2364|mirrors=594|hash_verified=582
  |unpinned=12|violations=0|verdict=PASS                              exit 0
```

For 582 of 594 `F:ml430-*` mirrors, `sha256(formal.statement)` must equal a
`source_statement_sha256` preregistered from the pinned Mathlib v4.30 source.
The 12 unpinned are the deliberately-mutated `ml430-mutation-*` family and have
no pin by construction.

**(d) Name AND type, against pinned Lean — 9 facts.** ADR-0915's C2 route
grades a root `accepted` only when *both* pinned Lean's own `env.constants`
contains the name **and** the type this kernel checked renders byte-identically
to the type a fresh `import_ndjson` rebuilt in a separately-constructed
`Kernel`. `BARE_NAME_ACCEPT` and `BARE_TYPE_ACCEPT` each fail a census that
claims one without the other. This is the only mechanism in the tree that
compares an Axeyum type against a second system's reconstruction of it.

### Verified how

Executed here, and the tree was clean before and after:

```
python3 scripts/check-statement-identity-mutations.py
STATEMENT_IDENTITY_MUTATIONS|control|clean-tree|statement=0|mirror=0
… 1 swapped binders      REJECTED|by=statement-pin
… 2 changed constant     REJECTED|by=statement-pin
… 3 altered relation     REJECTED|by=statement-pin
… 4 source drift         REJECTED|by=statement-pin+mirror-fidelity
… 5 our own rendering    REJECTED|by=statement-pin+mirror-fidelity
STATEMENT_IDENTITY_MUTATIONS|PASS|5/5 rejected|tree restored           exit 0
```

Read the `by=` field, because it is the finding. **Mutations 1–3 are caught
only by the statement pin** — that is, only because the statement changed
*after* pinning. Had the swapped binder or the wrong constant been present on
the day the fact was written, nothing in this gate would see it. Only
mutations 4 and 5 are additionally caught by an upstream comparison.

### Not covered

- **A drift pin is not a correctness claim, and `exact_statement` at
  2,167/2,167 reads like one.** It says the statement has not changed since we
  wrote it down. For the ~1,585 native (non-mirror) proved facts, that is the
  entire protection: we are the authority for those statements and the gate
  checks only that we have not quietly revised them.
- **`identity_bound` is 1,300 of 2,169, not 2,169.** The stronger pin — the one
  that ties a fact to a specific `kernel_theorem` alongside both digests —
  reaches 60% of settled facts. This number matches, exactly, the 1,300 facts
  carrying `formal.kernel_theorem` (measured independently below), which is a
  useful cross-check that both gates are reading the same binding.
- **Nothing compares a mirror's Axeyum kernel *type* against Mathlib's type,
  for 585 of 594 mirrors.** Mirror fidelity verifies the fact carries Mathlib's
  *statement text*; the header bind verifies the *name* matches. That two
  systems' identically-named declarations can state different propositions is
  measured in this repository already (ADR-0716, `Nat.multichoose`). The 9
  checked-interchange roots close it; 585 mirrors are open.

---

## Risk 3 — vacuity

*"an impossible/irrelevant hypothesis, degenerate definition, or zero cofactor
makes a readable theorem meaningless"*

### Covered

**8 facts of 2,167.** Executed:

```
python3 scripts/check-semantic-control-fixtures.py
… 13 fixtures, all classes behaving …
fixtures=13|executed=9742|mutations=19|killed=18|also_true=1|survived=0
load_bearing=8|semantic_falsification=96|proved=2136                  exit 0
```

The gate itself is well built and it discriminates in the right places:
a `false` fixture must produce a counterexample, a `vacuous` fixture must
discriminate **nothing** (the fixture asserts the zero rather than its own
greenness), a `valid` fixture must be accepted, must discriminate, **and must
kill at least one mutation** — and any fixture executing zero cases fails
whatever its class. A mutation that is not falsified because it is itself true
is classified `also-true` and reported for review, not failed, which is what
keeps the gate from being turned off.

The 8 facts, from the generated summary:

| fact | source |
|---|---|
| `F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7` | numerics |
| `F:ml430-nat-totient-dvd-of-dvd-9622e44a` | numerics |
| `F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7` | numerics |
| `F:nat-crt-self-map-injective-on` | fixture + numerics |
| `F:nat-totient-dvd-totient-mul-prime` | numerics |
| `F:nat-totient-mul-of-coprime` | fixture + numerics |
| `F:nat-totient-mul-of-dvd` | numerics |
| `F:nat-totient-prime-pow` | fixture + numerics |

### Not covered

- **2,159 of 2,167.** And the 8 are not a sample — they are one topic. All
  eight are `Nat.totient` multiplicativity or the CRT counting argument
  underneath it. Nothing in `CReal`, `Complex`, `Rat`, the integral, the IVT,
  the solver routes or the CAS certificates has a control demonstrated to fire.
- **92 facts carry a semantic-falsification evidence row that was never shown
  to discriminate** (100 fresh − 8). The census row carries an inline UPPER
  BOUND marker for this, correctly.
- **The ledger's `kind` enum has lost its discriminating power and the census
  works around it silently.** 1,920 evidence rows declare
  `exhaustive-enumeration` or `instance-pin` while their `supports` field
  records an axiom footprint. Nothing was enumerated. `is_footprint_row` in
  `scripts/gen-safety-matrix.py` exists precisely to stop that turning 96 into
  ~1,992 — the single largest over-count available on this ledger. The
  workaround is correct; the underlying ledger data is not, and no gate fails
  on it.

---

## Risk 4 — contamination

*"the target proof, an equivalent imported theorem, an axiom, opaque, or
quotient enters the dependency closure"*

### Covered — this is the strongest phase, centrally

**S2 reaches ~1,956 kernel-route settled facts on every merge**, with four
guards over closures computed from the admitted term: `population`,
`self_occurrence`, `alias_occurrence`, `forbidden_trust`. The floor is pinned
in `artifacts/trust-closure/population.json`:

```json
{"min_subjects": 1956, "min_ratio": 0.9583, "min_declarations": 2482}
```

and the floor is re-derived rather than merely monotone, so loosening it is
self-reverting. `alias_occurrence` is the part worth naming: it derives
equivalence classes from byte-identical `Kernel::render_lean` canonical types
and rejects a closure reaching an equivalent statement — the indirect-target
injection shape — with the 13 known duplicate-type disclosures listed in
`equivalent-pairs.tsv`, a file that can only shrink without a recorded update.

`forbidden_trust` walks each subject's closure and rejects any reachable
`Axiom`/`Opaque`/`Quotient`. **That is a per-theorem axiom-footprint check by
another name, over ~1,956 facts** — against the census's per-fact
`per_theorem_footprint` of 59.

### Verified how — and this one I did see fail

Executed here, and it is the best-controlled gate in the programme:

```
bash scripts/tests/test-trust-closure.sh
== mutation kill sets ==
  self_occurrence KILLED target-injection
  alias_unlisted  KILLED indirect-target-injection
  alias_stale     KILLED stale-disclosure
  trust_unowned   KILLED unowned-opaque
  trust_axiom     KILLED axiom-insertion
  population_empty / population_floor / population_absent  KILLED …
  identity_drift / scanned_nothing / population_pin_missing
  disclosure_missing / empty_projection / coverage_floor
  identity_map_missing                                     KILLED …
TRUST_CLOSURE_CONTROLS|cases=17|mutations=15|not_exactly_one=0         exit 0
```

15 guards deleted one at a time in a scratch copy; each kills **exactly one**
case, `not_exactly_one=0`. Every case asserts an exact failure tag rather than
a nonzero exit, which is what stops fifteen guards rejecting through one shared
path. `GUARD-SCANNED-NOTHING` is itself one of the guards, so a guard that
examined no cases is a failure rather than a green run.

S2 itself was **not run** (its projection needs a `--release` kernel build).
The pinned floor is committed evidence generated by the gate; the live number
was not re-derived here.

### Not covered — and this is the finding

**28% of S2's enforced population has its subject chosen by a regex the
repository documents as unreliable.** `subject_of`
(`scripts/check-trust-closure.py:287`) resolves in three tiers. Replicating
those tiers over today's ledger, in the gate's own order:

| tier | facts |
|---|---:|
| `formal.kernel_theorem` present | **1300** |
| single `evidence[].kernel_declaration` | **152** |
| `theorem_of` regex over `checker_command` text | **548** |
| unresolved (not enforced) | **87** |
| kernel-lean settled, total | **2087** |

`theorem_of`'s own docstring (`scripts/check-fact-depends-derived.py:140`) says
the extraction "is demonstrably NOT reliable in general", and names two recorded
failures: it extracted `Int.sub` instead of `Int.fib_cassini` for
`F:cassini-identity-over-constructed-integers`, and it collided two unrelated
facts onto one name. **If it picks the wrong declaration, all four S2 guards
run on the wrong subject and pass**, because the wrong subject's closure is
almost certainly clean. That is the checker-that-cannot-fail shape moved up to
the population layer.

Two cheap screens, and neither is conclusive:

- **Collisions are rare.** Over the 548, 542 distinct names; only 6 names
  claimed by more than one fact, covering 12 facts. 25 regex picks equal some
  *other* fact's explicit subject.
- **Absence rate is higher but the control is weak.** Against
  `artifacts/autogenesis/kernel-environment-snapshot-v1.json` (2,507 names,
  possibly stale), 13 of 548 regex picks are absent versus 2 of 1,452 explicit
  picks. Suggestive, not conclusive — most of the 13 are recent `ml430` names
  that the snapshot plausibly predates. S2's own `absent` guard is the
  authority and it is enforced; this screen is not a substitute for it.

So the honest statement is not "548 subjects are wrong". It is: **548 subjects
are unaudited, the mechanism that chose them has a recorded history of choosing
wrongly, and its characteristic failure — matching a fragment of an embedded
formal statement — is invisible to every screen available without the kernel.**

**Per-fact evidence for the risk-4 shape is zero.** ADR-0795 established this
and it still holds: `footprint_closure_audit`, the sole tool behind
`circularity`'s 14, proves a closure reaches no trusted declaration. It does
*not* detect the target or an equivalent entering its own closure, which is
what the column is named for. All real coverage of that shape is S2's.

**`env_footprint` at 1,907 is a prelude-wide sweep, not a per-fact one.** 440
of those facts have no checker naming their own subject at all
(`env_footprint: yes`, `coverage_bearing_checker: no`). The three widest
checker commands are one `nat_axiom_inventory --require-axiom-free` invocation
shared by 467, 347 and 290 facts respectively.

---

## Risk 5 — false evidence

*"a checker exits zero on completion, omits the subject, shares the
implementation defect, or records stale ledger state"*

### Covered

**Centrally: `scripts/check-fact-evidence-replay.sh` re-runs every settled
fact's `checker_command` at gate time**, route-agnostic across kernel-lean,
smt-term-level, cas-certificate and search-certificate. It refuses to run when
the worktree does not compile, so another lane's in-flight breakage cannot make
unrelated facts look rotted, and it reports which facts it never reached by
name when the whole-sweep deadline fires. This moves `close-fact.py`'s
write-time rule to gate time, which is the right shape.

**`scripts/check-gate-liveness.sh`** pins a minimum test count per suite, so a
suite emptied by a new `#![cfg(feature = …)]` breaks the build instead of
printing "running 0 tests … ok".

**The census's own controls run and are honest.** Executed:
`python3 scripts/tests/test_safety_matrix.py` → 7 tests, 1.145 s, OK. Its
`SYNTHETIC_UNPINNED` case runs the real `classify()` over a fact-shaped dict in
no manifest and requires `exact_statement: False`, which is what kills the
"write `True` as a constant" mutant that the earlier `UNPINNABLE_PROBE`
survived.

**The classifier is deliberately conservative in the right places.** It refuses
the `theorem_of` regex for `kernel_theorem` (so 1,495 understates by design and
should stay), it removed three `DEPENDENCY_CLOSURE` alternatives that walked no
closure, and `is_footprint_row` refuses to read the `kind` enum at face value.

### Not covered

- **`check-fact-evidence-replay.sh` verifies exit 0, not discrimination.** It
  is exactly the right gate against *stale* evidence and says nothing about a
  checker that could not have failed. It also publishes coverage by route, not
  a per-fact set.
- **696 facts (2,167 − 1,471) have no checker naming their own subject.** 305
  of them would gain one only if the unreliable regex were trusted — that is
  the `coverage_by_guess_only` column, and it is the ledger's unbound-subject
  debt rather than a protection.
- **17 facts cite no `checker_command` at all. 105 hold zero protections.**
- **1,358 of the 2,003 facts whose evidence lists two or more named `checkers`
  name the PRODUCING run as one of them.** A production is not a re-derivation
  of itself, so those rows are one check and one re-listing, and
  `validate-facts.py` counts them toward its "re-derived by 2+ independent
  checkers" line.
- **The census was stale and its gate red at the time of this audit**, which is
  precisely the "records stale ledger state" clause of risk 5, landing on the
  instrument that measures risk 5.

---

## Which census columns are wrong, and in which direction

| column | reads | direction | why |
|---|---:|---|---|
| `circularity` | 14 | **understates by ~1,942, and measures the wrong thing** | S2 enforces closure centrally over ~1,956 and no fact cites it. Separately, `footprint_closure_audit` does not detect target self-occurrence at all, so per-fact evidence for the named shape is **0**. |
| `semantic_falsification` | 100 fresh | **overstates by 92** | counts facts naming a control; 8 were demonstrated to discriminate. The row carries the marker. |
| `independent_replay` | 7 | **wrong in BOTH directions** | see below |
| `per_theorem_footprint` | 59 | understates by ~1,897 | S2's `forbidden_trust` is a per-theorem footprint check by another name |
| `kernel_theorem` | 1495 | understates **by design** — keep | refuses the `theorem_of` regex; the stricter number is the right one |
| `exact_statement` | 2167 | correct, on the correct (coverage) axis | but it is drift protection, and reads like a correctness claim |
| `env_footprint` | 1907 | correct as stated | 440 of them have no checker naming their subject |
| `coverage_bearing_checker` | 1471 | correct | per-fact by construction |
| `mutation_control` | 15 | mis-shaped, not wrong | S1's mutation gate is one ledger-wide pass/fail; reading it per-fact would be inflation |

**`independent_replay` deserves its own paragraph.** The seven facts it credits
are `F:bool-and-comm`, `F:lean-kernel-accepts-the-whole-constructed-real-carrier`,
`F:list-nil-append`, `F:nat-le-refl`, `F:nat-le-succ`,
`F:prop-excluded-middle-classical`, `F:schedule-critical-chain-infeasible`.
Meanwhile the nine roots of `artifacts/checked-interchange/census/credited-roots-v1.census.json`
— the only facts in this ledger with a published, per-fact,
name-**and**-type, real-pinned-Lean-admitted replay grade — **every one reads
`independent_replay: no`.** The sets are disjoint. And the seven include
`F:schedule-critical-chain-infeasible`, which ADR-0795 already flagged as
crediting replay from `scripts/check-lean-gate.sh` with no arguments.

So the column simultaneously misses the strongest evidence in the tree and
includes at least one row that inherits a grade from a gate that says nothing
about it.

### Is `independent_replay` at 7 a measurement gap or a real one?

**Mostly a measurement gap for declarations, partly a real gap for facts.**

Lean's kernel really did admit ~1,972 declarations. Reconstructing S2's
`subject_of` over the ledger, ~2,000 settled kernel-route facts resolve to a
declaration name, and roughly 1,688 of those name declarations in the
`Nat`/`Int`/`Rat`/`CReal` families that `build_creal_prelude` carries — i.e.
the replayed population. But that 1,688 is a **prefix proxy, not a set
intersection**: the ~1,972 replayed name list is never committed (it lives in a
scratch `.names` file), and the 73-name non-representable residue is not
committed either. So the join cannot be computed from the tree, only estimated.

The real gap, as opposed to the measurement gap, is smaller and specific: no
committed artifact and no `--json` output pairs a fact id with a replayed
declaration name, outside the 9 checked-interchange roots. Until one exists,
"Lean checked this theorem" is unverifiable per fact.

## Can per-fact and central coverage now both be reported?

**ADR-0795's "only one gate publishes a per-fact set" is no longer true.
Two do, and a third publishes half of one.**

| gate | publishes a per-fact set? | key | facts |
|---|---|---|---:|
| S1 `check-settled-fact-statements.py` | yes (already credited) | `pins[].fact_id` | 2169 |
| **C2 `check-checked-interchange.py`** | **yes, and uncredited** | `credited_roots_replay.roots[].fact_id`, with per-root `lean_admitted_by_name` / `reimport_type_matches` / `status` | **9** |
| S3 `check-semantic-control-fixtures.py` | **half** | `fixtures[].fact_ids` is in the JSON; the `load_bearing` map (which adds the numerics half) is still markdown-only | 8 |
| S2 `check-trust-closure.py` | no | `subjects.resolved` still built and discarded at `:730` | ~1956 |
| S4 `real_lean_replay_census` | no | no artifact written at all; stdout markers only | ~1972 names |

So the census can, today and with no new measurement, add a coverage row for
the 9 checked-interchange roots — on `independent_replay` *and* on a name+type
statement-identity axis — and can credit S3's 8 from JSON rather than markdown
once the `load_bearing` map is written alongside the counts it already emits.
S2 and S4 remain exactly where ADR-0795 left them, and S2's is one dict
comprehension.

## What "axiom-free" is worth now

Two lines a referee can check, replacing the single-sentence claim:

> Every theorem in the shipped preludes is admitted by a kernel that reaches
> no axiom, opaque or quotient — checked per subject by a closure walk from the
> admitted term for **1,956** ledger facts, and independently re-checked by
> Lean 4.30.0's own kernel for **1,972** declarations of the constructed real
> carrier. That establishes the *proofs* are complete. It does not establish
> the *statements* are the intended ones — **582** are bound by hash to pinned
> Mathlib source and **9** are additionally type-checked against Lean's
> reconstruction; the rest are ours — and it does not establish they are
> non-vacuous, for which **8** facts carry a control demonstrated to fire.

```sh
python3 scripts/check-trust-closure.py            # subjects=1956, forbidden trust 0
python3 scripts/check-semantic-control-fixtures.py # load_bearing=8
python3 scripts/check-mirror-statement-fidelity.py # hash_verified=582
```

The short form, if only one sentence is available: **axiom-freedom is a
completeness property of our proofs, verified per-subject and independently
re-checked; it is not a claim about what the statements say or whether they are
vacuous, and those two are covered for 582 and 8 facts respectively.**

## The risk I would attack next

**Vacuity.** 8 of 2,167 is the only risk where the honest number is under one
percent *and* there is no central gate quietly covering the rest — contamination
looks thin at 14 and is actually 1,956; vacuity looks thin at 8 and is 8.

## What this audit ran, and what it did not

Executed here, foreground, exit status read from the bare command:

- `scripts/check-settled-fact-statements.py` (0), `check-statement-identity-mutations.py`
  (0, 5/5, tree clean before and after), `check-mirror-statement-fidelity.py` (0),
  `check-semantic-control-fixtures.py` (0), `scripts/tests/test-trust-closure.sh`
  (0, 17 cases / 15 mutations / `not_exactly_one=0`),
  `scripts/tests/test_safety_matrix.py` (0, 7 tests),
  `gen-safety-matrix.py --check` (**1, stale**), plus `check-kernel-differential-mutants.py`
  (0) and `check-kernel-differential.py --self-test` (0).
- Ledger measurements computed directly from `artifacts/facts/*.json`, replicating
  `subject_of` and the census `classify()` in memory, writing nothing.

**Not run, and therefore reported as read rather than verified:**
`check-trust-closure.py` itself (needs a `--release` kernel build for its
projection), the S5 differential against Lean, the S4 replay census, and
`check-fact-evidence-replay.sh` (whole-sweep deadline 9,900 s). Their numbers
above come from committed artifacts and pinned floors, which is weaker evidence
than execution and is labelled as such at each use.
