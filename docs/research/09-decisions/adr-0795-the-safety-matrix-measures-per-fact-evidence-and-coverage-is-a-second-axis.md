# ADR-0795: The safety matrix measures per-fact evidence; coverage is a second axis

Status: accepted
Date: 2026-08-30
Index-summary: S0's nine columns all ask "does this fact's own record exercise
this protection". They were read as coverage. Audited all nine against every
centrally-run gate: `circularity` was 63% false positives (24 of 38 rows
credited to a tool that walks no closure) and is now 14; `semantic_falsification`
reads 95 against 8 demonstrated; `exact_statement` was never an evidence column
and moves to a separate coverage axis excluded from `protection_count`. Four
mutants that the census could not fail on are now killed by four distinct
controls.

Phase: S0 of the trusted-library safety roadmap (ADR-0717)
Lane: `safety-matrix-semantics`

## Context

`artifacts/safety-matrix/safety-matrix.tsv` is the census the whole L0
programme is graded against: every phase is justified by a column being thin
and measured by that column getting thicker. So what a column *means* is
load-bearing in a way an ordinary metric is not.

The trigger was one column disagreeing with a gate. `circularity` read 38 of
2,121 while `scripts/check-trust-closure.py` (S2, ADR-0771) computes each
settled fact's proof closure from the admitted kernel term and enforces that no
fact's closure contains its own target — covering 1,956 of 2,041 kernel-route
facts, on every merge.

Both numbers were right about their own question, and the column name fit
neither. The naive fix is a trap: `check-trust-closure` is not among the four
patterns `DEPENDENCY_CLOSURE` matches, and adding it changes nothing, because
**zero facts cite it** — S2 enforces centrally, so no fact needs to.

## The audit

All nine columns, read against every gate in the tree that provides the same
protection by another route. Census figures are live at 2,121 proved facts.

| column | census | true coverage | direction | the gate that supplies the rest |
|---|---:|---|---|---|
| `exact_statement` | 2121 | 2121 | correct, wrong axis | S1 `check-settled-fact-statements.py` — this column was *always* read from a ledger-wide manifest, never from the fact's own checkers |
| `kernel_theorem` | 1467 | 1956 resolved | understates by design | S2 adds the `theorem_of` regex fallback the census deliberately refuses; the census's number is the stricter one and should stay |
| `per_theorem_footprint` | 59 | 1956 | understates by 1903 | S2 `guard_forbidden_trust` walks each subject's closure and rejects any reachable `Axiom`/`Opaque`/`Quotient` — a per-theorem footprint check by another name |
| `env_footprint` | 1863 | 1863 | correct | no central per-fact set exists; the prelude-wide sweep is what it says |
| `circularity` | **38 → 14** | 1956 | **overstates AND understates** | S2 `guard_self_occurrence` + `guard_alias_occurrence`; see below |
| `semantic_falsification` | 95 | **8 demonstrated** | **overstates by 87** | S3 `check-semantic-control-fixtures.py`; its own artifact already says so |
| `mutation_control` | 15 | not a per-fact protection | mis-shaped | S1 `check-statement-identity-mutations.py` is one ledger-wide pass/fail |
| `independent_replay` | 8 | not measurable from a fact | understates, unquantified | S4 `real_lean_replay_census` (ADR-0760) grades declaration NAMES; the fact join is not published |
| `coverage_bearing_checker` | 1443 | 1443 | correct | per-fact by construction, and the only column that already required the command to name the fact's own subject |

### `circularity` was overstating, and that is the finding to read first

Not merely mislabelled — **wrong in the dangerous direction, for 24 of its 38
rows.** They were credited by

```sh
cargo run … --example kernel_declaration_projection -- \
  --require-declaration Complex.factorQuotient --require-kind definition \
  | grep -cE '^found[[:space:]]complex[[:space:]]definition[[:space:]]Complex\.factorQuotient[[:space:]]'
```

which computes no closure of any kind. It prints
`found <label> <kind> <name> <footprint-size>` and stops; the example's own
module doc says the projection *"is search vocabulary and must not be confused
with a transitive closure"*. Three further observations make it worse:

- every one of the 24 names a **`definition`**, which has no proof body and
  therefore no closure to be circular in;
- the committed greps end at the tab *before* `<footprint-size>` and do not
  constrain the value, so they are not even a footprint check;
- two of the four alternatives, `dependency-audit` and
  `check-fact-depends-derived`, match **zero** committed commands. A dead
  alternative is not harmless: it makes the pattern look broader than it is,
  which is how a per-fact regex came to be read as a coverage claim.

Removing them loses no measurement: all 24 already read
`coverage_bearing_checker: yes`, so the check they do run is counted where it
belongs. The column is now 14, every row a `footprint_closure_audit` run, which
does rebuild the narrow and widened closures and aborts if either disagrees
with `Kernel::axiom_footprint`.

**Note what remains true even at 14.** `footprint_closure_audit` establishes
that the closure reaches no trusted declaration. It does *not* detect the
target or an equivalent entering its own closure, which is the ADR-0717 risk-4
shape the column is named for. So `circularity` at 14 is an upper bound on a
protection that no per-fact evidence in this ledger currently carries, and the
real one is S2's, centrally, at 1,956.

### `semantic_falsification` overstates too, and S3 said so first

S3's own generated artifact carries the sentence:

> S0's `semantic_falsification` column reports 91 / 2117. That is the upper
> bound: it counts facts carrying a semantic evidence row, not facts whose
> control was shown to discriminate.

Live: evidence **95**, demonstrated **8**. That gap of 87 is the second place
this census stands above executed reality, and it was already measured — it
simply had nowhere in the census to be said.

### Two shapes the audit checked and did NOT find

Honest negatives, because an unchecked axis reported as clean is the defect
this repository cares most about:

- **A `cargo test` naming a suite that runs zero tests.** The three `cargo test`
  commands feeding `mutation_control` are `--lib` filters on
  `axeyum-lean-kernel`, not `#![cfg(feature = "full")]` suites. Not verified by
  execution — see "what this audit did not check".
- **`env_footprint` resting on a non-discriminating command.** Zero of 1,863.
  Every matching command carries `--require-axiom-free`, which is in the
  audited discriminating set.

One near-miss worth recording rather than counting: five
`per_theorem_footprint` and six `independent_replay` rows match none of the
census's `DISCRIMINATING` patterns. Five are
`scripts/check-imported-fact-lean-axioms.sh <Name>`, which *is* discriminating
— it compares Lean's `#print axioms` against a pinned payload — so that is a
false negative in the classifier, not an overstatement. The sixth is
`scripts/check-lean-gate.sh` with **no arguments**, crediting
`F:ordered-ring-farkas-refutation` with independent replay from a gate that
says nothing about that fact in particular. That is the inheritance ADR-0760's
exit clause forbids, surviving in a `checker_command`. It is left for the
fact's owner; this lane does not edit facts.

## Decision

**The census measures two different things and must say which.**

1. **Evidence columns** answer: *does this fact's own record exercise this
   protection, on this fact's subject?* A pattern earns a place in an evidence
   classifier only if the tool it names actually performs the named protection.
   An existence-and-kind check is not a closure walk, and a dead alternative is
   removed rather than kept for symmetry.

2. **Coverage columns** answer: *did a centrally-run gate reach this fact?*
   Credit is **membership in the gate's own published per-fact set** — never
   its headline number, never a family, never a route. A gate that cannot say
   which facts it reached earns no column, and that inability is recorded as a
   finding about the gate.

3. **The two are reported separately and `protection_count` counts only the
   evidence axis.** A fact does not become better protected because somebody
   else measured it, and a count that mixes the axes cannot be read as either.

`exact_statement` moves to the coverage axis. It was never evidence: it is
manifest membership, maintained by S1's gate under a `coverage_floor` ratchet.
That is the one protection here that already satisfies rule 2, which is why it
is the only coverage column today.

### Why not one axis

*Coverage alone* is tempting — it is stronger in practice and far cheaper, and
it is what a referee should be shown. But per-fact evidence is self-describing:
it travels with the fact when the row is quoted, exported, or copied into a
paper, and it survives the gate being retired. A fact whose only protection is
a central gate is protected exactly as long as somebody keeps running it, and
nothing in the fact says so.

*Evidence alone* is what we had, and it produced a `circularity` of 38 against
a real 1,956 — a programme metric off by a factor of fifty in the direction
that invents work.

Neither dominates. Both, separately.

### Cost

Three of the four uncredited gates are cheap, and all three already compute the
set they do not publish:

| gate | what it must emit | size |
|---|---|---|
| S2 `check-trust-closure.py` | `subjects.resolved` keys to its `--json` output | one dict comprehension; the set is built and discarded today |
| S3 `check-semantic-control-fixtures.py` | `census.load_bearing` into `fixture-pack.json` (the summary markdown already renders it) | one key; the map exists in memory |
| S4 `real_lean_replay_census` | the fact→declaration join, so a NAME grade becomes a FACT grade | the join is S2's `subjects.resolved`, so it lands free once S2 emits it |

Each is owned by its own lane and none is touched here. Until they land, the
summary names them and states what each would have to emit — which is a
falsifiable ask, not a note.

S1's `check-statement-identity-mutations.py` gets no column: it is a
ledger-wide pass/fail and reading it as per-fact coverage would be exactly the
inflation this ADR exists to prevent.

## S1's control repair: reviewed, and it is weaker

S1 pinned every settled fact, which made the census-row control
`("F:nat-sumrange-add", "exact_statement", False)` unsatisfiable, and moved the
negative polarity to `UNPINNABLE_PROBE` — an id in no manifest and no ledger,
asserted absent from `statement_pinned_ids()`. S1 flagged this as "a genuinely
smaller claim than a census-row negative" and asked for review.

**It is smaller, and measurably so.** The probe watches
`statement_pinned_ids()` for something impossible. Two failures contain nothing
impossible, and both were measured surviving it, exit 0, with the column still
reading 2121/2121:

- `"exact_statement": True` written as a constant in `classify` — the probe
  never reaches `classify`;
- `statement_pinned_ids()` reading `artifacts/facts` instead of the manifest —
  a set of real fact ids contains no probe id, so the column reports full
  coverage **from no manifest at all**.

The stronger form is restored without needing an unpinned fact to exist:

- `SYNTHETIC_UNPINNED` runs the real `classify()` over a fact-shaped dict whose
  id is in no manifest and requires `exact_statement` to come back `False`.
  Kills the first.
- The manifest pins *settled* facts, so an `open` or `refuted` id appearing in
  the set proves it did not come from the manifest. Kills the second (150 such
  ids today; the control fails loudly if that population ever empties, rather
  than passing vacuously).

## Controls

`scripts/tests/test_safety_matrix.py`, auto-discovered by
`scripts/run-python-controls.py` so it runs from the moment it is committed.
Seven cases, 1.1 s, no cargo. Each mutation applied to a **copy** of the tree.

| mutation | killed by | previously |
|---|---|---|
| restore `kernel_declaration_projection` to `DEPENDENCY_CLOSURE` | `F:complex-factorquotient.circularity` | no control existed |
| `DEPENDENCY_CLOSURE` matches nothing | `F:cpoint-cauchy-schwarz.circularity` | no control existed |
| `exact_statement` a constant `True` | `SYNTHETIC_UNPINNED` | **survived** |
| pin ids read from `artifacts/facts` | unsettled-id leak | **survived** |
| `statement_pinned_ids()` returns empty | the census's fail-closed path | already covered |
| fold `COVERAGE_COLUMNS` into `protection_count` | artifact drift | no control existed |

Each kills exactly one case; measured, not asserted.

## Alternatives rejected

- **Add `check-trust-closure` to the `circularity` regex.** Changes nothing —
  no fact cites it — and would be a coverage claim wearing an evidence
  column's clothes.
- **Credit S2's 1,956 to the census directly from its summary line.** This is
  the inflation the brief warns about and the shape ADR-0760 forbids: a
  headline number conferring a grade on members it never named. S2 builds the
  fact-id set; publishing it is a small change in S2's file, and the credit
  waits for that.
- **Rename `circularity` to match what its 14 rows do.** The name is right for
  the protection the programme is measuring; the classifier was wrong. Renaming
  would preserve the classifier and lose the target.
- **Drop `semantic_falsification` to 8.** The 95 is a real, different
  measurement (facts carrying a semantic evidence row) and deleting it would
  hide the 87-row gap rather than report it. Both belong, labelled.

## Consequences

- `circularity` reads 14, not 38. This is a **reduction in claimed protection**
  and no phase's exit criterion should be read as having been met by the
  previous number.
- `protection_count` drops by one for every proved fact, because
  `exact_statement` left the evidence axis. The histogram shifts uniformly; no
  fact lost a protection.
- The summary now names the four uncredited gates and what each must emit. When
  S2 lands `subjects.resolved`, `circularity` and `per_theorem_footprint` each
  gain a coverage column at ~1,956 — and the evidence columns stay at 14 and 59,
  which is the point.

## What this audit did not check

**It never executed a `checker_command`.** Every claim above about what a
command does is read from the command text and from the source of the tool it
names. So a command that names a real closure walk but fails for an unrelated
reason — a moved artifact path, a renamed example, a suite that compiles to
zero tests — is counted here as carrying its protection. `check-lean-gate.sh`'s
skip path (`AXEYUM_ALLOW_NO_LEAN=1`, a loud banner and exit 0) is the concrete
shape this blind spot has, and the five `cargo test --lib` filters feeding
`mutation_control` were checked for the feature-gate trap by reading, not by
running. `scripts/check-fact-evidence-replay.sh` executes evidence and is the
instrument that would close this; joining its per-fact result to the census is
the natural follow-on and is not done here.
