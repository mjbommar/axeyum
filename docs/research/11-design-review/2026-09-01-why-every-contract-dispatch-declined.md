# Why every producer-contract dispatch declined — and why the loop stayed quiet

Date: 2026-09-01
Lane: `contract-declines`

## Question

On 2026-08-27 the autogenesis loop dispatched 27 facts through its two
producer contracts. All 27 declined (15 `TrustedDeclaration`, 12
`TerminalNotClosed`), and the loop has produced nothing since. Is it

- **(a)** the two contracts are aimed at the wrong shape,
- **(b)** one specific capability is missing that every dispatch hits, or
- **(c)** something else?

## Verdict: (c)

Neither (a) nor (b) survives measurement.

**Not (a).** Both contracts' shape predicates matched exactly the family
members they claimed and nothing else. `int-modeq-family-v1` matched 12
`Int.ModEq` facts; `nat-coprime-family-v1` matched 15 `Nat.Coprime` facts;
the non-example guards in `scripts/validate-producer-contracts.py` fired
correctly, and the `title_prefix` clause structurally excluded every
outcome-blind mutation fixture. The shapes were right. What was wrong is one
level up: a contract asserts that a *recipe* discharges a *shape*, and both
contracts named `crates/axeyum-lean-import/examples/modeq_family_operation.rs`
as that recipe. That producer's entire vocabulary is refl / symm / trans /
`Iff.intro` **over equalities already handed to it as hypotheses**. It can
permute a given equality; it cannot derive a new one. The family members it
can permute (`refl`, `symm`, `trans`, `comm`) had already been proved before
either contract was written, so each contract's shape necessarily covered
exactly the complement of its recipe's competence.

**Not (b).** There is no single capability every dispatch hits. There are
four structurally distinct blockers across two different pipeline stages, and
two of the four are architecturally permanent under this kernel's design
while a third is a large engineering programme and the fourth is a different
programme again. The typed reason codes hide this: `TrustedDeclaration` is
not a producer decline reason at all — for all 15 nat-coprime facts the
producer never ran.

**(c), stated precisely.** Three things are true at once, and only the third
explains the silence:

1. All 27 declines were honest and are still reproducible today, byte for
   byte (§3).
2. **26 of the 27 declined facts are now `proved`** — closed within days by
   hand-authored kernel declarations that never invoked a producer, a
   contract, or the import pipeline (§4). The declines did not block those
   facts; they were simply irrelevant to how the facts got proved.
3. The contract layer reaches **2 of 217** dependency-ready open facts, and
   both of those 2 are the last members of the one family it describes. The
   loop is not stalled behind 27 declines; it is stalled because nobody ever
   wrote a third contract, and because the producer vocabulary has no
   overlap with the frontier's dominant shape (§5).

The flywheel arrow that is broken is not *producer → kernel*. It is
*kernel → contract*: the kernel gained the whole `Int.emod` congruence theory
on 2026-08-27 (`crates/axeyum-lean-kernel/src/int_prelude/modeq_family.rs`,
40 `declare_*` calls) and no producer, contract, or shape predicate was
updated as a consequence. The contract layer is a retrospective description
of what a producer already happened to do, and nothing forces it to track
what the system can now prove.

## 1. The 27 declines, split by stage

```sh
python3 - <<'PY'
import json, glob, collections
rows = []
for f in sorted(glob.glob('artifacts/autogenesis/*decline*.json')):
    d = json.load(open(f))
    if d.get('producer', {}).get('result') == 'declined':
        rows.append((f, d))
print(len(rows))
print(collections.Counter(d['producer']['decline_reason'] for _, d in rows))
print(collections.Counter(d['contract'] for _, d in rows))
print(collections.Counter(d['import']['result'] for _, d in rows))
PY
```

```
27
Counter({'TrustedDeclaration': 15, 'TerminalNotClosed': 12})
Counter({'.../nat-coprime-family-v1.json': 15, '.../int-modeq-family-v1.json': 12})
Counter({'blocked': 15, 'clean': 12})
```

The split by reason code is *exactly* the split by contract, and exactly the
split by import result. All 15 `TrustedDeclaration` artifacts record
`producer.module` as

> `axeyum_lean_import::import_statement_ndjson (import stage, before
> axeyum_lean_import::producers::modeq_family runs at all)`

so `propose_modeq_family` was invoked for 12 of 27 dispatches, not 27.

## 2. Root-cause table — 4 causes, not 2 reason codes

Grouped; every group is genuinely identical in cause, and the group counts
sum to 27.

| # | stage | reason code | first blocker / mechanism | facts | disposition |
|---|---|---|---|---:|---|
| G1 | import | `TrustedDeclaration` | `Quot` (Quotient primitive) reached through `Nat.minFac` | 1 | **permanent** — a quotient primitive is never exempted, by hard rule |
| G2 | import | `TrustedDeclaration` | `eq_self` (Theorem), whose only proof is `propext (…)` | 5 | **permanent** — this kernel deliberately has no `propext` (`crates/axeyum-lean-kernel/src/prelude.rs:61`) |
| G3 | import | `TrustedDeclaration` | `Nat.mod_lt` (Theorem), reached through `Nat.gcd`'s well-founded-recursion elaboration | 9 | **deferred, large** — the real closure needs ≥15 uncovered theorem-kind declarations including 7 WF-recursion internals |
| G4 | producer | `TerminalNotClosed` | goal needs a **new** `Int.emod` equality; the schema can only permute given ones | 12 | **deferred, large** — a different programme again |

Blocker-name counts, verbatim from `producer.decline_message`:
`Nat.mod_lt` 9, `eq_self` 5, `Quot` 1.

G1–G3 share one deeper cause: every one of the 15 statements says something
about `Nat.Coprime a b = (Nat.gcd a b = 1)`, so every one forces `Nat.gcd`'s
*value* — and hence Lean 4 core's whole WF-recursion cascade — into a stream
the v1 statement-adapter policy defines as proof-free. Which name is reported
first is traversal order, not cause. That measurement is
[doc 295](../../autogenesis/295-mod-lt-and-eq-self-cascades-are-not-a-two-name-extension.md),
which enumerated the smallest export in the family (52 theorem-kind records;
37 already covered by the four `SUBSTITUTABLE_*` lists; **15 not**) and the
largest (`nat-coprime-two-left`: **175** theorem-kind records). This lane did
not re-derive that; it verified the split is still current (§3).

G4 sub-splits by *why* the combinators cannot fire, read off the statements:

| sub-cause | facts | example |
|---|---:|---|
| unconditional — no hypothesis exists to permute | 5 | `∀ {n a : ℤ}, n + a ≡ a [ZMOD n]` |
| hypothesis exists but its sides are not the goal's sides after `whnf` | 6 | `a ≡ b [ZMOD n] → c + a ≡ c + b [ZMOD n]` |
| terminal is neither `Eq` nor `Iff` after unfold (`∣` unfolds to `∃`) | 1 | `a ≡ b [ZMOD n] → (n ∣ a ↔ n ∣ b)` |

All three sub-causes are the same missing capability at a coarser grain:
`Int.emod` congruence. The producer cannot borrow it from our prelude,
because it runs inside the isolated statement-import kernel whose environment
holds only the target definition's own elaboration closure
(`crates/axeyum-lean-import/src/producers/modeq_family.rs`, module doc).

## 3. Both declines reproduce today, on byte-identical input

The 2026-08-27 exports are still on s5 and unchanged. Their digests match the
`identity.export_ndjson_sha256` recorded in the decline artifacts, so this is
a re-run of the same dispatch, not a re-creation of it.

```sh
scp s5:/home/mjbommar/lean-import-scale/flywheel-2-exports/int-modeq-add-left.ndjson .
scp s5:/home/mjbommar/lean-import-scale/flywheel-2-exports/nat-coprime-add-self-left.ndjson .
sha256sum *.ndjson
```

```
0e26a9ce8966f711662f4b1f18e3d5236ac35279f20329a6ad95a7c224b1487f  int-modeq-add-left.ndjson
e0b56e571b9a8e0e1221e552fd4a0684308dd862234c5d8fc8fd31bc97a5f3f1  nat-coprime-add-self-left.ndjson
```

Both equal `identity.export_ndjson_sha256` in
`artifacts/autogenesis/mathlib-int-modeq-add-left-decline-v1.json` and
`artifacts/autogenesis/mathlib-nat-coprime-add-self-left-decline-v1.json`.

```sh
scripts/cargo-serialized.sh build --release -p axeyum-lean-import \
  --example modeq_family_operation
./target/release/examples/modeq_family_operation int-modeq-add-left.ndjson \
  Axeyum.Autogenesis.Statement.Generated.intModeqAddLeft
./target/release/examples/modeq_family_operation nat-coprime-add-self-left.ndjson \
  Axeyum.Autogenesis.Statement.NatCoprimeFamily.coprimeAddSelfLeft
```

```
Error: "producer declined: terminal goal is not an Eq/Iff shape this schema's
        refl/symm/trans/Iff.intro combinators can close"          (exit 1)
Error: TrustedDeclaration { name: "Nat.mod_lt", kind: Theorem }   (exit 1)
```

Unchanged from 2026-08-27. **No decline flipped.**

## 4. 26 of the 27 declined facts are now proved — by a route that ignores all of this

```sh
python3 - <<'PY'
import json, glob
byid = {}
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f))
    if isinstance(d, dict) and 'id' in d:
        byid[d['id']] = d
ids = []
for f in sorted(glob.glob('artifacts/autogenesis/*decline*.json')):
    d = json.load(open(f))
    if d.get('producer', {}).get('result') == 'declined':
        ids.append(d['fact_id'])
print(sum(byid[i]['epistemic_status'] == 'proved' for i in ids), 'of', len(ids), 'proved')
print([i for i in ids if byid[i]['epistemic_status'] != 'proved'])
PY
```

```
26 of 27 proved
['F:ml430-nat-coprime-of-lt-minfac-0f79bdba']
```

- All **12** int-modeq facts: `proved`. Closed by
  `crates/axeyum-lean-kernel/src/int_prelude/modeq_family.rs` (commits
  `36585470c`, plus the five doc 293 closed).
- **14 of 15** nat-coprime facts: `proved`, via `nat_prelude/primes.rs` and
  the ml430-mirror sweeps (`deda21872`, `92a61164e`, `935dde5e2`).
- The **one** still open is `F:ml430-nat-coprime-of-lt-minfac-0f79bdba` —
  precisely group G1, the `Quot` case doc 295 classified as permanent.

Note what this means for the framing of the question. "The minimum change
that makes one of the 27 not decline" would, for 26 of them, produce a second
proof of an already-proved fact. Only one dispatch is still on the critical
path, and it is the single member no bridging policy can ever admit.

Five of the decline artifacts already record this in an `amendment` block
("later-admission-different-route"); the other 21 do not, and nothing in
`scripts/validate-producer-contract-declines.py` requires them to. See §6.

## 5. Why the loop produced nothing: the contract vocabulary reaches 2 of 217

```sh
python3 scripts/fact-frontier.py --json
```

```
ready_count:                      217
shape_matched_count:                2
admissible_count:                   1
admissible_via_contract_count:      1
admissible_via_operation_count:     0
declined_count:                     1
declined_by_contract:  {int-modeq-family-v1: 12, nat-coprime-family-v1: 15}
unmatched_by_route_class: {no-route: 6, proof-route-only: 209}
selection.outcome:           selected
selection.selected_fact_id:  F:ml430-nat-coprime-factorizationlcmleft-factorizationlcmright-e7db70ce
```

Read those numbers together:

- `shape_matched_count: 2` — of 217 dependency-ready open facts, **two** match
  any producer contract at all. Both match `nat-coprime-family-v1`. One is
  live-declined (the `Quot` fact); the other is `admissible` and **has never
  been dispatched**. The selector's outcome is `selected`, not
  `refused-no-admissible-candidate` as it was on 2026-08-27. The loop has a
  candidate waiting.
- `declined_count: 1` against `declined_by_contract` summing to 27 — not a
  bug, the staleness made numeric. `declined_count` counts declines
  suppressing a fact that is *still ready and open*; `declined_by_contract`
  counts live `(fact, contract)` pairs regardless
  (`scripts/fact-frontier.py:1136-1150`). 27 live suppressions, 1 of which
  suppresses anything.
- `unmatched_by_route_class: {proof-route-only: 209}` — the dominant class.
  A fact is `proof-route-only` when its `formal.fragment` is `Nat`, `Int` or
  `Real` and no decision procedure applies (`scripts/fact-frontier.py:162`,
  `:806-810`), so a kernel proof is the only possible route.

Classifying those 209, verified independently of the frontier by reloading
each fact from `artifacts/facts/`:

| feature | count |
|---|---:|
| `formal.fragment` | `Nat` 135, `Int` 74 |
| `formal.language` | `lean4-surface` 207, `lean4` 2 |
| title class | Mathlib v4.30 source proposition 195, outcome-blind mutation 12, open conjecture 2 |
| statement contains `↔` | 40 |
| statement contains `∃` | 14 |
| statement contains `Decidable` | 10 |
| statement mentions a `motive` (asks for an induction principle) | 10 |
| statement contains `Coprime` | 1 |
| statement contains `[ZMOD` | 1 |
| statement contains `[MOD` | 1 |

The last three lines are the finding. The only three facts in the entire
209-fact pool that either contract's `statement_contains` clause would match
are **outcome-blind mutation negative controls**
(`F:ml430-mutation-c20db9b4…`, `-aca37b68…`, `-c86940b5…`), which both
contracts' `title_prefix` clause correctly excludes. **Both contracts' shapes
have zero remaining real targets.** The families they describe are finished.

The 195 real Mathlib-mirror targets are dominated by shapes no producer in
the current vocabulary addresses: 40 `Iff`-headed (only `modeq_family` closes
an `Iff`, and it has no applicability here), 14 existential, 10 `Decidable`
instances, 10 higher-order induction principles the producer would have to
*construct* rather than consume. A single new producer written in the current
vocabulary — the strongest being `bounded_induction`'s zero/succ structural
induction plus congruence rewrites over `Eq`-headed goals — is
shape-compatible with at most the `Eq`-headed, low-hypothesis subset, on the
order of **90 of 195 by shape alone**, and materially fewer once
`bounded_induction`'s own measured decline rate on diagonal and multi-step
recursions is applied. That is an upper bound from shape counting, not a
measured hit rate; treat it as sizing, not as a promise.

## 6. The minimum change

**To flip one of the 27: no bounded change exists, and this lane did not make
one.** Sizing, per group:

- **G1 (1 fact)** — would require exempting a Quotient primitive from the
  statement-import policy. Permanent by hard rule; also the only one of the
  27 that still matters, and even if the import passed, the producer cannot
  close `m ≠ 0 → m < n.minFac → n.Coprime m` with refl/symm/trans.
- **G2 (5 facts)** — would require adding `propext` as a genuine axiom. A
  project-level design reversal, not a lane change.
- **G3 (9 facts)** — measured at ≥15 uncovered theorem-kind declarations for
  the *smallest* export in the family, 7 of them Lean 4 core's
  `WellFounded.Nat.fix` / eager-fixpoint internals. Larger than
  `nat_order_substitution`'s existing 28 entries. Far above 200 lines.
- **G4 (12 facts)** — would require `Int.emod` congruence *inside the
  isolated import kernel*. The kernel-lane equivalent is
  `int_prelude/modeq_family.rs`, 40 declarations and ~33 KB, and the producer
  cannot cite it.

Every group is also, for 26 of 27 facts, work whose output already exists.

**To make the loop produce again: two bounded changes, neither a producer
change.**

1. **Dispatch the fact the selector already selected.**
   `F:ml430-nat-coprime-factorizationlcmleft-factorizationlcmright-e7db70ce`
   is `admissible`, dependency-ready, matched to `nat-coprime-family-v1`, and
   has sat undispatched. One lane, existing recipe. Expect a
   `TrustedDeclaration` decline for the same G3 reason — but expect it *from
   a run*, not from this document.
2. **Give a decline a lifecycle.** 26 of 27 live suppressions name facts that
   are `proved`. `scripts/validate-producer-contract-declines.py` checks that
   a decline's `fact_id` resolves to a real fact, but not that the fact is
   still open — so a decline against a settled fact is indistinguishable, to
   every checker and to the selector, from one that is suppressing live work.
   That is the "a decline artifact becomes a cheap way to make the selector
   shut up about a fact forever" failure mode the validator's own docstring
   names, materialised in its benign direction and therefore invisible. The
   fix is ~40 lines of validator plus a `resolution` block on the 21
   artifacts that lack one; it is a decision about the artifact contract, so
   it is written up as
   [ADR-1510](../09-decisions/adr-1510-a-contract-is-sized-by-the-frontier-and-a-decline-dies-with-its-fact.md)
   rather than landed unilaterally here.

The structural change behind both is what ADR-1510 decides: a producer
contract must be sized against the frontier's open population at the moment
it is written, not against the family a producer already happens to serve.
Both existing contracts were written against families that were, within days,
finished by hand — which is the strongest available evidence that the
producer/contract arrow was never the constraint on those facts.

## What did not run

- No Lean or `lean4export` invocation on s5 — the 2026-08-27 exports were
  reused, with their digests checked against the decline artifacts.
- The remaining 25 dispatches were not re-run; two representatives (one per
  contract, one per stage) were. Doc 292's table records all 27 originals and
  doc 295 independently re-ran three of the nat-coprime family on
  2026-08-27.
- No workspace test sweep, and no mutation control on any checker: this lane
  changed no Rust and no checker. It built one example
  (`scripts/cargo-serialized.sh build --release -p axeyum-lean-import
  --example modeq_family_operation`).
