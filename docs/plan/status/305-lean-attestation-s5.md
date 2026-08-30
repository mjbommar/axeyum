# Lane: lean-attestation-s5 -- s5 can attest, and one preregistered row is not a proposition

<!-- plan-section: lane-status -->

**Lane block (`DONE -- 159 of 160 attested, 1 rejected and recorded`,
lean-attestation-s5, 2026-08-29).**

## Headline

**s5 can do it, and it is cheap: 3.6 s for all 160 rows.** Three lanes today
worked around a missing Mathlib by inventing a weaker, labelled *quotation*
grade. That grade was honest and it was also unnecessary on this fleet.

| | before | after |
| --- | --- | --- |
| extension rows carrying a real Lean attestation | 0 | **159** of 160 |
| rows Lean REJECTS | unknown | **1**, recorded |
| grade | flat literal `"quotation"` | derived per row from the run |
| facts asserting a now-false quotation claim | 35 | **0** |
| new artifacts under `artifacts/autogenesis/` | -- | **0** (folded into the manifest) |

The row count is **160**, not the 120 the brief said: a third draw landed 40
more rows the same day.

## 1. Can s5 do it? Yes, end to end

Verified by elaborating, not by listing a build directory.

```
host            s5   (ssh BatchMode, 16 c, 27 G)
mathlib         ~/lean-import-scale/mathlib4   c5ea00351c28f...  .lake/build 6.2 GB
lean            4.30.0  d024af099ca4bf2c86f649261ebf59565dc8c622
import Mathlib + 160 proof-free axioms  ->  3.6 s
negative control                        ->  REJECTED (good)
```

The checkout's 64 `git status` entries are all **untracked probe `.lean` files**
from earlier lanes. No tracked file is modified and the commit is the one we
pin, so the checkout is trustworthy.

## 2. The finding: `Nat.le_induction` is not a well-formed proposition

**159 of 160 elaborate. One does not.**

```
F:ml430-nat-le-induction-2f088ac3   Nat.le_induction
family natural-induction-and-divisibility   partition HELD-OUT

  ∀ {m : ℕ} {P : (n : ℕ) → m ≤ n → Prop},
    P m ⋯ → (∀ (n : ℕ) (hmn : m ≤ n), P n hmn → P (n + 1) ⋯)
          → ∀ (n : ℕ) (hmn : m ≤ n), P n hmn

  error: don't know how to synthesize placeholder   ⊢ m ≤ m
  error: don't know how to synthesize placeholder   ⊢ m ≤ n + 1
```

`⋯` is Lean's pretty-printer glyph for an **elided proof term** (here `m.le_refl`
and `le_succ_of_le hn`). Re-parsed it is a hole Lean cannot fill. So we
preregistered a string that is not a proposition, and it **can never be closed
as stated**.

This is precisely the risk the quotation grade named and structurally could not
detect — *"a pretty-printed type is not guaranteed to re-parse"* — and the
per-row `source_statement_sha256` cannot see it either, because the checksum
faithfully binds a **lossy** string. Only elaboration distinguishes them.

**Confirmed in both directions**, because a parse error can desync Lean's parser
and swallow following lines:

| run | result |
| --- | --- |
| `--only F:ml430-nat-le-induction-2f088ac3` | **0 of 1** |
| `--exclude F:ml430-nat-le-induction-2f088ac3` | **159 of 159** |

**Not repaired, not deleted.** ADR-0615 forbids rewriting a preregistered
`formal.statement`; the row is held-out, so deletion is also wrong (ADR-0542:
amend, never delete). It is recorded in the manifest and in its own fact's
`notes`.

**Scope: it is the only one.** A scan for `⋯` / `✝` / `…` / `sorry` finds **1 of
160** in the extension and **0 of 216** in `nursery-v1.json` — consistent with
v1 having really been attested, and it means the defect is one row of one
family, not a systemic extraction fault.

**Next draw should screen for these glyphs at extraction time.** That is the
cheap fix and no existing check covers it.

## 3. What changed

- `scripts/attest-nursery-surface.py` (new). Runs the method the catalog's own
  `surface_validation.method` names, over ssh, against any manifest with an
  `entries` list. Maps each Lean diagnostic back to its row by line number so a
  failure names the `fact_id`. `--limit` / `--only` / `--exclude` / `--emit-only`.
  Exit 0 attested, 1 a row failed, 2 the host could not run Lean.
- `scripts/gen-autogenesis-nursery-refill.py`. `surface_validation` is now
  **derived** from a run instead of asserting a literal, as three disjoint sets
  (`attested` / `not_elaborable` / `unattested`). `--ingest-surface-attestation`
  folds in a record; `--sync-surface-notes` refreshes fact notes.
- `artifacts/autogenesis/nursery-v2-extension.json`. Carries the grade, the
  host, commit, Lean version, module sha256 and the negative-control outcome.
- 132 fact files: 97 notes rewritten from template, 35 repaired by replacing
  only the stale clause inside prose a lane wrote, 63 hand-edited left alone.
- `docs/contributor-guide/lean-surface-attestation.md` (new) + README row +
  a `fleet-hosts.md` paragraph.

## 4. Two things I got wrong, and did not work around

**The diagnostic regex could not see errors.** It demanded a bare `error:`;
Lean 4.30 emits `error(lean.unknownIdentifier):`. It matched nothing, so the
first real run reported a clean **4 of 4**. A parser blind to errors and a
genuine pass are the same output. Only the deliberately-unelaborable **negative
control** caught it — which is the standing rule about a checker whose exit
status does not depend on what the run found, arriving on my own harness within
minutes of my writing it. The control is now mandatory and the run fails if it
is ever accepted.

**The result first landed as its own artifact, and
`check-autogenesis-holdout-isolation.py` refused it** — no artifact may name a
held-out fact id except a file that defines a population, and **70 of these 160
are held-out**. I did not exempt the new file, and did not hash the ids to slip
past a syntactic walk. The grade moved **into** `nursery-v2-extension.json`,
which is already exempt and already names every held-out member it
preregistered, so it sits beside the rows it grades. The guard now passes on its
own terms: `held_out=107 files_scanned=1105 references=0 verdict=PASS`.

## 5. Why the grade is derived rather than written down

A literal cannot degrade. `"quotation"` was true when written and false the
moment a run happened — but the failure that matters is the *next* draw: new
rows would silently inherit a claim nobody ran for them. Running the generator
**without** `--ingest-…` carries the stored result forward, re-matches it
against the current entries, and drops anything uncovered into `unattested`,
flipping the grade to `mixed-real-lean-and-quotation-per-row`. Verified
byte-stable across a re-run with no ingest.

## 6. Checks, all foreground and each run bare (never after a pipe)

| check | status |
| --- | --- |
| `validate-facts.py` | **0** |
| `check-autogenesis-holdout-isolation.py` | **0** — PASS, references=0 |
| `check-dispatchable-frontier.py` | **0** — 27 dispatchable |
| `check-mirror-statement-fidelity.py` | **0** — PASS, violations=0 |
| `gen-plan.py --check` | **0** |
| manifest carry-forward idempotence | byte-stable |

**Pre-existing and NOT this lane:**
`gen-autogenesis-nursery-refill.py --check` is red on
`F-ml430-nat-totient-eq-zero-3be161d6.json` (`statement` drift), landed on main
in `defae5612` by the mirror-statement-repair lane. Untouched here.

## 7. For the next lane

- **Screen new draws for `⋯` / `✝` at extraction time.** One row got through and
  no checker could have caught it.
- **Attest every draw before dispatching against it.** It costs 3.6 s on s5, and
  it is the only thing that answers "is this even a proposition".
- **`command -v lean` is empty on hosts that have Lean** (elan keeps toolchains
  off `PATH`), and a provisioned checkout is **not** a built Mathlib. Only s5
  can do this today.
- The failing row stays open and unclosable as stated. Deciding what to do about
  it — an ADR-0542-style amendment, or leaving it as a permanent recorded
  defect — is a decision, not a lane's call.
