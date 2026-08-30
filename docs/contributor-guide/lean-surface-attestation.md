# Attesting a nursery statement against a real Mathlib

**What this answers:** *does Lean actually accept this string as a proposition?*

Nothing else here answers it. A `source_statement_sha256` binds a row to the
extractor output byte for byte and is blind to whether that output re-parses.
A pretty-printed type is not guaranteed to be valid input, and on 2026-08-29
one preregistered row turned out not to be — see *The finding*, below.

This is **syntax/type evidence about a statement**, never proof evidence about a
claim. Acceptance settles nothing.

## The command

```sh
python3 scripts/attest-nursery-surface.py \
  --manifest artifacts/autogenesis/nursery-v2-extension.json \
  --json-out /tmp/<lane>.record.json

python3 scripts/gen-autogenesis-nursery-refill.py \
  --ingest-surface-attestation /tmp/<lane>.record.json

python3 scripts/gen-autogenesis-nursery-refill.py --sync-surface-notes
```

Step 1 runs Lean on s5 over ssh and takes **3.6 s for 160 rows**. Step 2 folds
the result into the manifest's `surface_validation`. Step 3 refreshes the
one-sentence grade claim in each fact's `notes`.

Exit status depends on the finding, not on the run completing:

| status | meaning |
| --- | --- |
| 0 | every row elaborated |
| 1 | a row did not elaborate, **or the negative control was accepted** |
| 2 | the host could not run Lean at all — a setup failure, deliberately distinct |

Useful flags: `--limit N` for a bounded subset (it prints `(SUBSET)` and says so
in the verdict), `--only FACT_ID` / `--exclude FACT_ID` to isolate a suspect row
from its neighbours, `--emit-only` to inspect the generated module without
running anything.

## The host requirement, and the probe that lies about it

You need a Mathlib checkout at the pinned commit **with `.lake/build`
populated**. As of 2026-08-29 that is **s5 only**:

```
~/lean-import-scale/mathlib4              c5ea00351c28e24afc9f0f84379aa41082b1188f
~/lean-import-scale/mathlib4/.lake/build  6.2 GB
~/.elan/toolchains/leanprover--lean4---v4.30.0
~/.cache/mathlib                          422 MB
```

`ssh s5` works with `BatchMode=yes`. The checkout's ~64 `git status` entries are
untracked probe `.lean` files left by earlier lanes; no tracked file is
modified, and the commit is the one we pin.

Two traps, both of which have already cost a lane a wrong conclusion:

- **`command -v lean` returns nothing on a host that HAS Lean.** elan keeps
  toolchains off `PATH`. An agent once declared a whole capability impossible
  from that empty result. Use `scripts/check-lean-gate.sh --print-toolchain`, or
  the explicit path above.
- **A compiled build directory is not the same claim as a working `import
  Mathlib`.** `scripts/provision-lean-import-toolchain.sh` provisions a checkout
  at the pinned commit and does **not** build Mathlib, so a host that passes
  `--verify` still cannot run this. Verify end to end, not by directory listing.

## Why the negative control is not optional

The harness injects one statement Lean **must** reject
(`Nat.axeyumThisSymbolDoesNotExist`) and fails if it is ever accepted.

That control earned its place on the first real run. Lean 4.30 tags its
diagnostics —

```
/tmp/x.lean:2:37: error(lean.unknownIdentifier): Unknown constant `Nat.axeyum…`
```

— and the first diagnostic regex demanded a bare `error:`. It matched nothing,
so every row reported as elaborated and the run printed a clean `4 of 4`. **A
parser that cannot see errors and a genuine pass produce the same output.** Only
the row that must fail distinguished them.

Generalise it: this is the repository's standing rule about a checker whose exit
status does not depend on what the run found. Any harness that classifies
external tool output needs an input whose expected classification is *failure*.

## Confirm a failure in both directions

An error can desync Lean's parser and swallow following lines, which would
report never-read rows as elaborated. So a failing run is not finished until:

```sh
python3 scripts/attest-nursery-surface.py --only  <FAILING_ID>   # expect 0 of 1
python3 scripts/attest-nursery-surface.py --exclude <FAILING_ID>  # expect N of N
```

Both were run for the finding below.

## The finding, 2026-08-29

160 rows, **159 elaborate**. One does not:

```
F:ml430-nat-le-induction-2f088ac3   (Nat.le_induction, held-out)
  ∀ {m : ℕ} {P : (n : ℕ) → m ≤ n → Prop},
    P m ⋯ → (∀ (n : ℕ) (hmn : m ≤ n), P n hmn → P (n + 1) ⋯) → …
  error: don't know how to synthesize placeholder ... ⊢ m ≤ m
```

`⋯` is Lean's pretty-printer glyph for an **elided proof term**. Re-parsed it is
a hole nothing can fill, so what is preregistered is not a well-formed
proposition and cannot be closed as stated.

It is recorded, **not repaired and not deleted**: ADR-0615 forbids rewriting a
preregistered `formal.statement`, and the row is held-out. One row of one
family, and the only one in either manifest — a scan for `⋯`/`✝`/`…`/`sorry`
finds 1 of 160 in the extension and **0 of 216** in `nursery-v1.json`,
consistent with v1 having genuinely been attested.

**Screen new draws for these glyphs at extraction time.** The per-row checksum
cannot catch it, because it faithfully binds a lossy string.

## Where the result lives, and why not in its own file

In `nursery-v2-extension.json` under `surface_validation`, as three **disjoint**
sets — `attested`, `not_elaborable`, `unattested` — plus the host, commit, Lean
version, module sha256 and the negative-control outcome.

The first version wrote a separate artifact, and
`check-autogenesis-holdout-isolation.py` correctly refused it: no artifact may
name a held-out fact id except a file that *defines a population*, and 70 of
these 160 rows are held-out. That guard exists because prose failed to hold this
line, so it was neither exempted nor routed around by hashing ids past a
syntactic walk. The manifest is already exempt and already names every held-out
member it preregistered, so the grade belongs beside the rows it grades.

The grade is **derived, never asserted**. A flat literal `"quotation"` was true
when written and false the moment a run happened, and — the part that matters
for the next draw — a literal cannot degrade: new rows would silently inherit a
claim nobody ran for them. Running the generator *without* `--ingest-…` carries
the stored result forward and re-matches it against the current entries, so new
rows land in `unattested` on their own and the grade drops to
`mixed-real-lean-and-quotation-per-row`. Verified byte-stable across a re-run.

`--sync-surface-notes` refreshes fact `notes` and is deliberately timid: it
rewrites a note only where it still matches a generated template, replaces just
the stale clause inside prose a lane wrote, and leaves anything else alone,
naming it. On the first run that was 97 / 35 / 63.
