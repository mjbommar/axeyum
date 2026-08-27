# 298 — Mechanical fact registration: making the formulaic part formulaic

Date: 2026-08-27
Lane: fact-gen
ADR: [ADR-0607](../research/09-decisions/adr-0607-generated-facts-declare-themselves-and-coverage-ratchets-on-two-numbers.md)

## Task

[297](297-ledger-coverage-gate.md) measured the gap and gated it: **1,397 kernel
theorems, 474 registered, 923 unregistered — 34%.** Six ledger batches before it
each hand-picked and hand-wrote 12–30 facts, so the backlog is thirty more
batches and it grows every time a lane lands a theorem. This lane builds the
generator, decides what it may and may not claim, and runs it for real on the
one prelude at a genuine zero.

## What is derivable, and it is nearly everything

`kernel_declaration_projection`'s unfiltered emit prints one eight-field TSV row
per declaration: `prelude · kind · display name · axiom-footprint size · direct
type declarations · direct declarations · direct theorems ·
Kernel::render_lean(ty)`. From one row:

| fact field | derived from |
|---|---|
| `formal.statement` | field 8 verbatim, prefixed `theorem <display name> : ` |
| `formal.kernel_theorem` | field 3 |
| `formal.free_symbols` | binder names parsed from field 8, first-appearance order |
| `formal.fragment` | the prelude's entry in `PRELUDE_CONTRACT` |
| `axiom_footprint` | field 4, and **only** when it is 0 |
| `depends_on` | field 7, mapped through the ledger's own join, kept where registered |
| `epistemic_status`, `proof_route` | constant for this class (`proved`, `kernel-lean`) |
| both `checker_command`s | one settled shape each |
| `provenance.established_by` / `.source` | the prelude's builder and this command |

The join — "which theorem is this fact about" — is **imported** from
`gen-ledger-coverage.py` rather than re-implemented, which in turn imports
`theorem_of` from `check-fact-depends-derived.py`. Three consumers, one
definition; a fourth copy would silently diverge.

## What it refuses to derive, and why each refusal is real

**The mathematical characterisation.** A generated `title` and `statement` may
name the theorem, its prelude, its admission gate and its measured footprint,
and may point at `formal.statement`. They may not say what the theorem *means*.
The emitted `statement` opens `MECHANICALLY GENERATED, UNREVIEWED PROSE — this
sentence deliberately makes NO mathematical characterisation of the theorem`, so
the restriction travels with the file.

This is the judgement the task was really testing, and the tempting wrong answer
is a *readable* generated sentence — "states an equality between `append (append
a b) c` and `append a (append b c)`". That is a re-rendering of
`formal.statement` wearing prose clothes, and the moment it reads as
mathematics a reader can no longer tell where transcription ends and
interpretation begins.

**The commentary.** Six batches recorded things a generator cannot invent: *this
bound is loose and does not pin the sign*; *the global version is FALSE for an
arbitrary witness*; *domain-restricted*; *the ninth slice, and the one that
closed it*. Their absence must be visible rather than implied, so generated
`notes` say, in the file: **NO CURATED COMMENTARY EXISTS FOR THIS FACT. Its
absence means nobody has looked, NOT that there is nothing to say.**

**`external_status`.** Omitted, never guessed — the schema already reads absence
as "nobody has looked". `--audit` rejects a generated fact that carries one.

**A non-zero axiom footprint.** The projection prints the footprint *size*, not
the axiom *names*, so `axiom_footprint` could only be filled by guessing, and the
entire value of that field is that it was measured. Declined with the reason.

**A prelude outside `PRELUDE_CONTRACT`.** That table is the claim that a
falsifiable whole-prelude footprint checker exists under one of
`nat_axiom_inventory`'s own labels. Without it `--require-axiom-free <label>`
errors, and a checker that errors for the wrong reason is not evidence.

**A name whose spelling it cannot confirm.** `lean_pp` prefixes an all-digit name
component with `_` on export, so `axeyum.string.2.append_assoc`'s namespace is
spelled `axeyum.string._2.` inside its own type body. That is a RULE the script
applies, so it is *checked* against the body and refused when absent — and the
`_2` mapping is disclosed in every affected fact's `notes` rather than left as a
discrepancy a reader has to work out.

## The provenance marker

Inside `provenance` — the one `additionalProperties: true` object in the schema,
and the semantically right home:

```json
"curation":     "generated-unreviewed",
"generated_by": "scripts/gen-kernel-facts.py"
```

**Two keys because they decouple.** `generated_by` records what wrote the
skeleton and stays true forever; `curation` records whether anyone vouched for
the prose. A lane that enriches a generated fact flips `curation` to `curated`
and `generated_by` stays accurate. One key would force that lane to delete a true
provenance statement or leave an enriched fact indistinguishable from an
unreviewed one.

The marker is load-bearing rather than decorative because `--audit` re-derives
the prose the generator would emit and requires a **byte-identical** match while
`curation` says generated. Hand-edited prose therefore cannot sit under a
generated marker. Full reasoning and the alternatives considered: ADR-0607.

## The pilot: string, 0/64 → 64/64

64 kernel theorems, **64 planned, 0 declined**. All 64 pass the schema and the
semantic validator (882 facts, 0 errors).

Coverage moved **474/1,397 → 538/1,397**, 34% → **38.5%**, with `string` the only
row that changed:

| prelude | kernel theorems | registered | unregistered |
|---|---:|---:|---:|
| creal | 369 | 132 | 237 |
| nat | 329 | 86 | 243 |
| rat | 244 | 116 | 128 |
| integer | 153 | 53 | 100 |
| complex | 117 | 36 | 81 |
| cpoint | 89 | 27 | 62 |
| **string** | **64** | **64** | **0** |
| logic | 32 | 24 | 8 |
| **total** | **1,397** | **538** | **859** |

### One real defect found by registering them

`validate-facts.py`'s `KERNEL_THEOREM_RE` rejected all 64. Its namespace
allowlist contains `Str` — the carrier *type's* short name, which matches no
declaration this kernel admits — and never contained `axeyum.string.<N>`, the
prelude's actual namespace. One narrow alternative was added, and nothing else:
`theorem_of` returns `formal.kernel_theorem` verbatim when the key is present, so
no consumer needed changing and the two files cannot diverge on this.

It survived because the ledger registered zero string theorems. **An allowlist is
only tested by the names someone tries** — the coverage trap one level down.

## The checkers were executed, and shown able to fail

**Executed.** All 64 facts × 2 evidence rows = **128 commands run, 0 failed.**
Not sampled; every one.

**Able to fail — kernel side.** In an isolated snapshot
(`scripts/lane-snapshot.sh`, never the shared checkout), `append_assoc`'s
interned name was renamed and the kernel rebuilt:

```
axeyum.string.2.append_assoc          count=0   exit=1   <- the mutated theorem, FAILS
axeyum.string.2.append_nil            count=1   exit=0   <- control, same binary, same run
axeyum.string.2.append_assoc_MUTANT   count=1   exit=0   <- still there, under its new name
```

The third line is what makes the first mean something: the failure is the
**name**, not a broken build or a lost proof. Without a control in the same run,
a failing checker is indistinguishable from a bad path — the
"empty grep reported as a negative result" trap.

**Able to fail — footprint side.** `--require-axiom-free string` exits 0 (a
genuinely empty trusted surface), `axreal` exits 1 (30 axioms), and a prelude the
run never built exits 1 rather than passing on zero rows.

**Able to fail — the audit gate, on the real committed tree**, not only against
fixtures:

| perturbation of one real fact | audit |
|---|---|
| hand-enrich the title, leave `curation: generated-unreviewed` | exit 1 |
| add `external_status: proved` | exit 1 |
| replace the checker with one that exits 0 on completion alone | exit 1 |
| hand-enrich the title **and** flip `curation` to `curated` | exit 0 — permitted |

The last row is the design working: enrichment is allowed, and required to
declare itself.

## Mutation controls

`scripts/tests/mutation_controls.py kernel-facts` — 13 guards over 32 tests,
baseline green, **13 killed**. Eleven kill exactly one test. Two — the
`[[:space:]]` anchor and `grep -c` — kill four, and the overlap is structural
rather than sloppy: `ALLOWED_CHECKER_SHAPES` is the *audit* half of the same
contract the emitter implements, so changing the emitted command also makes every
generated fixture fail the audit. Splitting them to get a clean 1:1 would mean
letting the emitter and the audit disagree about what a valid checker looks like,
which is a worse property than an impure control. Recorded in the registration
comments rather than papered over.

Two tests run `/usr/bin/grep` against the emitted pattern rather than asserting
its text — deliberately the system grep, not the interactive `ugrep`-backed
function. Asserting the text would not have caught the 54-fact `\t` incident;
running it does.

## The ratchet: recommended, on two numbers

Yes — but not on one number, because a single coverage ratchet creates exactly
the incentive to generate junk to clear it. Ratchet `registered` (any provenance)
*and* `curated` (provenance not `generated-unreviewed`) separately. Generating
moves the first and not the second, so bulk generation cannot masquerade as
curation; it is permitted and visible. Combined with the checker-shape audit,
junk cannot clear the ratchet at all. The `curated` counter needs a small
addition to `gen-ledger-coverage.py`, deliberately out of this lane's scope and
recorded in ADR-0607 as the follow-up.

## What was NOT done, deliberately

* **No prelude beyond `string` was generated.** The pilot was chosen for a
  genuine zero and a uniform shape; running `nat` (243 unregistered) or `creal`
  (237) is a separate act that should follow the ratchet decision, not precede
  it. The generator already accepts them.
* **No prose enrichment.** Every one of the 64 is `generated-unreviewed`. A lane
  that knows the free monoid can enrich them and flip the marker.
* **`gen-ledger-coverage.py` and `fact-frontier.py` untouched.**
  `validate-facts.py` received the one allowlist alternative registration
  required, and nothing else.

## Scope

New: `scripts/gen-kernel-facts.py`, `scripts/tests/test_gen_kernel_facts.py`,
64 `artifacts/facts/F-string-*.json`, ADR-0607, this file. Modified:
`scripts/tests/mutation_controls.py` (one suite), `scripts/validate-facts.py`
(one regex alternative), `artifacts/ledger-coverage.json` (regenerated),
`scripts/check.sh` and `justfile` (two registration lines each, beside the
existing `gen-ledger-coverage` step).
