# Notes: 302-mirror-statement-repair

Detail moved out of [`../status/302-mirror-statement-repair.md`](../status/302-mirror-statement-repair.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Cross-check, a third independent artefact.** For 14 of the 19,
`mathlib-nat-int-candidates-v1.json` and `mathlib-nat-int-reviewed-nursery-v1.json`
carry the statement TEXT, and it is **byte-identical to the creating commit** in
all 14. The remaining 5 (`coprime_of_dvd_left`, `coprime_of_dvd_right`,
`dvd_two_of_totient_le_one`, `prime_dvd_iff_not_coprime`, `totient_eq_one_iff`)
came from later draws whose artefacts carry only the hash -- which still
verifies them exactly. **No row disagreed**, so no stop-and-report was needed.

The fact ids make the mapping unambiguous: `F:ml430-nat-coprime-add-self-left-`
**`5e93448c`** is the first eight hex of candidate id
`5e93448cb7efe3271a259cd7b9a7eec5…`.

## The repair

Per fact, five surgical substitutions:

| field | before | after |
| --- | --- | --- |
| `formal.statement` | the kernel rendering | the pinned Mathlib proposition |
| `formal.language` | `lean4` | `lean4-surface` |
| `formal.kernel_statement` | -- | the kernel rendering |
| `formal.free_symbols` | `["x0", "x1"]` | removed |
| `notes` | "`formal.statement` IS the render_lean output" | corrected to name both fields |

`free_symbols` goes because `x0`/`x1` are `render_lean`'s generated binder
names -- they describe the rendering, not the surface statement -- and 354 of
355 healthy mirrors omit the key. `language` moves because all 355 healthy
mirrors use `lean4-surface`; `lean4` means Lean **kernel core** in this schema,
so leaving it would assert the mirror states our rendering.

**Never a JSON re-dump.** Every edit is a byte-level substitution of an
exactly-located span, and the applier proves it with a **line-granularity mask
diff**: every line outside the intended keys byte-identical, and every changed
line carrying one of the six named keys. The check is not decoration -- it
caught the `free_symbols` array's continuation lines (`"x0",` on its own line)
on the first run, in 11 of 19 files.

## Should any of the 19 keep the kernel rendering? No, and here is why

**199 healthy `ml430` mirrors are `epistemic_status: proved` and still carry
the Mathlib surface statement.** Being proved is not what distinguishes the 19;
there is no class of mirror for which the kernel rendering is the right
top-level content. Repaired uniformly.

Several of the 19 carried an explicit `notes` sentence justifying the
substitution -- "`Nat.Coprime` has no separate name in this kernel's Nat
prelude … so `formal.statement` is the actual kernel-core `render_lean` output".
The *observation* is true and worth keeping; it is the reason the rendering
differs. It is not a reason to overwrite the claim, and now it does not have to
be: the notes were rewritten to name both fields.

## A second, milder class found while measuring -- and repaired

Four mirrors' statements are **not** kernel renderings and are **not** the
pinned text either:

```
F:ml430-nat-choose-mono            ∀ (b : ℕ), Monotone (fun a : ℕ => a.choose b)
                          pinned:  ∀ (b : ℕ), Monotone fun a => a.choose b
F:ml430-nat-clog-antitone-left     … AntitoneOn (fun b : ℕ => Nat.clog b n) …
F:ml430-nat-fib-add-two-strictmono StrictMono (fun n : ℕ => Nat.fib (n + 2))
F:ml430-nat-log-antitone-left      … AntitoneOn (fun b : ℕ => Nat.log b n) …
```

A redundant type ascription and a pair of parentheses added by the fact's
author. Semantically identical; not verbatim.

**These are drift-at-BIRTH, not overwrite** -- the creating commit equals the
current content in all four, so they are a genuinely different (and milder)
failure from the 19. I repaired them anyway, and the reason is structural
rather than tidiness: with them fixed, the new gate can enforce the hash check
**exactly**, over every pinned row. Leaving them would have required an
exemption list, which is the shape this repository calls a checker that cannot
fail.

## Where the kernel type now lives

`formal.kernel_statement` (new, `artifacts/ontology/fact.schema.json`, which is
`additionalProperties: false`, so this is a deliberate schema change).

The division the field's description states: **`statement` is WHAT IS CLAIMED,
in the vocabulary the claim was made in; `kernel_statement` is HOW OUR KERNEL
SPELLS IT.** They are frequently different strings for the same proposition --
`Nat.Coprime` is spelled inline as `gcd _ _ = 1` here -- and that difference is
exactly what a reviewer wants to see, not a discrepancy to hide by overwriting
one with the other.

It exists because lanes clearly *want* to record the rendered type: that
impulse is why this recurred 1 -> 3 -> 19, and a gate without an outlet would
have produced the same drift somewhere else.

## The gate

`scripts/check-mirror-statement-fidelity.py`, registered in **both**
`scripts/check.sh` (step `mirror-statement-fidelity`) and the `justfile`
(`facts` recipe). `scripts/check-control-registration.sh`: `orphans=0`,
`py_orphans=0`.

```
MIRROR_STATEMENT_FIDELITY|facts=2114|mirrors=374|hash_verified=362|unpinned=12|violations=0|verdict=PASS
```

Nine guards:

| | guard | why it exists |
| --- | --- | --- |
| G1 | no leading `theorem `/`def `/`axiom `/… | `render_lean` prints a DECLARATION; a mirror states a TYPE |
| G2 | no `AxNat`/`AxInt`/`AxRat`/`AxReal`/… | `lean_pp` carrier roots; Mathlib says `ℕ`, `ℤ` |
| G3 | no `Eq.{1}` / `Sort.{u}` | surface output suppresses universes; `render_lean` emits them |
| G4 | no `(x0 : ` binders | `render_lean`'s generated names |
| G5 | `formal.language == "lean4-surface"` | `lean4` asserts the statement IS kernel core |
| G6 | `sha256(statement)` == the preregistered pin | **exact**, where a pin exists (362 of 374) |
| G7 | `kernel_statement` requires `kernel_theorem` | ledger-wide, not mirror-scoped |
| G8 | scope selector found a nonzero number of mirrors | a gate that read nothing reports green |
| G9 | the hash check verified a nonzero number of rows | independent of G8: a broken catalog lookup silently downgrades this to a token screen |

**Why a hash guard and not only a token screen.** A token screen catches the
observed defect and nothing else. It cannot see a statement replaced by a
DIFFERENT plausible Lean statement -- the same integrity failure with better
camouflage -- and G6 is what found the four ascription drifts above. The token
guards stay because the 12 `ml430-mutation-*` facts (deliberately mutated
propositions) have no pin by construction and nothing else would cover them.

**Why G9 is separate from G8.** They fail for different reasons and only one is
visible in the output. A broken scope selector prints `mirrors=0`; a broken
catalog lookup prints `mirrors=374` and every other line unchanged, while
having silently stopped doing the exact check. G9 is guarded on `mirrors > 0`
precisely so a zero-mirror run does not trip both and make each unkillable.

**Scope stops at `F:ml430-` (a prefix, not a substring).** Facts outside the
mirror programme legitimately carry `render_lean` output -- `fact.schema.json`
says `lean4` "means Lean **kernel core** … the form a fact should normally
carry". Running these guards ledger-wide would flag the correct majority, which
is the fastest way to make a gate ignored. G7 is the one rule that IS
ledger-wide, and its control uses a deliberately non-mirror fixture to prove it.

## Mutation results

`python3 scripts/tests/mutation_controls.py mirror-statement-fidelity`, entry
added to `SUITES`; `__pycache__` cleared between runs (the stale-`.pyc` trap):

```
baseline green, 18 tests
  G1 … killed 1: test_g1_declaration_keyword_is_rejected
  G2 … killed 1: test_g2_kernel_carrier_is_rejected
  G3 … killed 1: test_g3_universe_annotation_is_rejected
  G4 … killed 1: test_g4_generated_binder_is_rejected
  G5 … killed 1: test_g5_kernel_core_language_is_rejected
  G6 … killed 1: test_g6_statement_not_matching_its_pin_is_rejected
  G7 … killed 1: test_g7_kernel_statement_without_kernel_theorem_is_rejected
  G8 … killed 1: test_g8_zero_mirrors_examined_is_rejected
  G9 … killed 1: test_g9_zero_hashes_verified_is_rejected
exit 0
```

**Nine guards, nine mutations, exactly one dead test each.** Fixtures are
deliberately ISOLATING: the real defect trips G1, G2, G4 and G5 at once, and a
fixture shaped like that would keep all four tests green while any one guard
survived -- coverage that was never measured.

The first run reported `G1 killed 2`, because the CLI exit-status test happened
to use a `theorem `-prefixed fixture and was a second, weaker copy of G1's
control. Its fixture now trips several guards on purpose: that test checks the
PLUMBING (exit status depends on the finding), not any one guard.

**False-positive controls (4).** The committed ledger passes with
`mirrors > 300` and `pinned > 300` (a gate firing on healthy input gets
ignored, which is the same end state as no gate); a healthy mirror alone
passes; a mirror carrying the rendering in `kernel_statement` passes -- that is
the whole point of the new field; and a non-mirror fact with `lean4` +
`render_lean` output passes, out of scope.

**Before/after on the real ledger**, which is the control neither fixtures nor
mutation can give:

```
pre-repair  (be5c0be20^)   violations=111 across 23 distinct facts   exit 1
post-repair (be5c0be20)    violations=0                              exit 0
```

23 = the 19 plus the 4 ascription drifts. Nothing else in 374 mirrors.

## Checks run (all FOREGROUND, all complete)

```
python3 scripts/validate-facts.py                            exit 0   2114 facts, 0 errors
python3 scripts/check-fact-depends-derived.py                exit 0   missing_edges=0
python3 scripts/create-autogenesis-chain-catalog.py --check  exit 0   edges=11827
python3 scripts/check-autogenesis-holdout-isolation.py       exit 0   held_out=107, verdict=PASS
python3 scripts/check-mirror-statement-fidelity.py           exit 0   verdict=PASS
python3 -m unittest scripts.tests.test_mirror_statement_fidelity      18 tests, OK
python3 scripts/tests/mutation_controls.py mirror-statement-fidelity  exit 0, 9/9 killed 1
scripts/check-control-registration.sh                        exit 0   orphans=0, py_orphans=0
python3 scripts/gen-plan.py --check                          exit 0
```

Not run, deliberately: the aggregate gate (`just check` / `scripts/check.sh`).

## What generalises

- **A "pinned artefact" may pin a HASH rather than the text, and that is
  stronger.** Both the brief and the design review said the nursery manifest
  holds the `type`; it does not, and the thing that does is content-addressed.
  Look for `*_sha256` before concluding a preregistered source is unusable.
- **A token screen for a content defect is a heuristic wearing a gate's
  clothes.** Where a content hash exists, the guard should be the hash, with the
  tokens as fallback for rows the hash cannot reach -- and the fallback's scope
  should be stated, not implied.
- **A non-vacuity guard needs one clause per thing that can go inert.** One
  `if nothing_examined` looks sufficient and is not: here the scope selector and
  the catalog lookup fail independently, the second leaves every printed number
  looking healthy, and folding them into one clause makes both unkillable by
  mutation.
- **Isolating fixtures are the price of "exactly one test dies".** The natural
  fixture is the real defect, and the real defect trips four guards at once.
