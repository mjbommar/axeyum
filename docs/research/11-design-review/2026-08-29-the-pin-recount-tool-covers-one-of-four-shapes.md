# The pin-recount tool covers one of four pinned-list shapes (2026-08-29)

**Measured, in the shared checkout, at `fe0e1dfee`.**

`scripts/recount-pinned-inventory.py` exists because two lanes each bumping a
pinned array length *correctly* against their own base produce a merge that
does not compile: git merges the entry lines cleanly (they are different lines)
and leaves the declared size one short. CLAUDE.md records this happening
**eight times in one day**.

The tool covers exactly one shape — `[(&str, crate::NameId, &str); N]`. A
survey of the tree finds **12 pinned-list sites across 4 shapes**:

| shape | sites | covered? |
| --- | --- | --- |
| `[(&str, crate::NameId, &str); N]` | 1 (`creal/inventory.rs`, N=432) | yes |
| `[crate::NameId; N]` | 5 (`int_prelude_tests.rs` ×4, `inductive_tests.rs` ×2 lines) | **no** |
| `[&str; N]` | 6 (`ordered_ring.rs` ×2, `complex_tests.rs`, `axreal_call_site_guard.rs`, `theorem_composition.rs`, `geometry_corpus.rs`, `geometry_certify.rs`) | **no** |

The gap is not hypothetical. Merging the `int-emod-negative` lane today hit
exactly the documented failure on `derived_laws`, a bare `[crate::NameId; N]`:
lane 151→153 (+2), HEAD 151→154 (+3), merged list 156, declared 154. The tool
was run first and answered **"no pinned inventory array found"** — a correct
answer to the question it asks, and a false negative for the question the
coordinator was asking. It had to be counted by hand.

Counting by hand is precisely what CLAUDE.md warns against, for a measured
reason: entries are **not one per line** (rustfmt wraps a long entry across five
lines starting with a bare `(`), and the obvious count — lines matching `("` —
undercounted **210 against a true 283** in one incident, with the wrong number
written into the file before the gap was noticed.

## The gap is widening right now

Five lanes are running concurrently against `nat_prelude` and `int_prelude`,
and at least three will touch a pinned list. Every pair of them that lands an
entry is a merge that compiles only if someone recounts.

## What the fix is NOT

Not simply "extend the regex to three more shapes." CLAUDE.md's own resolution
for `creal_tests.rs` went the other way, and the reasoning generalizes:

> No shard carries a pinned length, and none should be added: the length pin
> answered "is this list internally consistent", never "is it complete", and
> `creal_tests::every_creal_declaration_is_checked_and_axiom_free` already
> answers the question that matters — coverage read from `kernel.environment()`
> directly, both directions.

So each of the 11 uncovered sites needs a decision, not a regex: **is this pin
load-bearing, or is there an authority-derived assertion that subsumes it?**
A pin that constrains a list against itself while an environment-derived test
already checks completeness is pure merge friction with no diagnostic value.

This is the same defect family as the checker-that-cannot-fail: a guard whose
failures are all false positives trains everyone to resolve it mechanically,
which is exactly how a real one gets resolved mechanically too.

## Related

- `scripts/tests/test-recount-pinned-inventory.sh` — the existing controls,
  each mutation-verified.
- CLAUDE.md, "TWO LANES CAN EACH BUMP A PINNED COUNT CORRECTLY AND THE MERGE
  STILL WILL NOT COMPILE" and "AN INVENTORY TEST THAT ITERATES ITS OWN LIST
  CANNOT SEE WHAT IS MISSING FROM IT".

## CORRECTION (2026-08-29, same day): the survey above is wrong, in the worse direction

The Opus lane dispatched against this document re-measured and found **72 sites,
of which the tool covered ZERO** — not 12 sites with 1 covered.

**The 12/4/1 table above was produced by a grep that did not mask comments.**
`crates/axeyum-lean-kernel/src/creal/inventory.rs:8` is a `//!` line reading

    //! `let expected: [(&str, crate::NameId, &str); 432] = [ ... ];` covering

— a prose quote of a pin declaration in module documentation, describing the
array that was **deleted** when `creal_tests.rs` was sharded. There are **zero**
real sites of the tuple shape. So the one shape the tool handled had no live
consumer at all, which is why nobody noticed it had stopped working.

Three further corrections, all measured by the lane: `inductive_tests.rs` has no
pinned list (return-tuple components, no literal); `ordered_ring.rs` has three
sites, not two, and the third is what makes the other two load-bearing; and two
more sites exist in `geometry_corpus.rs`/`geometry_certify.rs`.

**The lesson is not about this table.** It is that a number produced by an
unvalidated grep was committed as "Measured, in the shared checkout". The grep
ran, exited 0, and printed something plausible — this repository's most-repeated
failure signature, arriving here through a survey rather than a gate. A survey
whose output will be quoted as a measurement needs the same comment/string
masking any parser does, which is precisely what the fixed tool now performs.
