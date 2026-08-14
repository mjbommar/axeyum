# agent-d — integration record for the Lean bridge slice

**The claim under test.** axeyum unites SAT search, proof production, proof
checking and kernel-level formal certification in one system, where the
conventional pipeline hands a solver's word to a proof assistant as an axiom.

**Verdict after this slice: the claim is now true end to end for reconstructed
theory and arithmetic refutations, and it is not yet true for the campaign's
frontier SAT claims.** The seam moved, it did not close. Below is exactly where
it sits, measured today on s0 against Lean 4.30.0 (d024af09).

## What is joined, and by what evidence

| link | mechanism | evidence today |
|---|---|---|
| SAT search -> proof production | own CDCL emits DRAT (`solve_with_drat_proof`) | existing gates |
| DRAT -> checked | own backward checker `check_drat` (RUP+RAT) | existing gates |
| LRAT -> Alethe -> kernel term | `lrat_to_alethe` + `reconstruct/resolution.rs` | `reconstruct/tests.rs:1709`, `carcara_crosscheck.rs:500` |
| kernel term -> our kernel | `axeyum_lean_kernel::Kernel` type-checks | in-process, long-standing |
| kernel term -> Lean surface | `lean_pp` module + real `lean` | **163 of 163 modules, 0 failed**, 70 families |
| kernel environment -> Lean's kernel | `lean_export` NDJSON + `Environment.addDeclCore` | **new**: 17 official fixtures + a 3,854-record axeyum development, with a tamper control |
| Lean -> axeyum | `axeyum-lean-import`, official v4.30 fixtures | 17 fixtures dual-admitted |

Before today the last-but-one row was believed broken and the last row did not
exist. Both were wrong in the same direction: the first was *already working*
for 163 modules and failed only for a parametric/indexed inductive; the second
was reachable with the installed toolchain alone.

## Against Li 2026, concretely

`crabsatellite/rado-numbers-sat`, `lean4/RadoNumbers/SAT.lean`:

```lean
axiom lem_keypair_sat (b k : ℕ) …   -- "all UNSAT under CaDiCaL 1.5.3"
```

The *mathematical content* — the SAT result itself — enters Lean as an
assertion. Every downstream theorem is conditional on it, honestly labelled
`gapOpen Cat 2 SAT-verified` in their `AxiomAudit.lean`.

What enters Lean from axeyum, measured by `#print axioms` on the real binary:

* the closed-form shell theorem: **no axioms at all**
  (`'shell_closed_form' does not depend on any axioms`, exit 0). Its `AxNat` and
  `Eq` are real Lean `inductive`s that Lean regenerates the recursors for; the
  arithmetic is proved, not assumed.
* a bit-blasted QF_ABV refutation, e.g. `qf_abv_btor_3vl1`:
  `depends on axioms: [Eq, False, α, axeyum.reconstruct.atom._0,
  axeyum.reconstruct.atom._1, axeyum.reconstruct.hyp._2, hyp._3]`.
* an LIA interpolant module: the same shape plus axiomatized ring/order lemmas
  (`Int.add_assoc`, `Int.mul_le_mul_of_nonneg_left`, `Int.no_int_between`, …).

The difference is categorical, and it is worth stating in exactly these terms:
**we never axiomatize the refutation.** The propositional/resolution structure
is a reconstructed proof term that a kernel type-checks. What our modules do
axiomatize is (a) the *hypotheses of the problem*, which is correct — a
refutation is `hyp₁ → … → False`; (b) the *signatures* of the logical prelude
when it is axiom-rendered rather than emitted as real inductives; and (c) for
the arithmetic fragments, the ring and order laws of `Int`.

(b) and (c) are real, and they are the honest counterweight to the comparison.
An axiom-rendered `False : Prop` with an axiomatized `False.rec` has the right
signature but Lean is not checking that the signature is inhabited-consistent —
that check is exactly what a real `inductive` command performs. So:

* the Rado module, after this session, is in the strong position: real
  inductives, zero axioms;
* the 163 solver modules are in the middle position: no axiomatized refutation,
  but an axiomatized logical prelude and (for arithmetic) axiomatized lemmas;
* Li's artifact is in the weak position: the result itself is an axiom.

Anyone quoting the middle row should quote it with its axiom list attached. It
is still stronger than an axiomatized SAT result, and it is not "0 axioms".

## Where the seam still is

1. **The campaign's frontier claims do not reach Lean.** `R_4(5(x−y)=4z)`,
   the off-diagonal Schur values, the cube-and-conquer covers: their evidence is
   a DRAT proof checked by our own backward checker plus an independent witness
   replay. No Lean-kernel term exists for them, and nothing in this slice
   creates one. The chain CDCL→DRAT→LRAT→Alethe→kernel term exists and is
   tested, but it has not been run at frontier scale, and the cover/cube
   structure of those claims is not yet expressible as a single refutation term.
   **This is the biggest remaining gap and it is not a plumbing gap** — it is
   proof-size and cover-composition.
2. **The Rado replay is a measurement, not yet a gate.** The committed gate
   replays a two-theorem development; the 74-record Rado replay lives in
   `logs/lean-kernel-replay.txt`.
3. **`lean_pp` still axiom-renders mutual inductives** — now an implemented and
   documented guard rather than a claimed one. The NDJSON route has no such
   limit.
4. **One wire field remains unmodelled:** `letE.nondep`, emitted `false`.

## The methodological finding, which I think outranks the code

The defect that made the flagship artifact unacceptable to Lean was a **comment
describing a check that did not exist**, in a file whose cross-check corpus was
structurally incapable of reaching that code path. Every gate was green. The
corpus was 163 modules and 70 families wide, and it could not see it, because
every fixture inductive is a flat enum.

It happened a second time the same day, in the same change: seven `(length,
hash)` pins over generated source went red, and the instrument could not tell
the reviewer whether the printer had improved or broken — a previous move of the
same pins had been resolved by writing a note beside the new number. Both are
the same failure: an assertion with nothing a reader can check it against.

`docs/prover-track/research/06-kernel-gap-analysis.md` item 7 predicted the
first in writing — widening the corpus without fixing `lean_pp`'s fallback "silently
widens the *vacuous* region". A realised prediction is much better evidence than
an argument, and the response should be structural: when a writer has a
capability guard, the corpus needs a fixture on the *far side* of that guard, or
the guard is untested by construction. That is the same rule CLAUDE.md already
states for partial operators and degenerate fuzz seeds, applied to renderers.
