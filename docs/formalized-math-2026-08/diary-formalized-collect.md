# Diary — lane `formalized-collect`, 2026-08-15

The first session of the `docs/formalized-math-2026-08/` strand. Its brief was
to start from a measurement rather than a plan. This is what the measurements
said, including where they contradicted the documents I was sent to implement.

## 1. The importer works. The kernel is what stops.

I expected the opposite. The strand's documents frame the risk as *scale* —
8.4 M edges, materialisation walls, arena growth — and the honest banner on the
README says the ingest path "works on toy inputs and has never been pointed at a
population."

So I pointed it at real Lean. There was already a `lean4export` binary built on
this box at commit `a3e35a58` under the pinned 4.30.0 toolchain (from the
tl0.7.4 acceptance run in July), and an elan toolchain at
`~/.elan/toolchains/leanprover--lean4---v4.30.0`. Exporting one theorem takes
about half a second:

```sh
lake env ./.lake/build/bin/lean4export Init -- Nat.add_comm > /tmp/x.ndjson
```

I did that for 40 well-known `Init`/`Std` theorems and ran each through
`cargo run -p axeyum-lean-import --example lean4export_import`.

**13 admitted. 27 declined. Every single decline came from
`Kernel::add_declaration`, and not one from the reader.** No `Unsupported`
record, no `Malformed`, no limit hit, at any size from 6 KB to 500 KB. The
format profile, the name/level/expression tables, the inductive and quotient
packaging all handled genuine Lean output.

The declines cluster into four things, and the first one is the whole story:

- **`Nat.add` does not reduce.** `Nat.add` is compiled through `Nat.brecOn` /
  `Nat.below` / `Nat.add.match_1`, and `Nat.add_succ` is proved by `rfl`. Our
  kernel returns `DeclarationValueMismatch` on the theorem and `TypeMismatch` on
  the `._f` auxiliaries. 15 of the 27 declines are this.
- **`eq_of_heq`** — `HEq` elimination. 5 declines.
- **`noConfusion` auxiliaries** — `_private.Init.Prelude.0.noConfusion_of_Nat.aux._f`.
  5 declines.
- 2 others.

The consequence I did not expect to have to write down: **`Nat.add_comm`, the
most cited theorem in our own fact ledger, cannot be imported.** We proved it
ourselves; we cannot check Lean's proof of it. That is a much more interesting
sentence than any corpus size, and it inverts what `01-collect.md` said to do
first. Cloning Mathlib before this is closed would be collecting to look busy.

It also means a *fail-closed* importer is the wrong instrument for measuring
coverage: at a 13/40 rate it reports the first blocker in a stream and stops.
`03-integrate.md`'s S2 ("make declines first-class") is not a refinement of S1 —
it is the only way to size the remaining work. I moved it ahead in both docs.

## 2. What I landed, and the one decision it forced

Five facts, end to end, each citing a SHA-256-pinned stream committed under
`artifacts/lean-imports/` with a manifest recording exporter commit, Lean
version, Lean githash, format version, the exact reproduction command, and a
verified determinism check (each stream re-exported byte-identically).

The decision: **an imported declaration is not the same epistemic object as one
we proved**, and `proof_route: kernel-lean` would have said it was. The gate is
literally the same function — `Kernel::add_declaration` re-derives the type from
the proof term either way — so the temptation to reuse the label is real, and
that is exactly why it needed an ADR rather than a judgement call. ADR-0454 adds
`imported-kernel-lean`, keeps it out of `AXIOM_FREE_CAPABLE`, and makes
`provenance.prior_art` mandatory on it. Three negative controls confirm all
three rules fire.

The footprint on this route names the assumptions the import adds and the
constructed route does not: exporter faithfulness, our wire translation, and —
the one I would have missed if the crate's own docs had not said so — that the
delivered bytes are the producer's intended export, because format 3.1 has no
footer.

**A sixth fact was written and then withdrawn.** `Nat.not_succ_le_zero` imported
cleanly and I had the file on disk before checking whether we already held it.
We do: `nat_theorem_inventory` lists it among 119 theorems in our own Nat
prelude, and `theorem_axiom_footprint` reports `0` for it. Landing it as an
import would have understated what this project holds, and it would have made
the ledger's route counts read as though the import were the only evidence. I
replaced it with `Nat.le_succ`, which our prelude does not have.

The same check corrected a claim I had already written into `F:nat-le-refl`'s
notes: that our Nat prelude "does not yet carry an order relation at all." It
carries a substantial one — `le_antisymm`, `le_total`, `le_dest`,
`le_of_mul_le_mul_left`. What is true is narrower and had to be verified by
name: `Nat.le_refl` itself is absent. One command would have told me; I wrote
the sentence first. The note now says so.

And the two `Nat.not_succ_le_zero` are the same *proposition* under two
different *statements* — ours over the kernel's own `Nat.le`, Lean's through the
`LE` type class as `LE.le.{0} Nat instLENat`. So they could not have been merged
into one fact even if I had wanted to. That is `02-synthesize.md`'s alignment
problem, arriving on the first five imports rather than at population scale.

## 3. The finding I would have shipped a lie about

`Kernel::render_lean` rewrites a root `Nat` to **`AxNat`**. It does that for a
good reason in the direction it was written for: emitting *our* prelude to a
real `lean` binary must not shadow Lean's builtin `Nat`, which has literal and
`OfNat` kernel support, and a shadowing module is rejected.

Applied to an *import* it is exactly backwards. The `Nat` in an imported stream
**is** Lean's builtin `Nat`, so the rendered statement names a constant that
does not exist. Had I pasted `render_lean` output into `formal.statement` the
way `int_theorem_inventory` is meant to be used, three of the five facts would
have carried an unparseable statement, and the fact ledger's whole promise is
that `formal.statement` is the proposition as the kernel admitted it.

The test now pins **both** strings — the verbatim render and the un-shadowed
form the fact carries — with the reason in a doc comment. I did not change
`render_lean`; it belongs to another lane and it is right for its own direction.

## 4. The two kernels do not agree on how to spell a footprint

`Classical.em` was chosen for the footprint, not the theorem, and it paid off:

- Lean 4.30.0 `#print axioms Classical.em` → `[propext, Classical.choice, Quot.sound]`, three names.
- `Kernel::axiom_footprint` on the imported declaration → six names, adding
  `Quot`, `Quot.mk`, `Quot.lift`, because our kernel classifies the whole
  quotient package as `Declaration::Quotient` and counts all of it as trusted.

Both are correct in their own vocabulary and ours is the more conservative one.
The fact records both and reconciles neither. `04-implement.md`'s operational
test ("if importing would enlarge the axiom footprint of a certificate we ship,
build it instead") now has to name *which kernel's* footprint, or it silently
compares two different numbers; I added that caveat there.

I also wrote `scripts/check-imported-fact-lean-axioms.sh` so the Lean side is a
real second checker rather than something I typed from memory. It discovers the
toolchain the way `check-lean-gate.sh` does (elan does not put `lean` on
`PATH`, and "`which lean` printed nothing" is how a whole gate went inert here
before), fails closed with no toolchain unless `AXEYUM_ALLOW_NO_LEAN=1`, and
refuses to exit 0 having examined zero declarations. Controls run: absent-Lean
exits 1; a wrong marker makes the cargo-test grep fail.

## 5. What the strand's own documents got wrong

Full table at the bottom of `01-collect.md`. The ones that would have cost real
work:

- **Mathlib "232,000 theorems"** was about a year stale; `mathlib_stats` says
  284,457 (with 135,592 definitions), and the arXiv:2604.24797 figure of 308,129
  *declarations* does not reconcile with it — different snapshot, different
  definition. Both are cited with dates now instead of averaged.
- **"There is no published bulk `lean4export` dump of Mathlib."** Confirmed by
  search; LeanDojo Benchmark 4 is tactic/proof-state data and is not a
  substitute. So the export must be produced, and its size is genuinely unknown.
- **OpenTheory** was described as a working path "not ours to build." The
  repository is live, but its newest packages date to ~2020 and the
  `gilith/hol-light` export fork was last pushed 2020-02-12 while mainline HOL
  Light ships weekly. Test it before planning a phase on it.
- **AFP licence** is per entry (BSD-style *or* LGPL), not "BSD-style terms" —
  the kind of thing a licence review would have caught late.
- **Mizar** was called "more restrictive"; it is dual GPL-3.0+ / CC BY-SA 3.0,
  i.e. copyleft and redistributable under those terms. Its size figures could
  not be verified at all — both primary sites refused connections.
- **`lean4checker` is archived.** Our pin (Lean 4.30.0) is four releases behind
  `lean4export` HEAD (`v4.34.0-rc1`), though format 3.1.0 is still current, so
  the reader's profile is fine and only the toolchain pin is stale.
- **OEIS licence is contested** (CC BY-NC 3.0 vs CC BY-SA 4.0 + EULA). NC vs SA
  is a materially different obligation and the draft did not mention it.

## 6. What I did not do

- No Mathlib clone, no `/nas3` corpus download. See §1: it would be collecting
  ahead of the constraint.
- No fix to the kernel blockers. They are `crates/axeyum-lean-kernel/`, another
  lane's file, and that lane has uncommitted WIP in the tree right now (which is
  also why `cargo clippy -p axeyum-lean-import --all-targets` currently fails on
  a `dead_code` error in `int_prelude` that is not mine).
- No decline census. It is the next task and it is cheap; §1 says why it comes
  before any bigger slice.
- No decision on how an import and a local proof of the same proposition should
  relate in the ledger. ADR-0454 records the question and declines to settle it.

## Next

1. **Decline census** over a few hundred `Init` declarations, reporting blocker
   clusters — the number the kernel lane can work against.
2. **`brecOn`/`below` reduction** is the single highest-value kernel gap this
   strand can name: it unblocks 15 of 27 observed declines, `Nat.add_comm`
   among them.
3. **Re-pin the toolchain deliberately** (4.30.0 → current), once, on purpose:
   every committed stream re-exports and every pinned SHA-256 changes.
