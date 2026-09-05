# ADR-1666: `by axeyum` is a Lean tactic, and Lean checks the term

Status: accepted
Date: 2026-09-05
Lane: `lean-tactic`

Index-summary: `lean/axeyum-tactic` is a Lake package exposing `by axeyum`:
the tactic ships the already-elaborated goal to an Axeyum sidecar, receives a
proof **term**, and Lean's own elaborator and kernel check it — nothing the
sidecar says is believed. Eleven ℕ goals in Lean-core notation close and
eleven mutations are rejected under `leanprover/lean4:v4.34.0-rc1`. The
name-correspondence finding: a rename is not enough — axeyum applies every
lemma with all arguments explicit in its own order, so the eleven lemmas the
battery reaches route through `Axeyum.Shim` — thirteen Lean theorems proved
from core, of which ten are axiom-free and three inherit `propext`. The ℤ fragment did NOT build:
`linarith::int::prove` and `ring::int::prove` are `pub(crate)`.

## Context

`docs/math-department/14-lean-lang.md` Next Ten item 6, and reviewer 11's
(applied and computational) one-line demand: *`by axeyum` as a real tactic,
and LRAT proofs Lean consumes.* What existed before this lane:

- **C3, the thin Lean adapter** ([ADR-0935](adr-0935-the-thin-lean-adapter-composes-c2s-two-checked-paths-and-adds-nothing-else.md)):
  a Rust-side protocol and grading module composing two already-checked paths,
  with an 8-category goal pack over one subject. Its alternatives section says
  in as many words: *"No in-Lean `#tactic`/command was built — a deliberate
  C5-adjacent scope call."* Nothing on the Lean side could reach Axeyum.
- **The native producers**: `linarith`, `ring`, `simp`, `decide` and a tactic
  combinator, 18,497 lines emitting kernel proof terms
  ([ADR-1576](adr-1576-a-tactic-is-a-producer-and-its-return-is-measured-in-retired-proofs.md),
  [ADR-1582](adr-1582-the-ring-producer-over-int-and-rat-and-what-each-carrier-costs-it.md)) —
  over *this* kernel's preludes, not over Lean goals.
- **`Kernel::render_lean`** ([ADR-0604](adr-0604-lean-is-the-surface-syntax.md)),
  which renders a kernel term as Lean source, in this kernel's own spellings.

The gap was not the producers and not the renderer. It was that no Lean user
could invoke either, and — the part nobody had measured — that a term this
kernel emits does not typecheck in Lean even after the names are translated.

## Decision

**A Lake package, `lean/axeyum-tactic`, exposing `by axeyum`. Lean checks the
term; nothing else in the pipeline is trusted.**

### The trust argument, in one paragraph

The tactic serializes the already-elaborated goal, calls the sidecar, and gets
back a string. It then checks the envelope, and then hands the string to
**Lean**: `Parser.runParserCategory`, `Term.elabTermEnsuringType` at the
goal's own type under `withoutErrToSorry`, a `hasSorry` guard, a `hasExprMVar`
guard, `Meta.check`, an `isDefEq` against the goal, and only then
`MVarId.assign`. There is no `sorry` path, no `admit` path, and no `addDecl`
of an axiom anywhere in the package. Consequently:

- **Trusted:** Lean's parser, elaborator and kernel. Lean core's own library,
  through `Axeyum.Shim`.
- **Not trusted, and demonstrated not to be:** the sidecar's `status`, its
  environment identity, its term, the Rust-side translator, the Rust-side name
  map, the Rust-side printer, and this kernel's own re-check. Each of those
  can be wrong, and each way of being wrong ends in Lean refusing a term.

The **environment identity is a staleness check, not a soundness mechanism**,
exactly as ADR-0935 said for C3. It is a plain string comparison, and an
honest sidecar simply echoes back what the request carried — so it can only
fire on a response that did not come from this request. It is kept because a
stale response is a real failure mode and a cheap one to catch; it is not
counted as defence.

### The protocol

Request (Lean → sidecar, one JSON object on stdin):

```json
{"protocol": "axeyum-tactic-v1",
 "environment_id": "lean-4.34.0-rc1:axeyum-tactic-v1",
 "hypotheses": [{"name": "hab", "type": <expr>}],
 "goal": <expr>}
```

Response (sidecar → Lean, one JSON object on stdout), exactly two shapes:

```json
{"protocol": "axeyum-tactic-v1", "status": "accepted",
 "environment_id": "…", "term": "<Lean source>"}
{"protocol": "axeyum-tactic-v1", "status": "declined",
 "reason": "unknown" | "timeout" | "unsupported"}
```

Anything else is `malformed-response`. The decline vocabulary is the same
three strings as `axeyum_lean_import::thin_adapter::KNOWN_DECLINE_REASONS`,
deliberately: a bridge that could invent a fourth would make the Lean side's
`malformed-response` path unreachable.

`<expr>` is an **already-elaborated `Lean.Expr`**, serialized as a tree of
`const` / `app` / `fvar` / `bvar` / `nat`. This is the load-bearing design
choice. Shipping Lean *source* would have required a Lean parser on the Rust
side, which does not exist and is `14-lean-lang.md` item 9 — a larger piece of
work than this whole lane. An elaborated `Expr` needs none: the translator
either recognizes a node or declines `unsupported`.

The sidecar carries a hard timeout (`AXEYUM_TACTIC_TIMEOUT_MS`, default 30 s)
and always answers. A hanging sidecar is a hanging Lean session.

## The name-correspondence finding

**Measured, not assumed.** `crates/axeyum-lean-import/examples/axeyum_tactic_probe.rs`
runs the `ring` and `linarith` ℕ producers over an eleven-goal battery and
reports every kernel constant the emitted terms reference, with its type.
Result on 2026-09-05: **twenty constants.**

The first finding is the one a name search would have missed entirely: the
terms are over **`AxNat`**, not `Nat`, and every lemma is applied with **all
arguments explicit, in axeyum's own order**. Lean core takes most of these
implicitly, and in five cases in a different order. So a rename is not enough,
and the correspondence has three grades:

| grade | meaning | count |
|---|---|---|
| **structural** | Lean core has it under the same spelling, same arity | 9 |
| **exact** | Lean core has the statement with the same explicit argument order | 6 |
| **reordered** | Lean core has the statement, with different implicitness and/or order | 5 |
| **derived** | Lean core has no single constant with this statement | 0 |

The nine structural rows are `AxNat`→`Nat`, `AxNat.zero`, `AxNat.succ`,
`AxNat.add`, `AxNat.mul`, `AxNat.le`, and `Eq` / `Eq.refl` / `Eq.rec` (which
are already spelled the way Lean spells them). The six **exact** rows are
`add_comm`, `add_assoc`, `add_right_comm`, `mul_comm`, `left_distrib` and
`le_add_right`.

The eleven lemma rows go through **`Axeyum.Shim`**, which carries **thirteen**
Lean theorems: the eleven this battery reached, plus `natMulAssoc` and
`natRightDistrib`, which `ring/nat.rs`'s own emitted-term table names but no
goal in this battery exercised. Each is **stated with axeyum's exact signature
and proved from Lean core**. The shim is the
correspondence table and its own check: a wrong row makes Lean refuse the
file, and the gate is red before any tactic runs. Negative control run
2026-09-05 — flipping `natAddComm`'s statement makes Lean reject it.

The five **reordered** rows, which are the actual content of "a rename is not
enough":

| axeyum | Lean core | what differs |
|---|---|---|
| `AxNat.le.refl a` | `Nat.le.refl` | `n` implicit |
| `AxNat.le_trans a b c h₁ h₂` | `Nat.le_trans h₁ h₂` | `n m k` implicit |
| `AxNat.add_le_add_left k m n h` | `Nat.add_le_add_left h k` | proof first, `m n` implicit |
| `AxNat.add_le_add_right k m n h` | `Nat.add_le_add_right h k` | proof first, `n m` implicit |
| `AxNat.le_of_add_le_add_right k m n h` | `Nat.le_of_add_le_add_right h` | all three implicit |

### The axiom cost, which does not split where one would guess

`#print axioms` on each shim row, measured on `v4.34.0-rc1`
(`lean/axeyum-tactic/Tests/ShimCorrespondence.lean`):

- **Ten of thirteen depend on no axiom at all.**
- **Three reach `propext`**: `natLeOfAddLeAddRight`, `natMulAssoc`,
  `natRightDistrib`.

That is *five of six order rows clean and two of seven ring rows not* — the
opposite of the shape one would predict from "ordering is the classical part".
It is **Lean core's** axiom use, inherited when an axeyum statement is
re-proved from Lean's library; an axeyum-side proof of any of these is
axiom-free. Downstream, the five ring goals in `Tests/NatLinear.lean` are
axiom-free end to end and the six order goals carry `propext` through
`natLeOfAddLeAddRight`.

This is worth naming precisely because it is the first measured instance of
[ADR-1601](adr-1601-classical-logic-enters-as-a-hypothesis-not-as-an-axiom.md)'s
concern running in the *export* direction: our footprint is empty, and the
Lean-side restatement is not.

## What works, and what does not

### Fragment 1 — ℕ linear arithmetic and ring identities: **works**

Eleven goals in `lean/axeyum-tactic/Tests/NatLinear.lean`, stated in ordinary
Lean-core notation (`+`, `*`, `≤`, numerals, through `HAdd.hAdd` /
`instLENat` / `OfNat.ofNat`), all closed by `by axeyum`: `add_comm`,
`add_assoc`, `add_right_comm`, `mul_comm`, `left_distrib`, `le_add_right`,
`le_add_left`, `le_refl`, `zero_le`, `le` from a hypothesis, and `le_trans`.

The translator recognizes exactly: `HAdd.hAdd`/`Nat.add`, `HMul.hMul`/
`Nat.mul`, `Nat.succ`, `Nat.zero`, `OfNat.ofNat`, and the relations `Eq`,
`LE.le`/`Nat.le`, `LT.lt`/`Nat.lt`. The type arguments and the instance
argument of every heterogeneous operator are *checked* to be ℕ's own, not
assumed; anything else declines `unsupported`.

### Fragment 2 — the mutation battery: **works, 11 of 11 rejected**

`lean/axeyum-tactic/Tests/Mutations.lean`, the same eight categories as C3's
goal pack asked of the Lean side, plus three the Lean side makes possible
(`not_a_term`, `sorry_term`, and a real emitted term damaged in one place).
Each points `by axeyum` at a stub sidecar and pins the failure message with
`#guard_msgs`.

The distinction the battery exists to draw is **which side rejected**. Six are
rejected by the protocol check. Five — `wrong_goal`, `mutated_proof`,
`not_a_term`, `sorry_term`, and the wrong-environment case's Lean-side twin —
arrive with a *flawless* `accepted` envelope carrying the correct environment
identity: every protocol and Rust-side check passes, and the goal still does
not close. `wrong_goal` is the sharpest: the term is
`Axeyum.Shim.natAddComm a b`, a true theorem Lean is entirely happy with,
offered for the goal `a ≤ a + b`. Nothing short of elaborating at the goal's
own type distinguishes it.

A positive control (the same goal through the real sidecar, which must close)
is in the same file, because every test in it would pass with a tactic that
always failed.

### Fragment 3 — ℤ: **did not build**, and the reason is not the shim

The brief asked for ℕ *and* ℤ. ℤ did not build, for a reason found by trying:
**`linarith::int::prove` and `ring::int::prove` are `pub(crate)` in
`axeyum-lean-kernel`**, so no downstream crate can call them at all. The ℕ
entry points are `pub`; the ℤ ones are not. That is a visibility fact, not a
mathematical one, and it blocks the route before any correspondence question
is reached.

Sized, so the next lane does not re-derive it:

1. Make `linarith::int::prove` and `ring::int::{prove, prove_eq}` `pub`, and
   give `Dev` an `IntDev`-shaped sibling (`IntDev<'k>` borrows the kernel,
   unlike `NatDev`, so the bridge's `Dev` cannot simply gain a second impl).
2. Re-run `axeyum_tactic_probe` over an ℤ battery to get the constant
   inventory. **Expect a name collision the ℕ side does not have**: the ℤ
   prelude's carrier is interned as `Int`, not `AxInt`
   (`int_prelude.rs`, `let z = kernel.name_str(anon, "Int")`), so the name map cannot key on a distinguishing
   prefix and must be carrier-scoped.
3. Add an `Axeyum.Shim` ℤ section, one proved theorem per emitted constant,
   in axeyum's argument order.
4. Extend the translator with `Int` at `HAdd`/`HMul`/`HSub`/`Neg`, `Int.le`,
   and ℤ literals (`Int.ofNat` / `Int.negSucc`), each with the same
   instance-checking discipline as the ℕ side.

### Fragment 4 — an LRAT route for `Bool`/BV goals: **did not build**

Not started, and sized rather than attempted. `crates/axeyum-cnf` has a
proof-producing CDCL core emitting DRAT and an independent DRAT checker
([ADR-0011](adr-0011-drat-unsat-proof-checking.md),
[ADR-0012](adr-0012-proof-producing-sat-core.md)); Lean's `Std.Tactic.BVDecide`
consumes **LRAT**, not DRAT. So the route needs, in order: a DRAT→LRAT
conversion or a natively LRAT-emitting core; a BV/`Bool` goal fragment in the
translator (a different fragment from this one, over `BitVec`/`Bool` rather
than ℕ); and a response shape carrying a certificate *file* rather than a
term, which is a second protocol variant. That is the C5-shaped work
`14-lean-lang.md` deliberately deferred, and it should be its own lane with
its own ADR. Nothing in this ADR blocks it; the protocol's `accepted` shape
would grow a third field, not change.

## Two defects Lean found that no Rust-side test could have

Recorded because both are the kind of thing a green Rust suite says nothing
about, and both were found on the *first* run against real Lean.

1. **`@` binds to the application node, not to the head.** The printer emitted
   binary applications — `((@Eq.rec Nat) x) y` — and Lean re-inserts
   `Eq.rec`'s implicit arguments around the *parenthesized partial
   application*, so every later argument landed one slot late and the motive
   arrived where the `refl` case was expected. Applications are now printed as
   one flat spine. No Rust-side test could have caught this: the Rust side had
   a term it believed in, and the defect is entirely in how Lean reads it.

2. **The mutation battery was vacuous on its first run.** The tactic's
   optional sidecar-override argument was read as `stx[1].isStrLit?`, but
   `stx[1]` is the *optional syntax node*, not the string inside it, so
   `axeyum "stub"` silently fell back to `AXEYUM_SIDECAR` — the real sidecar —
   and every mutation "passed" by **closing** the goal it was meant to fail.
   It was caught only because `#guard_msgs` reported an *empty* message where
   an error was expected. A battery whose exit status did not depend on the
   finding would have shipped eleven unfalsifiable rejections.

## The gate

`scripts/check-lean-tactic.sh`, registered in `scripts/check.sh` and the
`justfile` beside `lean-adapter`. It:

1. resolves the pinned Lean by delegating to
   `scripts/check-lean-gate.sh --print-toolchain` — one policy, one
   implementation — and prints `AXEYUM-LEAN-TOOLCHAIN lean-tactic bin=… version=…`;
2. asserts `lean/axeyum-tactic/lean-toolchain` equals the repository pin, so
   the package cannot drift onto a different Lean than everything else
   (the two-pin distinction is [ADR-1660](adr-1660-there-are-two-lean-pins-and-every-claim-names-which-one-it-means.md);
   this package follows the **cross-check** pin, not the Mathlib corpus pin);
3. builds the sidecar rather than assuming one, so a stale binary cannot
   answer for a source tree it does not match;
4. **deletes the `Tests` build products first**, because a cached Lake module
   prints none of its `logInfo` lines and a gate reading zero would otherwise
   pass;
5. counts, with a floor on each: goals accepted (11), mutations (11), shim
   rows (13), positive controls (1). The first, third and fourth are read out
   of **Lean's own environment**; the second is counted by reading
   `Tests/Mutations.lean`, because Lean cannot count its own `#guard_msgs`
   blocks — and that the file *elaborated* is what says each one still matched
   its pinned message.

Measured 2026-09-05: `goals-accepted=11 mutations-rejected=11 shim-rows=13
controls=1`, checker
`~/.elan/toolchains/leanprover--lean4---v4.34.0-rc1/bin/lean` (commit
`3447a668783dbce1a8fdb97101dd067687b2b418`).

## Alternatives considered

- **Ship the NDJSON closure and replay it, as C2/C3 do.** Rejected for a
  tactic: `Environment.addDeclCore` adds a *declaration* to an environment, it
  does not close an open goal in a local context. A tactic needs a term over
  the goal's own free variables, and the whole point of item 6 is that a Lean
  user's goal — not a census subject — is what gets closed.
- **Rename axeyum's constants to Lean's and skip the shim.** This is what the
  measurement refuted: five of the eleven lemmas have a different argument
  order or implicitness, so a rename produces terms Lean rejects. The shim is
  the minimum honest fix, and it costs nothing in trust because Lean proves it.
- **Emit `omega` / `simp` calls instead of terms.** Rejected: it would make
  the goal close because *Lean's* automation closed it, and the claim would be
  worth nothing. A term is the only artefact that says Axeyum found the proof.
- **Depend on Mathlib in v1.** Rejected for the same reason: with Mathlib in
  scope it is not possible to tell whether a goal closed because Lean core
  admitted the term or because a Mathlib simp lemma did the work. A v2 that
  *does* need Mathlib is a real thing — see below — and it should say so.

## What a Mathlib-dependent v2 would need

Not required for the ℕ or ℤ fragments, and that is itself the finding: **Lean
core is enough for ordered-semiring arithmetic over ℕ and ℤ.** Mathlib becomes
necessary at the first goal whose *statement* is not statable in core:

- a goal over `ℚ` or `ℝ` (core has neither; the `rat` and `creal` producers
  have nowhere to land), which is where the carrier-correspondence ledger
  (`14-lean-lang.md` item 4) becomes a prerequisite rather than a nicety;
- a goal over a **typeclass-headed** structure (`[CommRing R]`), where the
  shim's "one theorem per emitted constant" shape does not apply because the
  constants are projections out of an instance
  ([ADR-1495](adr-1495-abstraction-over-structures-is-already-expressible-the-gap-is-surface.md)
  is the same gap seen from the other side);
- a goal over `Finset`, `SimpleGraph`, or any carrier where the correspondence
  is *not* "same statement" and the grade has to be recorded before a term is
  emitted at all.

In each case the addition is the same: a Mathlib section of the shim, one
proved theorem per emitted constant, and a **carrier-scoped** name map — the
same shape as the ℤ collision above, for the same reason.

## Consequences

- `14-lean-lang.md`'s K3 row can now say something it could not: there is a
  Lean-side tactic, and the producers reach Lean goals and not only this
  kernel's preludes. It remains a *fragment* claim: ℕ, quantifier-free, in
  Lean-core notation.
- The Lean boundary now has a second gate that a `lean`-less host cannot
  silently pass (`AXEYUM_ALLOW_NO_LEAN=1` prints a loud SKIP saying zero goals
  were checked).
- `Axeyum.Shim` is a new, small, Lean-checked surface. It is not a trusted
  surface: it adds no axiom, and Lean proves every row from core. Growing it
  is how the fragment grows, and each new row costs one measured `#print
  axioms` line.
- Nothing in ADR-0935 changes. C3 remains the Rust-side protocol over C2's two
  checked paths; this is the Lean-side tactic its alternatives section
  deliberately did not build. A dated cross-reference is appended to ADR-0935.

## References

- [ADR-0935](adr-0935-the-thin-lean-adapter-composes-c2s-two-checked-paths-and-adds-nothing-else.md)
  — C3, the thin Lean adapter, and the scope call this ADR closes
- [ADR-1660](adr-1660-there-are-two-lean-pins-and-every-claim-names-which-one-it-means.md)
  — the two pins; this package follows the cross-check pin
- [ADR-1594](adr-1594-the-crosscheck-pin-moves-to-lean-4-34-0-rc1-and-follows-the-pin-file.md)
  — the cross-check pin itself
- [ADR-0601](adr-0601-three-producers-one-trust-anchor.md) — producers behind
  one trust anchor; here the anchor is Lean's kernel rather than ours
- [ADR-0604](adr-0604-lean-is-the-surface-syntax.md) — Lean as the surface
  syntax, and `render_lean`
- [ADR-0517](adr-0517-lean-has-two-checkers-and-the-kernel-is-the-one-we-target.md)
  — Lean's two checkers; this tactic goes through the *elaborator* as well as
  the kernel, which is the stricter of the two
- [`docs/math-department/14-lean-lang.md`](../../math-department/14-lean-lang.md)
  — Next Ten item 6, and reviewer 11's demand
