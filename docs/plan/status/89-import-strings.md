# Lane: import-strings — Lean `String` literals type, expand, and compute

<!-- plan-section: lane-status -->

**Implemented primitive Lean `String`-literal semantics end to end — checked
bootstrap, Unicode-scalar `String.ofList` expansion, projection and recursor
hooks, the `strVal` wire arm and the writer arm — and re-censused the seeded
samples the previous lane measured** (`WIP`, import-strings, 2026-08-15).
Continues [`import-scale`](88-import-scale.md), which sized this and left it.
Full write-up:
[`docs/formalized-math-2026-08/diary-import-strings.md`](../../formalized-math-2026-08/diary-import-strings.md).
Decisions: [ADR-0366](../../research/09-decisions/adr-0366-preregister-lean-string-literal-semantics.md)
accepted; [ADR-0461](../../research/09-decisions/adr-0461-lean-string-literal-def-eq-hook-is-unreachable.md)
new.

**The bootstrap.** Official Lean inherits `String`/`String.ofList`/`Char.ofNat`/
`List` from its own boot; we import into a fresh environment, so spelling alone
would let the *stream* decide what a literal means. `String.ofList` must be a
`Definition` of exactly `List Char → String` with no universe parameters,
`Char.ofNat` one of exactly `Nat → Char` for the same `Char`, `List` the
one-parameter recursive family at universe zero with `[nil, cons]` at 0/2 fields,
and `Char`/`String` one-constructor structures named `Char.mk` and
`String.ofByteArray`. Nothing is interned: names are looked up and every
expression handle is read back out of a declared type, because minting a name
renumbers a subsequent export.

**The conversion is over Unicode scalars, never bytes:** `"é"` is one character
`0xE9`, `"🙂"` is `0x1F642`, `"e\u{301}"` stays two, and nothing is normalized.

**Lean's own def-eq hook cannot fire, and removing each hook in turn is how I
know.** `try_string_lit_expansion` keys on an immediate `String.ofList` head, but
`is_def_eq_core` runs lazy delta first and `String.ofList` is a *definition* in
4.30 — so the head is already `String.ofByteArray` by the time the hook looks.
The rule dates from when `String` was `structure String where mk :: (data : List
Char)` and that constant was a constructor. Controls: projection hook removed →
**3** tests fail; recursor hook removed → **1**; def-eq hook removed → **0**.
What identifies a literal with a constructor application is structure eta calling
the projection rule. The hook stays (it is in the pinned source and can only
accept *more*), and a test pins the *mechanism* so a toolchain re-pin that makes
`String.ofList` a constructor again fails loudly. ADR-0461.

**Negative tests.** Eleven bootstrap mutations each rejecting with
`StringLiteralBootstrapMismatch`, paired with the unmutated positive in the same
test; byte-split, reordered, truncated and composed/decomposed controls beside
every scalar positive; a bare constant and an `Opaque` alias both refused; a bare
literal not expanded by ordinary `whnf`. Our reconstruction prelude cannot
impersonate Lean's `String` **by mechanism** — its types live under
`axeyum.string.<n>` — and the test asserts the namespace, not just the refusal.

**A writer defect on the way.** `json_string` wrote `\t`/`\b`/`\f`; Lean's
`Json.escapeAux` short-escapes only quote, backslash, newline and carriage
return and writes every other sub-`0x20` character as `\u00xx`. Irrelevant while
only name components were emitted; load-bearing the moment `strVal` is, because
the difference parses identically and is not byte-identical to lean4export's.

**The ADR-0366 artifact, reproduced exactly.** That ADR froze an export it said
had never been retained or re-run. Re-exported twice from pinned Lean 4.30.0,
byte-identical, and matching all six frozen properties including SHA-256
`2404a6ca…0ab4`. It **imports clean** (290/290 records, 374 declarations, 0.04 s)
and the literal *computes*: a new probe example shows the imported
`importStringLiteral` definitionally equal to `String.ofList` over its scalars in
Lean's own environment — through the real `ByteArray`/`List.utf8Encode` — while
refusing the reordered list.

**Checked by Lean.** `real_lean_string_literal_crosscheck` (new, registered)
reads scalar lists back out of *this kernel's* reducts for ten payloads and has
Lean 4.30.0 confirm each; switching our conversion to bytes makes Lean reject.
Floor raised 107 → 109; measured 117.

**Re-census, same seeded samples, same bounds.** CLEAN `Init`+`Std` 219 -> **254
of 500**, Mathlib 78 -> **139 of 400**; `literal-string-typing` 262/315 -> **0**;
DECLINED 16 -> **242** and 7 -> **241**. So strings bought **7 and 15 points of
clean rate, not 52 and 79** — the previous lane was right to refuse to project.
What they really bought is that **18.6x and 86x more declarations reach the
trusted gate at all** (34,112 -> 634,291 records; 13,710 -> 1,181,015), because a
stream no longer stops at its first `strVal`.

Roots: 6 -> **50** (`Init`+`Std`) and 5 -> **267** (Mathlib), with 98%+ of the
97,341 / 256,297 declines being `UnknownConst` cascades. **Every root is a
definitional-equality failure** — `TypeMismatch`, `DeclarationValueMismatch`,
`NotAPi` — and none is a missing construct. A new fourteen-stream class is an
*importer* record cap, not a verdict.

**The previous lane's headline flips.** "Not one Mathlib-specific root blocker"
was true only because strings were hiding the Mathlib: `Pi.preorder`,
`Prop.partialOrder`, `DistribLattice.ofInfSupLe._proof_4`,
`Function.Injective.*`, `Nat.inst*`, `Int.instCommRing` now sit at the top of the
Mathlib table and are absent from `Init`+`Std`'s, which is containers and
`ByteArray`. Cumulatively, fixing the top 50 `Init`+`Std` roots clears **all 242**
of its declined streams; Mathlib's top 100 clear 142 of 241.

**Next binding constraint, located.** `Nat.bitwise._unary` is the top root in both
(236/500 and 186/400 streams); its stream admits 301 of 302 records and refuses
only the declaration, with `TypeMismatch`. It is the **well-founded-recursion
unary helper** shape — `WellFounded.Nat.fix` over a `PSigma`-packed argument with
an `InvImage` relation and a dependent `PSigma.casesOn` motive — and
`Nat.Linear.Poly.denote_reverse`, `…ExprCnstr.denote_toNormPoly` and the
`Std.DTreeMap.Internal.*.eq_def` roots are the same family. No new IR construct
and no new bootstrap: this is a def-eq gap on a shape the kernel already
represents, so the work is diagnosis first and the fix is unsized until the
mismatch is exhibited as one pair of terms. Budget a session for the diagnosis.

<!-- plan-section: landed-changes -->

| 2026-08-15 | (pending) | Primitive Lean `String`-literal semantics in the trusted kernel: a checked `String`/`String.ofList`/`Char.ofNat`/`List` bootstrap, the exact Unicode-scalar expansion, Lean's projection / recursor / def-eq hooks, the `strVal` wire arm, and the writer arm with Lean's own JSON escape grammar. 11 mutation controls plus hook-removal controls, a real-Lean crosscheck generated from this kernel's reducts (floor 107 → 109, measured 117), the ADR-0366 root export reproduced byte-exactly and imported clean, and a re-census of both seeded samples. |
