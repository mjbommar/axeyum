# Theorem correspondences

One file per adjudicated claim that **two settled facts are the same
mathematical content**. Schema: [`../ontology/theorem-correspondence.schema.json`](../ontology/theorem-correspondence.schema.json).
Gate: `python3 scripts/validate-correspondences.py` (`just correspondences`).
Rationale and rejected alternatives: [ADR-0546](../../docs/research/09-decisions/adr-0546-theorem-correspondences-are-not-proof-dependencies.md).

## This is not `depends_on`, and the gate enforces that

`depends_on` in the fact ledger says **one proof used the other**. A
correspondence says **the two statements are the same idea**, whether or not
either proof ever mentions the other.

The motivating case is the one the two relations cannot share. Cassini's
identity, `fib(n+2)·fib(n) − fib(n+1)² = (−1)^(n+1)`, and the multiplicativity
of a 2×2 determinant, `det(AB) = det A · det B`, are one theorem: with
`M = [[1,1],[1,0]]`, `Mⁿ` has entries `[[fib(n+1), fib(n)], [fib(n), fib(n−1)]]`
and `det M = −1`, so `det(Mⁿ) = (−1)ⁿ` **is** Cassini. No `depends_on` edge will
ever connect them, because the kernel proof of Cassini is an induction that
never mentions a determinant.

So the two relations are mutually exclusive by construction: the validator
**refuses** any correspondence whose endpoints the fact ledger already connects,
directly or transitively, in either direction, and says `depends_on` in the
message. `F:ml430-nat-fib-add-two` / `F:ml430-int-fib-add-two` looks exactly like
a carrier transport and is a proof dependency; that refusal is pinned in
`scripts/tests/test_validate_correspondences.py` against the committed ledger,
not against a fixture.

## The three kinds

| kind | what it asserts | what the gate CAN check |
|---|---|---|
| `carrier-transport` | the same law over two carriers | **structurally**: erase the carrier from both formal statements and the strings must be equal |
| `independent-formalization` | the same classical theorem reached by two different machines | the two facts must be on **different `proof_route`s** |
| `specialization` | endpoints[0] is endpoints[1] under a stated substitution | `via` must be non-empty and every non-null ref must resolve |

`carrier-transport` is the one with real teeth. `∀ {n : ℕ}, Nat.fib n = 0 ↔ n = 0`
and `∀ {n : ℤ}, Int.fib n = 0 ↔ n = 0` both erase to
`∀ {n : ⟨C⟩}, ⟨C⟩.fib n = 0 ↔ n = 0`; an unrelated pair does not, and is
rejected. A fragment with no entry in the validator's `CARRIERS` map **fails**
rather than skipping the check — an unmeasured claim is not a passing one.

`independent-formalization` has no structural check available, because its two
endpoints are in different languages by definition, and the validator does not
pretend otherwise.

## The two status axes

Deliberately the fact ledger's two axes, applied to the edge instead of to a
proposition — and each one is required to be **backed by what is in the
document**, never by tone.

`derivation_status` — what **we** established about the correspondence:

| value | required |
|---|---|
| `asserted` | `via` is empty. Exactly; the gate checks both directions. |
| `route-recorded` | `via` is non-empty and every non-null `ref` resolves to a fact or to a declaration the kernel projection has actually observed. |
| `mechanized-here` | additionally: no `ref` is `null`, and `evidence` carries a checker command whose exit status depends on what it found. |

Evidence at all requires `mechanized-here`, mirroring the ledger's rule that an
`open` fact must carry an **empty** evidence array.

`external_status` — what **mathematics** knows: `classical`, `folklore`,
`novel-here`, `unclassified`. `novel-here` requires `mechanized-here`: claiming
the connection is new while nothing here derives it is the one combination that
is pure tone.

A `null` `ref` in `via` is a **named gap**, and naming it is the point. All five
`via` steps in the three committed correspondences that are `null` mark a
transport step no fact in this repository states.

## Writing one

1. Pick two **settled** facts (`proved` or `computed`) that the ledger does
   **not** connect by `depends_on`.
2. `id` is `X:<slug>` and the filename is `X-<slug>.json`. One adjudication per
   endpoint pair.
3. `claim` says *what* is shared (≥120 chars); `transport` says *how* the two are
   identified (≥60 chars) — the specific map, cast or substitution, not the fact
   that one exists. They may not be the same text.

   Those floors come from measured practice next door, not from a round number:
   `../math-education`'s 1,263 `bridges_to` reasons run 75–328 characters with a
   median of 190, and its SHACL floor of 10 never fired once.
4. Write the route in `via`, with a `null` `ref` for every step this repository
   does not have. Set `derivation_status` to whatever that leaves you.
5. `python3 scripts/validate-correspondences.py`.

## What a prose reason buys, measured

Next door, 100% of `bridges_to` edges carry a reason and `volume.md` still
shipped a bridge to `C:pi` whose reason text was entirely about density. It
validated cleanly because both fields were well-formed. That is why every rule
here is about something a machine recomputes, and why `claim` and `transport`
are the *least* load-bearing fields in the file.
