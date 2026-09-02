# Lane: testbit-codomain — decide the `Nat.testBit` codomain question

<!-- plan-section: lane-status -->

**testbit-codomain (`DONE`, testbit-codomain, 2026-09-02).** The
`shape-census` lane ranked this the single highest-leverage item on the ready
frontier: six `ml430` mirrors blocked, one construction decision, no producer
able to take it. Decided in
[ADR-1545](../../research/09-decisions/adr-1545-the-testbit-codomain-is-the-outermost-link-of-a-chain-and-the-bool-view-is-already-built.md)
as **option (c), leave all six blocked** — because the premise underneath the
recommendation does not hold.

**Option (a) is already built, and it flipped nothing.** A `Bool`-valued
`testBit` beside the `Nat`-valued one, with the agreement bridge, exists as
`Axeyum.Autogenesis.testBitBool n i := bitToBool (Nat.testBit n i)` in
`examples/nat_testbit_bool_bridge.rs` — run in this lane, every theorem
reporting `axioms=0`, exported as a committed capsule and gated from the
justfile since 2026-08-26. Six mirrors, zero moved. `docs/autogenesis/279`
says why in its own words: "the result-sort adaptation itself is available;
equivalence with the exact imported `Nat.testBit` definition remains
missing."

**The codomain is the outermost link of a chain.** Read at the pinned commit
`c5ea0035…`: Lean core's `testBit m n := 1 &&& (m >>> n) != 0` is a
shift-and-mask closed form over `Nat.shiftRight` (**absent from this
kernel**) and `Nat.land`; doc 279 already measured that imported closure as
carrying `propext`. Three of the six additionally name `Nat.land`/`lor`/
`ldiff`, which Mathlib specializes from the **well-founded** `Nat.bitwise`
and this kernel builds as three independent hand-rolled fuel recursions
(`land.rs`'s own module doc records the divergence and the axiom-freedom
reason for it). A fourth needs `List Bool` and `Inhabited`, neither of which
exists here. Per ADR-0840 a flip needs the whole chain.

**Option (b) costed:** 23 declarations, measured twice by independent routes
(`shape_search` type + value indexes; `kernel_declaration_projection` over
15,005 rows) that agree on the *set*, not merely the count. Three of them —
`testBit_le_one`, `sum_testBit_eq`, `sum_testBit_lt` — do arithmetic on the
result and have no `Bool`-typed restatement at all. Zero flips bought.

**Nothing moved that should not have.** No fact file edited; all six are
`partition: development`, family `natural-bitwise`, whose 19 members are all
`development` — **no held-out row is in scope**. `brief-step0.py` on all six
before and after: `DIVERGENCE-BLOCKED`, unchanged, which is the decision.
`validate-facts.py` exit 0; `check-mirror-statement-fidelity.py` PASS
(`violations=0`).

**Landed as a checker, not as prose.** The wrong claim lived in
`gen-obstruction-producers.py`'s `nat-testbit-bool-codomain` row —
`removability: new-construction`, reason "neither is built" — in the field a
selector reads, written directly beneath that same file's record of the
identical mistake about `fastFib`. Corrected to `not-removable` and pinned by
`scripts/tests/test_gen_obstruction_producers.py` (5 tests, one of them a
vacuity control), registered in `mutation_controls.py` as
`obstruction-testbit-classification`: **4 mutations, each `killed 1`,
different test each time.** Wired into `just check` and `check.sh`.

**Three gates are red on `main`, none of them caused here** (each re-run from
a pristine `lane-snapshot.sh main` extraction, identical output):
`gen-obstruction-producers.py --check` / `check-obstruction-producers.py`
(exit 2, `P2 target F:ml430-nat-and-or-distrib-left-fe131f64 is missing or
not open` — both its targets were flipped to `proved` in `845fc8823`, so the
producer hypothesis is spent); `check-settled-fact-statements.py` (10 settled
facts unpinned); `check-dispatchable-frontier.py` (`G7 queue-below-floor`, 2
dispatchable against a floor of 10). The first is why
`artifacts/obstruction-producers/obstructions.json` is **not** regenerated
here — the generator dies before it writes. The corrected classification was
verified by calling `build_obstructions_doc()` directly and lands on the
first successful regeneration after that producer is re-pointed or retired.

**Named next action, measured but deliberately not taken.**
`Nat.land`/`Nat.lor`/`Nat.ldiff` diverge from Mathlib by the same standard
the registry applies to `Nat.minFac`, and none has a registry row.
`gen-obstruction-producers.py`'s docstring leans on that absence as the
precondition licensing the `extensional-duplicate-close` producer, which
claims three targets today. Adding the rows retires that producer's whole
population — a producer-policy decision with its own blast radius, not a
corollary of the codomain question. ADR-1545 §"What this ADR does NOT claim"
carries the measurement for whoever takes it.

<!-- plan-section: landed-changes -->

| 2026-09-02 | `7a029fab1` | ADR-1545 decides the `Nat.testBit` codomain question as (c); `gen-obstruction-producers.py`'s `nat-testbit-bool-codomain` row corrected `new-construction` → `not-removable` with the measured chain and five existing-file evidence citations; the divergence registry's `Nat.testBit` `why` records the whole chain; `test_gen_obstruction_producers.py` (5 tests) + 4 mutation anchors, each killing exactly one test; gated in `justfile` and `check.sh`. |
