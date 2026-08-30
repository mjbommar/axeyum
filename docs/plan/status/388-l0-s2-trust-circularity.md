# 388 — L0/S2: the universal trust and circularity audit

<!-- plan-section: lane-status -->

Lane: `l0-s2-trust-circularity`
Phase: ADR-0717 L0, roadmap phase **S2** — complete.
Decision: [ADR-0771](../../research/09-decisions/adr-0771-trust-and-circularity-are-read-from-the-admitted-term-and-the-identity-map-is-derived.md)

## Status

S2's exit criterion is met and gated. `scripts/check-trust-closure.py` reads the
whole constructed declaration surface out of `kernel_declaration_projection` —
one build reused for every check — and audits every kernel-route settled fact
against its own transitive `Kernel::declaration_dependencies` closure, never
against authored `depends_on`. Registered in both `scripts/check.sh` and the
justfile, together with its control suite.

**No fact was edited.** No `epistemic_status`, `proof_route`, `axiom_footprint`
or `formal.statement` was touched; `git diff main...HEAD -- artifacts/facts/` is
empty. `check-autogenesis-holdout-isolation.py` reports
`held_out=116|files_scanned=1109|settled=0|references=0|verdict=PASS`.

## Coverage

    TRUST_CLOSURE|declarations=2482|identity_classes=15|kernel_facts=2041|
      subjects=1956|unresolved=85|absent=0|disclosed_equivalent_pairs=13|failures=0

**1,956 subjects of 2,041 kernel-route settled facts (95.8%)**, against S0's
measured `circularity 38 / 2117`. The remaining 85 resolve to no kernel
declaration and are reported as unenforced rather than assumed correct; the
pinned coverage ratio stops that number growing quietly.

Subject identification adds `evidence[].kernel_declaration` between
`formal.kernel_theorem` and the regex fallback, which closes the primed-name gap
`check-fact-depends-derived.py`'s own comment predicted: that regex excludes an
apostrophe, and `F:nat-bitwise-bit`'s subject is `Nat.bitwise_bit'`, so
extraction yielded a name no declaration bears. The regex itself is imported,
not copied — it carries five measured corrections that must not drift.

## The four mutations and the four guards

| mutation | guard that rejected it | what that guard looks at |
|---|---|---|
| target injection | `guard_self_occurrence` | identity of the subject |
| indirect target injection | `guard_alias_occurrence` | the derived identity map |
| axiom insertion | `guard_forbidden_trust` | declaration KIND in the closure |
| checker-population deletion | `guard_population` | **no closure at all** |

Four different guards, and each looks at something the others do not. The fourth
exists because the other three cannot fail when there is nothing to check.

## Kill sets — 15 mutations, each killing exactly one, ZERO survivors

    baseline: 17 case(s) behaved
    TRUST_CLOSURE_CONTROLS|cases=17|mutations=15|not_exactly_one=0

    self_occurrence        KILLED target-injection
    alias_unlisted         KILLED indirect-target-injection
    alias_stale            KILLED stale-disclosure
    trust_unowned          KILLED unowned-opaque
    trust_axiom            KILLED axiom-insertion
    population_empty       KILLED population-empty
    population_floor       KILLED population-floor
    population_absent      KILLED subject-absent
    coverage_floor         KILLED coverage-floor
    identity_drift         KILLED identity-map-drift
    identity_map_missing   KILLED identity-map-missing
    scanned_nothing        KILLED scanned-nothing
    population_pin_missing KILLED pin-missing
    disclosure_missing     KILLED disclosure-missing
    empty_projection       KILLED empty-projection

Plus one more, outside this suite and verified by hand: replacing
`validate-facts.py`'s producing-run classifier with `return False` in a scratch
copy gives exit 1 naming the 1,581 rows it matched when written, not a green run.

Two things made those numbers worth having. Every case asserts an **exact
failure tag**, not merely a nonzero exit — two guards that both reject are not
the same guard. And the identity-map branch was rewritten from `if/else` into
two `if`s so each half can be deleted independently; an `else:` cannot be
mutated without taking the branch above it, which would have made one mutation
kill two cases and hidden exactly the question this phase asks.

## Findings

**No fact's closure contains its own target.** `guard_self_occurrence` rejected
0 of 1,956. That is the answer to the question the brief flagged as serious, and
it is now measured rather than assumed.

**But 30 proved facts state 15 propositions.** The environment has 15 identity
classes — theorems whose `Kernel::render_lean` types are byte-identical — and in
**all 15 both members are ledger facts**. In **13 of the 15** one member's proof
closure literally contains the other, so the second fact proved a renaming.
`F:rat-weak-law-of-large-numbers` and `F:rat-chebyshev-samplemean-uncorrelated`
are the same theorem; `F:int-characterization-le-total` is proved from
`Int.le_total`. Full table in ADR-0771.

Those pre-date this guard and no fact's status is this lane's to change, so they
are `artifacts/trust-closure/equivalent-pairs.tsv`: a **ratcheting backlog** that
rejects an unlisted pair AND a listed pair that no longer occurs, so it can only
shrink deliberately.

**No theorem in the environment reaches an axiom.** The only declarations with a
nonzero footprint are the 30 `AxReal.*` axioms themselves; zero `Opaque`s, zero
`Quotient`s. `guard_forbidden_trust` is therefore a tripwire rather than a
finding — its scan is real (1,956 subjects) and both branches are
fixture-verified, but it has never rejected real data.

## The self-re-derivation count, settled

`validate-facts.py` printed `3579 evidence row(s) re-derived by 2+ independent
checkers`. **1,581 of those 3,579 rows name the producing run** — 1,333
`producing-build (Kernel::add_declaration)` plus 248 naming
`Kernel::add_declaration` in another phrasing or a `*-producing-solve`. For a
kernel-route fact the proof term is built and admitted in one step, so
`add_declaration` IS the production. **2,097 rows carry 2+ checks that are not
the production.**

Both the count and the wording changed; the line now reads

    3579 evidence row(s) checked by 2+ distinct checkers -- 1581 of those count
    the PRODUCING run as one of the two, so 2097 carry 2+ checks that are not
    the production itself

S0's `1,356 of 1,984 facts` reproduces exactly under its own method (the literal
string `producing`) as **1,359 of 1,989** today, the drift being three facts
landed since. That measurement was right about what it measured; this classifier
is broader because a checker named `Kernel::add_declaration (re-derives the type
from the proof term)` is the producing build whether or not it says "producing".

**ADR-0746 quotes the old line verbatim and is now stale in that one respect.**
It belongs to the S0 lane and was not edited here; the correction is in ADR-0771.

## Handoff — what I did NOT do, and what is a hypothesis

Per the standing rule that a handoff's "blocked on X" is a claim about one route
and is reliably pessimistic: everything below is what this route did not reach,
not a claim that it is hard.

- **85 kernel-route settled facts resolve to no kernel declaration** and sit
  outside every guard here. Down from `check-fact-depends-derived.py`'s 169, but
  a real hole. It cannot grow silently (the coverage ratio is pinned) and it can
  shrink further: several of the 85 likely have an `evidence[].kernel_declaration`
  that could be filled in, which is a fact-owner's edit rather than a tool
  change. I did not sample them, so the shape of the 85 is a hypothesis.
- **The 13 duplicates are disclosed, not resolved.** Each needs its fact owner
  to decide which member keeps the proposition. Resolving one requires a
  `--update` so the ratchet records the progress.
- **The identity map's exact compare will go red** when a lane lands a theorem
  whose canonical type duplicates an existing one. That is the intended review
  signal, not churn — but it means the gate can redden from another lane's work,
  and whoever hits it should confirm the pair really does state one proposition
  before re-running `--update`.
- **I did not run the full `just check` or `scripts/check-fast.sh`.** I ran the
  two steps I registered, `validate-facts.py`, `gen-adr-index.py --check`,
  `gen-plan.py`, the holdout isolation check and `check-merge-hygiene.sh`. Any
  interaction with a step I did not run is unmeasured.
- **Nothing here checks a fact's `formal.statement` against its subject's
  rendered type** (S1's question), and the closure is over declaration
  references rather than over a Lean export (S4's question).

## Paths owned by this lane

`scripts/check-trust-closure.py`, `scripts/tests/test-trust-closure.sh`,
`artifacts/trust-closure/`, `docs/research/09-decisions/adr-0771-*.md`, this
file. Registration lines only in `scripts/check.sh` and `justfile`. One
surgical change in `scripts/validate-facts.py` (the multi-checker counter and
its print), which no other lane holds.
