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

Detail moved to [`../notes/388-l0-s2-trust-circularity.md`](../notes/388-l0-s2-trust-circularity.md).

