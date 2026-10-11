# Lane: cas-negative-powers — exact signed powers and domain preservation

<!-- plan-section: lane-status -->

**Signed CAS powers (`WIP`, cas-negative-powers, 2026-10-10).** Based on
97359c332's bounded wide Python surface. ADR-3000 proposes signed Rust/Python
powers lowering to partial Div/Pow nodes with explicit limits and zero/missing
behavior. Four Rust tests pass; revised fresh extension passes 223 Python tests,
including seeded Fraction comparisons and degenerate inputs. Focused clippy,
645-item stub generation and diff checks pass. Private domain-guard mutation:
four baseline passes, three mutant passes/exactly one failure. Parent CAS gate
has one timing failure; workspace jobs remain live. Next: domain-aware trace
certificates, kernel admission and integration gates. No completion claim.
[Evidence](../notes/cas-negative-powers.md).
