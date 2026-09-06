# Lane: cas-frontier — advancing the ten items of docs/math-department/13-computer-algebra.md in waves

<!-- plan-section: lane-status -->

**CAS frontier (`WIP`, cas-frontier / coordinator axeyum-15, 2026-09-06).** The plan is `docs/math-department/13-computer-algebra.md`: ten items, each advanced by lanes in waves, the file's checklist and progress log updated at every merge. On 2026-09-06 twelve lanes landed (see rows): items 1, 3, 5, 6, 9 and 10 each moved a wave, `axeyum-arith` (ADR-1710) reached its designed surface with `axeyum-ir` and `axeyum-fp` off the raw bignum crates, and three checkers that can fail were added (parity-ledger drift, the arith dependency boundary, the fallback entry gate). Trust registry floor 151; parity corpus 138 entries, 0 disagreements. Next: the CAS and kernel import rewrite behind `scripts/arith-boundary-allowlist.txt` (one compiling commit per crate); an exp-tower path for the zero-test (the generic fallback costs 217x, measured); Burnside-Dixon for nonabelian character tables; algebraic-logarithmic singularities for item 3; Pascal on an arbitrary conic. Blocked on nothing; the kernel numeral bridge waits on the user's word.

<!-- plan-section: landed-changes -->

| 2026-09-06 | `6cdcda3c7` | Lane arith-finish: Normalize, HenselLift and AlgebraicNumber implemented in axeyum-arith; axeyum-ir and axeyum-fp no longer name num-bigint or num-rational; a boundary gate with an allowlist (ADR-1710, file 13 item 1) |
| 2026-09-06 | `be1ca0a4c` | Lane cas-fps-4: the exact asymptotic amplitude of a rational generating function (file 13 item 3, wave four) |
| 2026-09-06 | `ae6d38279` | Lane cas-bigfallback-1: the zero-test's fallback entry distinguishes overflow from out-of-fragment; exp measured and kept out (file 13 item 1, wave five) |
| 2026-09-06 | `5a7355b2a` | Lane cas-matgroup-2: finiteness and order of matrix groups over Q, and a character-table checker (file 13 item 5, wave five) |
| 2026-09-06 | `e176b2f06` | Lane cas-geometry-4: Pascal on the parabola and affine Desargues certify (file 13 item 6, wave four) |
| 2026-09-06 | `06e18899c` | Lane cas-corpus-counts: a checker that fails when the parity corpus's three ledgers drift (file 13 item 10) |
| 2026-09-06 | `7278d6404` | Lane cas-witness-3: transcendental atoms key on a canonical rational form; three wrong refutations fixed (file 13 item 1, wave four) |
| 2026-09-06 | `750bde174` | Lane arith-slice-2: enclosure rounding moves onto Dyadic; sqrt and ln round their arguments outward (ADR-1710, file 13 items 1 and 4) |
| 2026-09-06 | `35e4aff98` | Lane arith-slice-3: ZPoly/QPoly, the fraction-free layer and one Sturm chain in axeyum-arith; four of five CAS copies migrated (ADR-1710, file 13 item 1) |
| 2026-09-06 | `de37ceb08` | Lane cas-sum-gaps-2: Geometric with symbolic p and Normal with symbolic variance certify under hypotheses (file 13 item 9, wave four) |
| 2026-09-06 | `ffb32f715` | Lane cas-witness-2: constant radicals of every root index canonicalize together; exp measured and not shipped; the degree wall corrected (file 13 item 1, wave three) |
| 2026-09-06 | `3cc85756e` | Lane homology-guards: the eleven cup-product and relative-homology guards each kill exactly one test |
| 2026-09-06 | `5685a328a` | Lane cas-matgroup: finite matrix groups over F_p through certified permutation actions (file 13 item 5, wave four) |
| 2026-09-06 | `a1c5c7c76` | Lane cas-homology-4: relative homology with the long exact sequence, and the cup product (file 13 item 8, wave four) |
| 2026-09-06 | `e9f47afc5` | Lane cas-enclosure-3: the integral-defined heads, symbolic exponents, certified quadrature (file 13 item 2, wave three) |
| 2026-09-06 | `8fa1b9340` | Lane arith-slice-1: workspace dependencies hoisted; ModularRing and PowModCertificate; two pow_mod copies migrated (ADR-1710 slices 0 and 2) |
| 2026-09-06 | `0db8a5b03` | Lane cas-permgroup-3: isomorphism testing and presentations (file 13 item 5, wave three) |
| 2026-09-06 | `ec716a889` | Lane cas-elim-combine: a power of a stated condition is what gets inverted; the medians certify in a second (file 13 item 6, wave three) |
| 2026-09-06 | `6c864e9f6` | Lane cas-numberfield-4: real quadratic class numbers by form cycles, and the regulator as an enclosure (file 13 item 4, wave four) |
| 2026-09-06 | `ab7a5a088` | Lane cas-qe-4: three variables with one existential, and the first quantifier alternation (file 13 item 7, wave four) |

