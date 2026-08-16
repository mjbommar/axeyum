# Lane: agent-i — CAS bridge

<!-- plan-section: lane-status -->

**CAS bridge lane (`DONE`, agent-i, 2026-08-13).** `cas-ideal-refuter`
(ADR-0429, `119858e2c` + `04249ded3`) emits cofactor-tracked ideal identities
that a CAS-free checker re-derives. Six non-polynomial-atom query classes moved
from `unknown` to certified `unsat`; route ordering avoids the measured fast-path
regression. Guard-isolating satisfiable-query forgeries replaced ineffective
tamper cases. **Next:** exact-rational LP over candidate residues instead of
unit-coefficient subset search; see `agent-i-cas-bridge/FEEDBACK.md` F8.
