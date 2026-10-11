# Typed Date facade evidence — 2026-10-11

CON-7 starts from a7df59e83 in its own worktree. ADR-3200 records the proposed
lowering contract; native Date IR is not claimed. Context keeps Date and Duration
source sorts, adds range obligations to all constructed Date terms, rejects
cross-context comparisons and duplicate declaration names. Date arithmetic uses
signed integral day durations; no month/year convention is invented. Model
lifting requires SAT and replay of the complete supplied source query, then
converts present Date values; missing values remain absent.

Eight public Python tests pass (eight collected, 0.12 seconds). They cover
lifted leap-day models, discriminating date-difference assertions, century leap
rules, year boundaries, invalid Date arithmetic bounds, malformed/mixed/context
inputs and rejection of a changed source query at lifting. Package:
`/var/tmp/axeyum-rules-date-python-soke0thm`. It contains the new pure Python
source and the previously built native extension SHA-256
`e0fc5d60da33153038bc552ba51709ecc309959638d9e828ed478ab157d1b48b`;
this is explicitly reused native code, not a fresh build of the Date branch.
The facade changes no Rust code. Full integration/native gates remain required.

Example:

```python
from datetime import date
from axeyum.rules import Context
ctx = Context()
start = ctx.date_var("start")
end = ctx.date_var("end")
assertions = [start == ctx.date(date(2024, 2, 28)),
              end == start + ctx.days(2)]
result = ctx.solve(assertions)
if result.is_sat():
    print(ctx.lift_model(result, assertions))
```

Next: existing temporal pack loading/typed input binding and obligations,
source-linked results and a bounded sourced Minnesota statute template.
No native Date sort, statute coverage or complete CON-7 claim is made yet.

## Existing pack reuse

ADR-3300 proposes bounded local pack loading, sorted native obligation outcomes
and typed benefit evaluation. All seven authoritative metadata paths are loaded
by a population-derived test (with positive count seven). The benefit evaluator
builds the existing predicate from metadata inputs/fixture parameters using native
Bool/Int terms and Date ordinals. Every fixture witness agrees with its expected
eligibility after complete query SAT replay; source citations accompany outcomes.
Missing facts return missing-inputs, malformed/extra facts reject, and complete
facts outside the half-open effective interval yield no rule output. No SMT
fixtures rejects rather than counting an empty check set as evidence.

Thirteen combined Python tests pass (13 collected, 0.10 seconds) against the
same isolated package/native identity as above. The four existing benefit SMT
obligations return native UNSAT outcomes; no external/kernel proof-check claim
is inferred from those verdicts. Other six typed evaluators explicitly decline
with NotImplementedError while their metadata and fixture checking remain
available. Full schema validator integration and statute-backed template remain
open. This increment does not close CON-7.

## Tax-benefit and procurement lowering

Typed evaluation now also lowers the existing tax-benefit arithmetic and
procurement models, including Date cutoffs, caps, phaseout, business bonus and
specified household/quality domains. Model outputs are returned only after
native SAT replay; domain-inconsistent input yields native UNSAT and no outputs.
Ordinal dates deliberately differ from the old YYYYMMDD fixture representation
while preserving its calendar ordering. ADR-3300 records the added model scope.

18 combined Python tests pass (18 collected, 0.35 seconds) with the previously
recorded isolated extension identity. All tax/procurement explicit witnesses
agree, plus the complete generated bounded populations derived from the checked-in
query files: 66 benefit rows and 144 award rows, each with native replay.
Generated row counts are checked against both the authority and positive controls;
these finite populations establish no general legal applicability claim.
Authorization, category equivalence, grant allocation and workflow typed
evaluators remain open, as do the statute template and full integration gates.

## Finite enum and exact rational pack evaluation

All seven existing packs now have typed evaluators. Authorization, category and
workflow use explicit admitted-label Int maps; workflow outputs check and lift
back to labels. Grant allocation uses exact Fraction Real terms with the current
explicit 127-bit component limit. Floats and unknown enum labels reject. Packs
without a Date input require an explicit as_of date rather than choosing a clock
value or silently assuming applicability. Source intervals still decline dates
outside the declared half-open range. Category handles its one shipped pair and
explicitly declines a changed equivalence-pair family.

24 combined Python tests pass (24 collected, 1.31 seconds) against the same
isolated native identity documented above. Added complete generated populations:
authorization 96, category 6, grant 125, workflow 24 (251 rows), each returned
outputs only after native model replay. Negative controls cover absent as_of,
pre-effective dates, invalid enum labels, float/wide Real inputs and tampered
negative workflow model ordinals. No general theorem or external proof claim
follows from finite samples.

Private snapshot `/data0/axeyum/scratch/snap-rules-enum-mutation-f966949b7`
received only the owned Python implementation/test files. Removing the enum
ordinal guard from its private package caused exactly the one targeted tampered
model test to fail (baseline one pass, mutant one fail). Logs:
`/var/tmp/axeyum-rules-enum-mutation-iuoys982`. Shared source was not mutated.
Next: complete pack validation, obligation-proof distinction and the sourced
statute template; integration/native/workspace gates remain open.

## Sourced day-period template

ADR-3400 proposes a bounded positive-day interpretation of Minnesota §645.15,
with explicit §§645.13/645.14 exclusions and caller-established applicability.
The official 2025 section identities for §§645.15, 645.13, 645.14 and 645.44
are fetched/pinned in the template manifest; retrieval date is 2026-10-11 and
historical effective interval remains not-established. The source/crosswalk
explain the interpretation and branch-specific holiday limitations. Calendar
facts are sourced input, assumed complete only inside an inclusive window;
examples use synthetic calendars, not claimed legal holiday authority.

31 combined Python tests pass (31 collected, 0.69 seconds), with the same
isolated native identity as above. Seven added deadline tests include weekend,
holiday, leap/year boundaries, missing/excluded applicability, malformed input,
calendar coverage and representation/budget declines. A separate ordinal-based
reference agrees over 124 stated cases. The executable synthetic example exits
zero and produces July 6 after a nominal Saturday July 4. Declines carry no
final deadline. No checker/proof-certified result is claimed for this producer.

Template: docs/rules-as-code/statute-templates/minnesota-64515-v0. Its manifest
sits outside the old example schema because that schema requires a known from
date; no historical date was fabricated. Next: native feasible/minimal/unique
endpoint obligations, proof routes, independent source/calendar validation,
validator/dashboard integration and full branch integration gates. CON-7 and
the overall goal remain open.

## Native deadline obligations

verify_minnesota_deadline reconstructs feasibility, minimality and uniqueness
without invoking the producer. Native ground ordinal modulo seven supplies
weekday predicates; calendar/applicability remain input assumptions. It requires
coverage over the whole bounded obligation window and records serialized subjects,
verdicts, evidence and three-valued check statuses. Wrong decided verdicts or
failed replay reject; unknown/coverage gaps remain inconclusive. checked-native
requires checked evidence and certified reductions for all obligations.

34 combined Python tests pass (34 collected; 3.50 seconds before the additional
certified-reduction classification guard, repeated after it). All 124 reference
cases have SAT/UNSAT/UNSAT obligation verdicts and verified feasible models.
Current UNSAT evidence is unsat-uncertified with nothing-to-check; reports are
validated, never proof-certified. The executable example displays that distinction.

Private snapshot snap-deadline-obligation-mutation-d83a5a016 received owned
Python files. Removing verdict/expectation rejection causes exactly one target
test to fail: baseline one pass, mutant one fail, accepting a wrong deadline.
Logs: /var/tmp/axeyum-deadline-obligation-mutation-u6kxiimm. No shared mutation.
Remaining: checked UNSAT proof routes, source/calendar validation, validator/
dashboard and native/workspace/full integration gates.

## Finite-window certificate

ADR-3500 specifies versioned bounded JSON carrying the complete conditional
subject and every candidate observation. Producer uses datetime weekday;
checker uses native ground ordinal modulo arithmetic and does not call the
producer. It verifies authoritative population/order, each witness, rejects
admitted predecessors and requires an admitted claimed endpoint. Optional
expected_subject binds an external query with JSON type distinctions preserved.
Shared calendar validation/encoding means no implementation-independence claim.
No source authenticity, legal applicability or kernel admission is implied.

35 combined Python tests pass (35 collected, 5.47 seconds), including malformed,
future-version, byte-limit, duplicate-field, Unicode, source/context, boolean vs
integer and witness/claim tampering controls. Exported synthetic fixture replays
in a separate Python process with checked status and eight checked candidates.
Private snapshot snap-deadline-certificate-mutation-33c7366ab received owned files;
removing the least-endpoint guard makes exactly the one targeted test fail
(baseline one pass, mutant one fail). Logs:
/var/tmp/axeyum-deadline-certificate-mutation-ww4xph4p.
Native minimality/uniqueness UNSAT evidence stays separately uncertified; finite
certificate checking is a narrower explicit route, not replacement of the full
proof/integration requirements. All previously observed workspace runners remain
live and advancing through kernel tests; none was restarted or credited green.
