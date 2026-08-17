# 01 — What we decide but cannot certify

**The gap, as first written.** 101 capability entries across 26 areas. **Four**
name a kernel/Lean-checked proof in their evidence field: `QF_LIA`, `QF_LRA`,
`QF_NRA`, `quantifiers`. The other 22 areas return verdicts backed by our own
machinery and nothing an independent kernel has seen.

> **RE-MEASURED 2026-08-17 — the gap is 12 areas, not 22.**
> `scripts/check-capability-assurance.py` derives the count instead of reading
> it:
>
> ```
> CAPABILITY_ASSURANCE|entries=101|areas=23|external=36|self=48|differential=2|unclassified=15
> areas with >=1 externally-checked capability: 11 of 23
>   QF_ABV, QF_BV, QF_LIA, QF_LRA, QF_NRA, QF_UF, QF_UFLIA, QF_UFLRA,
>   datatypes, quantifiers, reachability
> ```
>
> The four named above are all real. **Seven more had joined them** — mostly via
> **Carcara**, the external Alethe checker, whose acceptances the entries record
> as `accepted (valid && !holey)`. Nobody noticed, because counting meant reading
> 101 prose `evidence` fields, which is precisely the complaint item A makes
> below.
>
> Two cautions carried into the script rather than left here. **Agreement with an
> oracle is not an external check** — "differential vs Z3" tests the verdict, not
> our artifact — so it gets its own tier and cannot inflate this number. And the
> classifier is a HEURISTIC over prose: 15 entries are `unclassified` and are
> reported as such rather than sorted into whichever tier flatters the count.
>
> `areas` counts LOGICS, not `area` strings. Some entries legitimately span two
> (`"QF_ABV / QF_AUFBV"`, `"QF_UFLIA/UFLRA"`), so counting the strings hides a
> logic reachable only through a compound entry, while rewriting them to one
> name would delete the fact that the capability covers both. The string is left
> alone and the count is normalised — including the abbreviated prefix, since
> `QF_UFLIA/UFLRA` names `QF_UFLRA` and not a logic called `UFLRA`.
>
> **11 of 23 logics** have at least one externally-checked capability. The 12
> without are the actual queue: `QF_AUFBV`, `QF_FP`, `QF_IDL`, `QF_NIA`,
> `QF_RDL`, `QF_S`, `SAT`, `diagnostics`, `incremental`, `optimization`,
> `symbolic execution`, `synthesis`.
>
> The floor is now gated: the externally-checked count may not fall silently.

That is not a criticism of the verdicts. `Assurance::Checked` (49 entries) and
`Assurance::Validated` (40) are real: replayed models, DRAT certificates
re-derived by our own backward checker, differential validation against Z3 with
zero disagreement on the fuzzes that ran. **The distinction this document draws
is narrower and sharper: who has to trust us.**

## The three tiers, and why the third one is the product

| tier | what a sceptic must accept | where we are |
|---|---|---|
| **verdict** | that axeyum is correct | 101 capabilities |
| **self-certified** | that axeyum's *checker* is correct | broad on SAT/BV: DRAT + independent backward checker, instance regeneration, cover obligations discharged mechanically |
| **independently certified** | nothing — they run their own kernel | 4 areas; 19 certificates accepted by official Lean v4.30.0 from an empty environment |

The third tier is the one nobody else in this problem space has at scale, and
it is the one the project's identity sentence is about: *untrusted fast search,
trusted small checking*. A verdict is a claim. A self-checked certificate is a
much better claim. **A certificate a stranger's kernel accepts is not a claim at
all — it is a proof.**

## The flagship gap: CAD decides, CAD does not certify

`capabilities.rs:705-719`, `QF_NRA`:

> a complete cylindrical-decomposition decision side ... **ANY dimension**,
> rational OR algebraic coordinates ... differentially VALIDATED DISAGREE=0 vs
> Z3 over the NRA fuzz (which found+fixed real wrong-unsats); **degree-2 SOS
> UNSAT carries a kernel-checked Lean proof, general CAD UNSAT no proof yet**

So for nonlinear real arithmetic we have two paths:

- **SOS/PSD** — narrow (capped at `MAX_CROSS_PRODUCTS = 2`, i.e. the
  two-variable frontier `a²+b² < 2ab`), and it **certifies** into Lean.
- **CAD** — any dimension, algebraic coordinates, validated against Z3, and it
  **does not certify at all**.

`MAX_CROSS_PRODUCTS = 2` therefore is not a tuning parameter and not a missing
engine. **It is the width of the certifying path.** Every nonlinear problem
between "two cross-products" and "what CAD can decide" gets a correct answer
that no independent party can check.

That also corrects how the engineering strand framed the `k=3` blocker: integer
bound strictness normalisation closes one measured leaf, but the general
nonlinear case is a *proof-production* problem, not a rewrite-pass problem.

**Certifying CAD is a genuinely hard research problem**, not an oversight.
Proof-producing CAD is an open area. The honest options, in increasing
ambition:

1. **Widen the certifying path.** Push SOS/Positivstellensatz beyond two
   cross-products with exact rational arithmetic. Certificates are polynomial
   identities — already re-checkable, and the CAS gained exactly this machinery
   in `cas-ideal-refuter`.
2. **Certify CAD's *witnesses*, not its refutations.** SAT results are already
   replay-checked via `sign_at` and exact field arithmetic; a witness is
   cheaply certifiable even where a refutation is not.
3. **Emit a checkable trace for restricted CAD fragments** — sign-determination
   over a single variable, or resultant-grid cases — and declare the rest
   decided-but-uncertified, explicitly, in the evidence field.

Option 3 is the honest near-term move and it is mostly *labelling*: make
"decided but not certified" a first-class evidence status rather than a phrase
in a string.

## The other 21 areas

`QF_BV`, `SAT (propositional)`, `QF_UF`, `QF_ABV`, `QF_FP`, `QF_S (strings)`,
`datatypes`, `optimization`, `incremental`, and the rest carry no kernel-proof
mention.

**Two caveats, stated because this measurement is a document, not a run.**
First, the evidence strings may lag the code: propositional resolution
reconstruction was extended on 2026-08-14 to **4,572,930 LRAT hints** with 19
certificates accepted by official Lean, and that has not necessarily reached
every capability entry. Second, "no Lean proof" does not mean "no evidence" —
the SAT/BV path has DRAT certificates our own checker re-derives, which is tier
two and is genuinely strong.

So the actionable form of this section is not "add Lean proofs to 21 areas". It
is:

**A. Re-derive the capability table from the code rather than maintaining it by
hand.** A 1,858-line hand-written table of what the system can do is the same
category of artifact as a guard that exists only in a comment. It should be
generated, or at minimum gated against the routes it describes.

**B. Rank the 21 by how much a certificate would be worth.** They are not
equal. `QF_UF` and `datatypes` have small, well-understood proof formats.
`QF_FP` and strings do not. Ranking honestly beats attempting uniformly.

**C. Make "decided, not certified" an explicit status**, so the gap is visible
in the artifact instead of discoverable only by reading a prose evidence field.

## The measurement to repeat

For each area: does a verdict come with an artifact a third party can check
without trusting us? Today that answer is *yes* for four areas and *partly* —
via DRAT — for the SAT/BV family. Everything else is a verdict.

Moving that count is the strand's primary metric, and it is a better one than
any benchmark because it is the thing the architecture was built to make
possible.
