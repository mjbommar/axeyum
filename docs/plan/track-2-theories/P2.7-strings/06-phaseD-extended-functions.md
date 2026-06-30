# P2.7 · Phase D — Extended functions (lazy reduction + context-dependent simplification)

**Size:** L · **Depends on:** Phase B (core), Phase C (regex for `replace_re`) ·
**Brings full `str.*` coverage.**

> The core theory is a minimal kernel (`++`, `len`, `in_re`); everything else
> (`substr`, `indexof`, `replace`, `replace_re`, `contains`, `prefixof`/`suffixof`,
> `to_int`/`from_int`/`to_code`) is **reduced into the kernel** — but **lazily**,
> and simplified **in context** so the expensive reductions usually never fire.

## The two ideas that make it scale

1. **Lazy reduction** (cvc5 `StringsPreprocess::reduce`): a function `f(t₁,…)` is
   replaced by a fresh `k` plus a *semantic-expansion* lemma `F[k] ∧ f(t)=k`, but
   only when needed (by effort level), not eagerly. `¬contains(x,y)` in particular
   reduces to a **bounded universal over positions** — expensive — so we delay it.
2. **Context-dependent simplification** (Reynolds et al., CAV 2017): when a variable
   is *partially concrete* in the current context, simplify the extended function
   in place (e.g. `contains(x++y,"a")` with `x=""` → `contains(y,"a")`), often
   discharging it **without** the full reduction. Plus **high-level abstractions**
   (CAV 2019): arithmetic-entailment, multiset, and containment over/under-
   approximations as cheap filters.

## Per-function reduction (the kernel expansions)

| Function | Reduction sketch |
|---|---|
| `substr(s,i,n)` | skolems `k_pre,k,k_suf`: `s=k_pre++k++k_suf ∧ len(k_pre)=i ∧ len(k)=n` (with boundary cases) |
| `indexof(s,t,i)` | case split: found at `j≥i` (with a "no earlier occurrence" constraint) vs −1 |
| `contains(s,t)` | `s = pre ++ t ++ post`; negation → bounded-universal (lazy!) |
| `replace(s,t,r)` | first occurrence: `s=pre++t++post` ⇒ `pre++r++post`, or `s` if absent |
| `replace_all/_re(s,t,r)` | recursive first-occurrence to fixpoint; `_re` uses the Phase-C regex |
| `prefixof/suffixof` | `s = t ++ x` / `t = x ++ s` |
| `to_int/from_int` | digit-sequence constraints — **dedicated code-point reasoning**, not word equations |
| `to_code/from_code` | length-1 ⇒ code point else −1; injectivity `to_code(x)=to_code(y) ⇒ x=y` |

## Effort-based firing (cvc5 strategy order)

- Effort 0: reductions on constants only.
- Effort 1: reductions on normal forms (after the core's normal-form pass).
- Last-call: reductions guided by the candidate model.
This staging keeps the expensive bounded-universal reductions to a minimum.

## Tasks

| id | task | key refs | size | exit |
|---|---|---|---|---|
| T-D.1 | reduction lemmas for `substr`/`indexof`/`prefixof`/`suffixof` | cvc5 `theory_strings_preprocess` | M | these ops decided over unbounded strings |
| T-D.2 | `replace`/`replace_all`/`replace_re` (latter on Phase-C regex) | cvc5 + Phase C | L | replace family decided |
| T-D.3 | `contains` + lazy negated-`contains` (bounded universal, deferred) | LRT; cvc5 CAV 2022 lazier reductions | M | `¬contains` decided without eager blowup |
| T-D.4 | **context-dependent simplification** loop | Reynolds et al. CAV 2017 | L | measured: most ext-fns discharged without full reduction |
| T-D.5 | high-level abstractions (arith-entailment, multiset, containment approx) | Reynolds et al. CAV 2019 | M | cheap UNSAT/SAT filters before reduction |
| T-D.6 | code-point reasoning for `to_int`/`from_int`/`to_code` | cvc5 code-point solver | M | numeric conversions decided |

## Soundness

- Each reduction lemma is a **valid semantic expansion** of the function — a
  consequence, not an added constraint; `sat` models replay through the ground
  evaluator's true semantics.
- The lazy/effort staging never changes the verdict, only when work happens —
  assert this with a test that compares eager vs lazy on a fixed suite.

## Exit criteria

- Full `str.*` extended-function set decided over unbounded strings via lazy
  reduction + context-dependent simplification.
- Measured: most extended functions discharged by context simplification without
  the full (expensive) reduction; no decide-rate regression.
- DISAGREE=0 vs Z3 on an extended-function fuzz set.
