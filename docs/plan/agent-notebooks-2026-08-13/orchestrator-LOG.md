# Orchestrator lab notebook — proof approaches session, 2026-08-12

Append-only. Everything here was measured in this session; nothing is recalled
from a summary. Machine: 4 cores, 61 GB, contended by three concurrent Opus
agents throughout — **all wall times are upper bounds.**

---

## Entry 1 — independent re-verification of the shell construction

**Why:** my own summary of the construction was wrong (I had it as the
`b = a-1` specialisation `a^k + a^(k-1) - 2a + 1`; it is actually general in
`(a,b,k)` with `N = b(a^(k-1) + 2(a^(k-2)+...+a))`). Re-derived from
`construction/construct.py` and enumerated rather than trusted.

**Method:** direct enumeration of every solution triple `x-y = bt, z = at`,
`t >= 1`, in `[1,N]`, against the shell colouring.

**Range:** `2 <= a <= 6`, `1 <= b <= 6`, `gcd(a,b) = 1`, `k = 2..5` (60 triples).

**Result:**
- `b < a`: solution-free in **24 of 24** triples.
- `b > a`: solution-free at `k = 2`, **defective at every `k >= 3`**.

So the source's soundness guard (`refuse when b >= a`) is empirically exactly
right, and its boundary is sharper than recorded: the guard is only needed for
`k >= 3`.

## Entry 2 — the `b > a` failures have a closed form (NEW)

The committed claim justifies the guard with "a sweep of the b>a regime found
19 of 19 parameter triples defective" — an empirical sweep. The failures for
`b = a+1` are in fact a single algebraic family:

    y = 1,  x = a*b^2 + 1,  z = a^2*b

verified at `a = 2,3,4,5` (giving `(19,1,12)`, `(49,1,36)`, `(101,1,80)`,
`(181,1,150)`). The identity `a(x-y) = a^2 b^2 = b(a^2 b) = bz` holds for all
`a, b`, so this is a candidate **provable** infinite counterexample family,
which would upgrade the sweep to a proposition. Handed to route A as its
Theorem 2.

**Negative result, recorded to prevent overclaiming:** the form does NOT
extend to general `b > a`. At `(a,b,k) = (3,5,3)` the defect is `(61,1,36)`
while `a*b^2+1 = 76`. Only the `b = a+1` subfamily is known to follow it.

## Entry 3 — FACT 1: `z` is always a multiple of `a`

With `gcd(a,b) = 1`, every solution has `z = at`, so `a | z` unconditionally.
Enumerated: 0 counterexamples over all coprime `a,b <= 7` at `n = 60`.

**Consequence (the lever):** a unit is never the `z` of a solution, so any
colour class made only of units is automatically solution-free. A violated
colour class must contain a multiple of `a`, and the violation forces
`v(t) = c-1`. This should collapse most of a case analysis and was sent to
route A.

## Entry 4 — FACT 2: a proved, weaker, general-`k` bound (the lifting)

If `chi` is a solution-free `k`-colouring of `[M]`, then (units -> a fresh
colour; `j = a j'` -> `chi(j')`) is a solution-free `(k+1)`-colouring of
`[aM + (a-1)]`. Follows from FACT 1 plus self-similarity: if `a` divides
`x, y, z` then `a | t` too, and `t = at'` reproduces the same equation.

Iterating from `f(1) = b` gives **`f(k) = a^(k-1)(b+1) - 1`**, checked
solution-free in **55 of 55** cases (`a <= 6`, `b < a`, `k <= 5`). At
`b = a-1` this is exactly `a^k - 1`, so it re-proves Chang-De Loera-Wesley's
Lemma 4.1 as a clean induction.

Sharpness: at `b = a-1` the colouring fails at `N+1` (the bound is exact for
this colouring); for `b < a-1` it survives past `N+1`, so the bound is not
sharp there.

**Value:** this is a rigorous general-`k` theorem available *now*, independent
of whether route A closes the shell proof. It is a safety net for the paper.
It is also strictly weaker than the shell (242 vs 318 at `(3,2,5)`), which
localises what the shell's proof actually has to earn: the gain comes from
*reusing* colour `i` for both the valuation stratum `V_i` and a unit shell.

## Entry 5 — the `k=5` witness, independently verified and dissected

Re-verified `witness-350.txt` from the claim ledger by my own enumerator:
**0 monochromatic solutions** among all triples in `[350]`. Confirms the
ledger's `checked` status.

Structure:
- Colour 2 is the valuation-1 stratum `V_1` **up to a single element**: the
  only `j` in `[350]` where `(v_3(j) = 1)` and `(colour = 2)` disagree is
  **`j = 60`**. So the witness is a one-point perturbation away from the clean
  stratum structure the shell colouring uses.
- The other four colours all mix units with higher valuations — it is not a
  shell colouring.
- Periodicity is real and 3-adic: agreement rate of `col[j] = col[j+p]` is
  **0.633 at `p = 18`**, 0.607 at 78, 0.588 at 27, 0.519 at 9, against a
  chance rate of ~0.20. Note `p = 78` is exactly the shell's outermost cut
  `c_4`, and 9, 27 are powers of `a = 3`.

**Interpretation (provisional):** a *structured* colouring beating the shell
at `k = 5` may exist, built from period-`3^m` blocks. Not yet established.

## Entry 6 — the shell family is EXHAUSTED at `(3,2,5)` (NEW negative result)

**Question:** is the shell's ceiling of 318 a property of the *shape* or of
the particular cut widths `L_i = a^(i-1) b`?

**Method:** freed the cuts. The shell shape is determined by
`(0, c_2, c_3, c_4)`; the canonical construction picks `(0, 6, 24, 78)`. Key
simplification from FACT 1: `z` is always a multiple of `a`, so its colour is
`min(v(z), k)` **independent of the cuts** — the cuts only move `x` and `y`.

**Search:** exhaustive over `c_2 in [1,40]`, `c_3 in [c_2+1,90]`,
`c_4 in [c_3+1,150]` at `N = 319`. **264,680 cut vectors tested, 0 feasible.**
(Canonical cuts confirmed feasible at `N = 318`, infeasible at 319.)

**Conclusion:** 318 is the hard ceiling of the entire two-sided-shell family
at `(a,b,k) = (3,2,5)`, not an artifact of the chosen widths. Since
`R_5(3(x-y)=2z) > 350` is witnessed and verified, the gap of 32+ **cannot be
closed by tuning this construction** — it requires a structurally different
colouring. This sharpens the paper's "not tight at k=5" from an observation
into a bounded negative result about the construction family.

**Caveat, stated honestly:** the search is exhaustive only within the stated
box. Cut vectors with `c_2 > 40`, `c_3 > 90`, or `c_4 > 150` were not tested.
The box was chosen to comfortably contain the canonical point (6, 24, 78);
I have not proved the optimum must lie inside it.

---

## Entry 7 — CORRECTION to Entry 4 (the lifting base case was wrong)

Per my own rule, appending rather than editing Entry 4 away.

**The error:** Entry 4 gave the base case as `f(1) = b`, from "solution-free
iff `N < min(a, b+1)`". That is backwards. A `t = 1` solution needs **both**
`z = a <= N` **and** `x = y + b <= N` with `y >= 1`. So a solution exists iff
`N >= a` AND `N >= b+1`, hence solution-free iff **`N <= max(a-1, b)`** — a
max, not a min.

**Check:** empirical maximum solution-free `N` for one colour matches
`max(a-1,b)` in **16 of 16** coprime pairs with `a <= 6, b <= 5`.

**Corrected result:** the recursion `f(k+1) = a f(k) + (a-1)` with base
`f(1) = a-1` (for `b <= a-1`) solves to **`f(k) = a^k - 1`**, uniformly in `b`.

**Consequence — Entry 4 overclaimed and this retracts it.** The lifting does
NOT give a new bound. `a^k - 1` is exactly Chang-De Loera-Wesley Lemma 4.1,
already published. What the lifting contributes is a *clean inductive proof*
of that known lemma covering all `b < a` at once — useful as the structural
engine and as a rigorous fallback, but **not novel**. The expression
`a^(k-1)(b+1) - 1` from Entry 4 describes a real solution-free colouring
(verified at 55 points) that is simply not maximal: it is `<= a^k - 1` with
equality only at `b = a-1`.

**Sharpness, freshly measured:** the valuation colouring `min(v_a(j), k-1)`
is solution-free at `a^k - 1` and **fails at `a^k`**, for every tested
`a <= 6`, `b < a`, `k <= 5`. Exactly tight for that colouring.

Route A was sent this correction immediately, since it had the wrong formula.

**Process note worth keeping for the paper's own honesty section:** this is
the second selection/arithmetic error of the wider session to be caught only
by re-deriving a result rather than re-reading it. The error was invisible in
the verification data — the colouring I tested really was solution-free, so
every check passed; only the *claim of maximality* was wrong. Passing tests
do not detect a bound that is merely not tight.

## Entry 8 — RIGIDITY: the canonical cut vector is UNIQUE (NEW, and the best
## mathematical finding I have produced this session)

This supersedes Entry 6 and removes its caveat. Entry 6 searched an arbitrary
box (`c_2 <= 40, c_3 <= 90, c_4 <= 150`). Here I use the **natural and
complete** bound: the two-sided shells may not cross the midpoint, so
`0 < c_2 < ... < c_{k-1} < N/2` exhausts the shape.

**Method:** free every cut, keep the valuation strata fixed (legitimate,
since by FACT 1 the colour of `z` is `min(v(z),k)` independent of the cuts).
Enumerate all cut vectors at `N = N_shell(a,b,k)` and at `N+1`.

| (a,b,k) | N | canonical cuts | vectors tested | feasible @N | @N+1 |
|---|---|---|---|---|---|
| (3,2,3) | 30 | (0,6) | 14 | **1** | 0 |
| (4,3,3) | 72 | (0,12) | 35 | **1** | 0 |
| (3,2,4) | 102 | (0,6,24) | 1,225 | **1** | 0 |
| (4,3,4) | 312 | (0,12,60) | 11,935 | **1** | 0 |
| (3,2,5) | 318 | (0,6,24,78) | 644,956 | **1** | 0 |

**In every case the unique feasible vector IS the canonical one**, i.e. the
one with widths `c_i - c_{i-1} = L_i = a^(i-1) b`.

**Why this matters.** It reframes the construction entirely. The widths
`L_i = a^(i-1) b` are not a tuned parameter choice that happens to work —
within the two-sided shell shape they are the **only** choice that works at
the extremal `N`, and the shape admits nothing at all at `N+1`. The
construction is rigid, hence canonical. That is a much stronger and more
interesting statement than "here is a colouring", and it is a natural
theorem to prove (route A should be told, but only after it has its own
proof, so as not to redirect it mid-argument).

**The k=5 contrast, now sharp.** At `k <= 4` the shell's unique optimum
coincides with the true Rado number (31, 73, 103, 313 — all proved by
refutation elsewhere in this work). At `k = 5` the unique optimum is 318
while `R_5(3(x-y)=2z) > 350` is witnessed and verified. So the failure at
`k = 5` is a failure of the **shape**, not of the parameters, and no amount
of tuning can recover it. This converts the paper's "the construction is not
tight at k=5" from an observation into a bounded negative result:

> Within the two-sided shell family, 318 is unimprovable at (3,2,5); the
> true value exceeds 350; therefore a fundamentally different colouring is
> required, and we exhibit one (the verified 350-witness) without a
> generalising description.

**Honesty note.** "Unique" here is unique *within the two-sided shell shape
with valuation strata fixed*. It is not a uniqueness claim about all
solution-free colourings — the 350-witness is itself a solution-free
colouring outside this family. The claim is exactly as scoped in the table.

## Entry 9 — REFINEMENT of Entry 8: rigidity is exactly a `b = a-1` phenomenon

Entry 8 tested only `b = a-1` points and I stated it as though it were a
general fact about the shell shape. Extending the sweep shows the dichotomy
is sharp, and Entry 8 must be read with this scope.

| regime | (a,b,k) tested | feasible @N | feasible @N+1 | verdict |
|---|---|---|---|---|
| `b = a-1` | (3,2,3) (4,3,3) (5,4,3) (6,5,3) (3,2,4) (4,3,4) (5,4,4) (3,2,5) | **1, canonical** | **0** | rigid |
| `b < a-1` | (3,1,3) (4,1,3) (5,1,3) (5,2,3) (5,3,3) (4,1,4) (5,2,4) (5,3,4) | many (3–1125) | **same count** | slack |

Examples of the slack regime: `(5,3,4)` has **1125** feasible cut vectors at
`N = 555` and **1125 again at N+1**; `(4,1,4)` has 64 and 64.

**Interpretation.** For `b < a-1` we have `N_shell < a^k - 1`, so the shell
bound is not extremal at all — the plain `a`-adic valuation colouring
(Corollary "R_k >= a^k", i.e. CDW Lemma 4.1) is strictly better there, and
the shell shape has room to spare, which is exactly why many cut vectors work
and keep working past `N`. The shell construction is therefore properly a
**`b = a-1` construction**, and that is the only regime where it is both
extremal and rigid.

Check that it beats the known bound in its own regime: at `(5,4,4)`,
`N_shell + 1 = 741` versus `a^k = 625`; at `(6,5,3)`, 241 versus 216. Yes,
strictly better throughout `b = a-1`.

**Corrected statement to carry forward:**

> Let `b = a-1`, `k >= 3`. Within the two-sided shell shape with valuation
> strata fixed, the cut vector with widths `L_i = a^(i-1) b` is the UNIQUE
> solution-free choice at `N = N_shell(a,b,k)`, and no choice is
> solution-free at `N+1`. Verified at 8 parameter points. For `b < a-1` the
> statement is false and the shape is slack.

Note `(5,4,4)` gives `N = 740`, matching the already-verified lower-bound
witness for the predicted `R_4(5(x-y)=4z) = 741` — an independent
consistency check on both.

## Entry 10 — CORRECTION to Entry 2 (my counterexample family was k=3 only)

Route A refuted my Entry 2 family and produced the right one. I re-verified
both myself rather than take the report on trust.

**My claim (Entry 2), now retracted:** for `b = a+1`, `k >= 3`, the triple
`(a b^2 + 1, 1, a^2 b)` is monochromatic. **False for `k >= 4`.** The
arithmetic identity holds for all `k` — that part was right — but the colour
claim does not, because the triple is *fixed* while `N` grows with `k`, so it
drifts out of shell 2 into the core. Measured: monochromatic at `k = 3` for
`a = 2,3,4,5` (colours `(2,2,2)`); at `k = 4,5,6` the colours are `(4,2,2)`
in every one of those cases. I had verified only `k = 3` and generalised
without checking — the same failure mode as Entry 7, and the second time this
session that a claim survived its tests because the tests did not vary the
parameter that mattered.

**Route A's correct family, verified by me:** for every `b > a` coprime to
`a` and every `k >= 3`,
```
    (X, Y, Z) = (N - ab + 1,  1,  a(N/b - a))
```
is a valid solution and is monochromatic of colour 2. Checked over all
coprime `a <= 6`, `a < b <= a+6`, `k = 3,4,5`: **all valid, all
monochromatic**. Unlike mine, this witness *moves with N*.

It also resolves the loose end in Entry 2: I recorded `(3,5,3) -> (61,1,36)`
as "anomalous, does not follow the form". The moving formula predicts exactly
`(61,1,36)` there. There was no anomaly; my formula was simply wrong.

**Consequence:** the `b >= a` soundness guard is now backed by a proved
uniform family rather than a 19-point sweep — which was Entry 2's goal, just
reached with a different (correct) witness.

## Entry 11 — three independent routes converge on `b = a-1`

Worth recording because the agreement was not coordinated:

- **My Entry 9** (exhaustive cut-vector enumeration): the canonical cut
  vector is unique exactly when `b = a-1`; for `b < a-1` the shape is slack.
- **Route A** (direct proof): `N+1 > a^k` iff `b = a-1` and `k >= 3` — i.e.
  the construction beats the known baseline exactly on that line.
- **Route A** again: its Lemma 4 is *exactly tight* at `b = a-1, c = k-1`
  (252 equalities, 0 elsewhere).

I had predicted from Entry 9's rigidity that any correct proof would have to
saturate its inequality at the canonical widths, and sent that to route A as
an optional check. Their Lemma 4 does exactly that, and they reported it
independently. Rigidity (measured) and tightness-of-the-bound (proved) are
two views of the same fact.

## Entry 12 — status of the three routes

- **Route A: Theorem 1 PROVED** for `a >= 2, b >= 1, gcd(a,b)=1, b < a,
  k >= 2`. This is the general-`k` theorem that was previously "verified at
  11 points, not proved". Plus an exact characterisation — the shell
  colouring is solution-free **iff `b < a` or `k = 2`** — which matches my
  Entry 1 sweep (24/24 clean for `b<a`; clean at `k=2` even for `b>a`)
  exactly. No upper bounds: nothing here shows `R_k = N+1`, so the `(3,2,5)`
  non-tightness stands.
- **Route C: C2 reached with ZERO axioms.** `Nat` is already a real
  inductive with a real recursor in the logic prelude, so induction needed no
  axiomatisation. 9 kernel-checked `forall`-statements over `N`, 7 negative
  controls all rejected. I re-ran the suite myself: **9 passed, 0 failed**.
  Not the conjecture — solution-freeness is neither proved nor assumed there.
- **Route B: still running.**

## Entry 13 — I read and checked route A's proof line by line

Not taking the agent's word for it. I verified the algebra and the case
analysis independently; the computational stress tests are theirs, the
mathematical review below is mine.

**Lemma 4 (shell gap) — correct.** Verified each step:
`Sigma_{k-2} = Sigma_{c-1} + a^c T` (the tail factors as
`a^c(1 + a + ... + a^{k-2-c})`); `c_c = b Sigma_{c-1}` from
`c_i = c_{i-1} + a^(i-1) b`; hence `N - 2c_c = b a^(k-1) + 2b a^c T`. The
bound `0 < theta < 2` is where `b <= a-1` enters, via
`b Sigma_{c-1} = b(a^c - a)/(a-1) <= a^c - a < a^c`. The integer step
`s <= b a^(k-1-c) + 2bT + 1` is valid since the other terms are integers and
`theta < 2`. I expanded the final chain myself and it collapses exactly as
claimed to `b[a^(k-2)(a-b) + 2a^(c-1)T(a-b) - a^(c-1)] >= b[a^(k-2) -
a^(c-1)] >= 0`, using `a-b >= 1`, `T >= 0`, `c-1 <= k-2`.

**Lemma 5 (size) — correct.** `N <= (a-1)a^(k-1) + 2(a-1)Sigma_{k-2} =
a^k + a^(k-1) - 2a`, using `(a-1)Sigma_m = a^(m+1) - a`; and
`2a^k - (a^k + a^(k-1) - 2a) = a^(k-1)(a-1) + 2a > 0`.

**Case analysis — exhaustive and each branch valid.** The engine is that
`a | z` forces `chi(z) = min(v(z),k)`, which *pins* `v(t) = c-1` for
`c <= k-1` and `v(t) >= k-1` for `c = k`. The classification of a
colour-`c` element into (alpha) non-unit with `v = c` or (beta) unit in
`Sh_c` is exhaustive precisely because `min(v,k) = c < k` forces `v = c`.
I checked all seven branches; each is a genuine contradiction. `k = 2` is
consistent: the middle case is empty and `c` ranges over `{1, k}`.

**Verdict: Theorem 1 is proved.** This is the result that was, at the start
of this session, "verified at 11 computational points and asserted in the
construction source". It is now a theorem with a reviewed proof.

**Independent convergence worth recording.** Route A's Remark on sharpness
computes the slack of Lemma 4 at `c = k-1` (where `T = 0`) as
`b a^(k-2)(a - b - 1)`, which vanishes **exactly at `b = a-1`**. That is my
Entry 9 rigidity result — measured by exhaustive cut enumeration — arrived at
analytically and independently. Their worked example `(a,b,k,c) = (3,2,4,3)`:
`N = 102`, `floor(102/27) = 3`, `b a^2 s = 54 = 102 - 48`. Equality, as
predicted.

**Route A also refuted a natural false route** and recorded it so nobody
retries: the real-valued argument `x - y = (b/a)z <= (b/a)N` does not
suffice, because at `c = k-1` one has `2ab Sigma_{k-2} - N = ab(a^(k-2) - 2)
> 0` for `a >= 2, k >= 4`. The integrality of `s = t/a^(c-1)` is essential,
not a convenience. I checked the counterexample at `(3,2,4)`: `N(a-b) = 102`
versus `2ab Sigma_2 = 144`. Confirmed.

**Still not established (do not let this drift):** no upper bounds anywhere
in route A. Nothing shows `R_k = N+1` at any point; the `(3,2,5)`
non-tightness stands, and the exact values 31/73/103/313 rest on the
refutation side, which is a separate body of evidence.

## Entry 14 — the CAS gap, and closing it

**The user asked whether we were actually using axeyum's CAS crate. We were
not.** Route A: "nothing was verified by axeyum: no cargo, no solver, no
DRAT". Route C used the Lean kernel. My own checks were all Python. Only
route B was pointed at `axeyum-cas`, and it was still running. This is drift
— the same drift the user flagged earlier in the session — and worth logging
plainly rather than quietly fixing.

**Closed it.** Built `scratchpad/casproof/` against `axeyum-cas` +
`axeyum-ir` and verified the proof's algebraic content with `MvPoly` exact
rational polynomial arithmetic. Every identity is checked by building the
difference of the two sides and testing `is_zero()` — a proof for **all**
values of `a`, `b`, `T`, not a numeric sample. Symbolic exponents are handled
by instantiating the integer parameters `k, c` over a range while keeping
`a, b, T` symbolic.

Checked (107 positive):
1. `(a-1)*Sigma_m = a^(m+1) - a`, m = 1..10.
2. The split `Sigma_(k-2) = Sigma_(c-1) + a^c*T`, all k = 3..10, c = 2..k-1.
3. **Lemma 4's entire final chain**, all k = 3..10, c = 2..k-1 (36 cases).
4. Lemma 5's size identity at `b = a-1`, k = 2..10.
5. Lemma 4's slack at `c = k-1` equals `b*a^(k-2)*(a-b-1)` — the algebraic
   form of the rigidity phenomenon, k = 3..10.
6. Theorem 2's identity `a(X-Y) = bZ` for the moving witness, k = 3..10.

Negative controls (11), all of which correctly did **not** vanish: a wrong
`Sigma` closed form (`a^(m+1) - 1`), Lemma 4 with the `+1` truncation term
dropped, and Theorem 2 with a sign slip in `W`.

```
axeyum-cas MvPoly exact symbolic checks: 118 run, 0 failed
```

**Why this is worth more than my hand-check in Entry 13.** Entry 13 was me
expanding the algebra by hand at a few parameter values. This verifies the
same identities *symbolically over Q* across 36 (k,c) pairs, so it covers all
`a` and `b` at once. Item 5 in particular turns my Entry 9 rigidity
observation — which was an exhaustive *numeric* enumeration over cut vectors
— into an exact algebraic statement: the slack is literally the polynomial
`b*a^(k-2)*(a-b-1)`, which is zero precisely on the line `b = a-1`.

## Entry 15 — dead end: the periodic-colouring search

Recorded because negative results belong in the log. I probed whether a
*periodic* unit colouring (units coloured by `j mod p` for `p in {9,18,27,
54,81,162}`, valuation strata fixed) could beat the shell ceiling of 318 at
`(3,2,5)`, motivated by the 350-witness's period-18 correlation (Entry 5).

The DFS was written without constraint propagation and did not finish: killed
at its 1500 s timeout (exit 143) with output still buffered, so **no result
was obtained at all**. Two process faults worth naming: (i) unbuffered output
was not forced, so a 25-minute run produced zero information; (ii) the search
space for the larger periods (p = 162 gives 108 free residues over 5 colours)
was never estimated before launching.

Not retried, because Entry 8/9's rigidity result answered the underlying
question more decisively: the shell family is exhausted at 318 by exhaustive
enumeration, so the question is not "can the shell be tuned" but "what
different shape works", and a strictly periodic colouring is a poor candidate
given the witness agreed with period 18 only 63% of the time.

## Entry 16 — CORRECTION to Entries 11 and 13: I identified the wrong mechanism

Route A pushed back on my rigidity interpretation and is right. I verified it
myself rather than accept either position.

**What I claimed** (Entries 11, 13): that my Entry 9 cut-vector rigidity and
route A's Lemma 4 tightness are "two views of the same fact", and I advised
route A that its inequality should be saturated at the canonical widths.

**Test:** perturb each canonical cut by +/-1, find the monochromatic solution
that appears, and classify which of the seven proof branches it belongs to.

| point | perturbation | refuting branch |
|---|---|---|
| (4,3,4) | c2 -1, c2 +1, c3 +1 | **B4 — same shell interval (WIDTH)** |
| (4,3,4) | c3 -1 | **B8 — core (WIDTH)** |
| (3,2,4) | all four | **B4 / B8 (WIDTH)** |
| (3,2,5) | all six | **B4 / B8 (WIDTH)** |
| all three | canonical at N+1 | **B8 — core (WIDTH)** |

**B5, the Lemma 4 branch, never fires — not once, in either direction, at
any point.** My advice pointed route A at the wrong inequality.

**The correct mechanism.** Cut-vector rigidity is governed by the *width*
branches: each shell interval holds exactly `L_c` elements, giving
`x - y <= L_c - 1`, against `x - y >= L_c` from the solution form. Tight by
exactly one. Widen any shell by a single element and the bad pair appears
immediately — on the left when widening, on the right when narrowing, which
is what the two-sidedness buys. Lemma 4 constrains *cross-shell* distance,
a different quantity; its slack for `c < k-1` is correct and not a symptom
of weakness.

**What survives.** Two true statements that I wrongly merged:
1. The CAS result (Entry 14, item 5) stands: Lemma 4's slack at `c = k-1` is
   exactly `b*a^(k-2)*(a-b-1)`, vanishing iff `b = a-1`. True, verified
   symbolically — just not the mechanism of cut rigidity.
2. The `b = a-1` line in my Entry 9 *is* the same statement as route A's
   extremality proposition, but for a different reason than I gave: the
   `c = k` width constraint bites only when its minimal witness `z = a^k`
   fits in `[1,N]`, i.e. `a^k <= N`, which holds **iff `b = a-1` and
   `k >= 3`**. That is why rigidity is a `b = a-1` phenomenon.

**Pattern worth recording for the paper's methods discussion.** This is the
third error of mine caught this session, and all three share a shape: Entry 7
(base case `min` for `max`), Entry 10 (a family verified only at `k=3` and
generalised), and now Entry 16 (a correct correlation attributed to the wrong
cause). In each case the *data* were fine and the *inference* was wrong —
Entry 9's rigidity numbers were correct and remain correct; only my
explanation of them was false. Numerical verification does not discipline
causal claims. Route A caught this by running a discriminating experiment
(which branch fires?) rather than by re-checking the numbers, which is the
right instinct and the one I had failed to apply to my own result.

## Entry 17 — a proof strategy for the N+1 / uniqueness theorem, with its gap

Route A flagged my `feasible @ N+1 = 0` result as "reproduced at 6 points,
not proved — natural next theorem". A pigeonhole argument appears to prove it
*and* the uniqueness in one stroke.

**Identity.** With `w_c = c_c - c_(c-1)` (`c = 2..k-1`) and core width
`W = M - 2c_(k-1)`, trivially `2(w_2 + ... + w_(k-1)) + W = M`.

**Strategy.** If solution-freeness forces `w_c <= L_c` and `W <= L_k`, then
`M <= 2(L_2+...+L_(k-1)) + L_k = N`. Hence `M = N+1` is impossible, and at
`M = N` equality forces `w_c = L_c` for every `c` — the canonical vector,
uniquely. Both halves fall out together.

**The width bound is FALSE in general.** Measured in the slack regime:

| (a,b,k) | N | solution-free | violating `w_c <= L_c` |
|---|---|---|---|
| (3,1,3) | 15 | 3 | 2 |
| (4,1,3) | 24 | 4 | 3 |
| (5,2,3) | 70 | 10 | 9 |
| (5,3,3) | 105 | 15 | 14 |
| (4,1,4) | 104 | 64 | 63 |

Example: `(3,1,3)` with cuts `(0,1)` has core width 13 against `L_3 = 9`, and
is solution-free.

**Why, and why that is reassuring.** A width constraint bites only if its
minimal witness fits: the bad pair at distance `L_c` needs `z = a^c <= M`. At
`(3,1,3)`, `a^k = 27 > N = 15`, so the core bound has no witness. The binding
case `c = k` needs `a^k <= N`, which by route A's extremality proposition
holds **iff `b = a-1` and `k >= 3`**. So the pigeonhole is valid exactly on
the rigidity line — an independent consistency check on Entry 9/16.

**Unclosed gap (mine, not route A's).** Showing `w_c > L_c` forces a
monochromatic solution needs a *unit* pair at distance `L_c` in the interval.
Since `c >= 2` gives `a | L_c`, we get `x = y (mod a)`, so x is a unit iff y
is — good. But at `w_c = L_c + 1` there is exactly one candidate start, and
one must show it is not a multiple of `a`. For canonical cuts this follows
from `a | c_i` and `a | N`; for arbitrary cuts it is open. Handed to route A
as a conjecture with the gap located, explicitly flagged as unverified.

## Entry 18 — route C verified independently

Re-ran their suite myself: **9 passed, 0 failed** (`cargo test -p
axeyum-lean-kernel --test rado_shell_arithmetic`). Nonzero count confirmed,
which this repo's CLAUDE.md specifically warns to check.

Verified their toolchain claim: `lean`, `lake`, `elan` are all **absent** and
there is no `~/.elan`. So their honesty flag is accurate — the 42 KB export
is emitted and structurally checked but has **not** been validated by real
Lean. That remains the highest-value single next measurement.

Structural check of the export, done by me: **0 `sorry`, 0 `axiom`
declarations**, 14 theorems, 6 defs, 2 inductives, terminating in
`#print axioms shell_closed_form`. The final statement is a genuine
`forall`-quantified equation over N, and its proof term is explicit — built
from `AxNat.rec` (real induction), `Eq.rec`, `left_distrib`, `mul_assoc`,
`mul_comm`, `add_assoc`, `mul_one`, and the separately proved
`geo_closed_form`. It is a proof term, not a stub.

**Process note:** I tailed a file with megabyte-long lines and dumped a large
proof term into my context. Use `cut -c1-200` or `grep -c` on generated proof
artifacts; they are not human-line-length files.

## Entry 19 — the Rigidity Theorem is PROVED, and my table had a blind spot

Route A closed the Entry 17 gap and proved the theorem for all `a >= 2`.

**How the gap closed.** I had said: at `w_c = L_c + 1` there is only ONE
candidate start, and one must show it is not a multiple of `a`. Wrong count —
**the shell is two-sided, so there are TWO candidate starts**,
`y_L = c_(c-1) + 1` and `y_R = M - c_c + 1`. The obstruction needs *both* to
be multiples of `a`, which forces `c_(c-1) = -1` and `M = -1 (mod a)`. Hence:
- at `M = N`, since `a | N`, the obstruction would need `a | 1` — impossible,
  so **no obstruction can ever occur at `M = N`**, the pigeonhole closes, and
  equality forces the canonical vector;
- at `M = N+1`, it needs `a | 2`, i.e. **`a = 2` only**.

**The blind spot.** The `a = 2` case is real: route A's width-lemma audit
found the obstruction **117 times, every one at `a = 2, M = N+1`**, zero
elsewhere. My Entry 9 rigidity table contains **no `a = 2` point at all** —
on the line `b = a-1` that means `(2,1,k)`, which I never enumerated. Route
A's earlier sweep missed it too. An untested corner on both sides,
independently.

Closed by a **defect induction** uniform in `a`: with `e_c = w_c - L_c` and
`E_j = e_2 + ... + e_j`, the trigger `e_c = 1` requires `E_(c-1) = -1 (mod
a)`, which rules out `E_(c-1) = 0` and forces `E_j <= 0` throughout,
contradicting `2E_(k-1) + e_K = 1`.

**My verification of the corner** (exhaustive, my own code):

| (a,b,k) | N | canonical | vectors | feas @N | @N+1 |
|---|---|---|---|---|---|
| (2,1,3) | 8 | (0,2) | 3 | 1 = canonical | 0 |
| (2,1,4) | 20 | (0,2,6) | 36 | 1 = canonical | 0 |
| (2,1,5) | 44 | (0,2,6,14) | 1,330 | 1 = canonical | 0 |
| (2,1,6) | 92 | (0,2,6,14,30) | 148,995 | 1 = canonical | 0 |

The theorem holds at `a = 2`. The 117 "obstructions" are obstructions to the
*width lemma's witness construction*, not counterexamples to the theorem —
the defect induction covers them.

**Route A also corrected itself**, which I want on the record since I asked
them not to tidy: their earlier claim that two-sidedness matters because
"narrowing exposes a unit pair on the right" was true but not sharp. The
load-bearing statement is that two-sidedness supplies **two** candidate
starts. With one-sided shells the residue argument loses `a | M - c_c + 1`
and part (1) does not go through at all.

**Scope, unchanged and worth restating:** Theorem 3 is about the shell
*shape* only. It does not say `R_k = N+1`. At `(3,2,5)` a solution-free
5-colouring of `[1,350]` exists while `N = 318`; that colouring is simply not
of this shape. Shape-optimality is not global optimality.

## Entry 20 — the paper justifies cube-and-conquer with a defect WE FIXED

The user challenged this sentence in `05_method.tex`:

> "A monolithic proof is out of range at these sizes — one attempt was killed
> by the out-of-memory killer after two and a half hours with no verdict — so
> we split on the colours of six integers…"

**They are right and the claim is stale.** ADR-0381 (streaming DRAT) says
exactly what that OOM was:

> "On `F_226` (35,858 clauses) the single-run driver was **OOM-killed at
> 27.6 GiB RSS after ~2.5 h**, with the proof vector as the dominant
> consumer. … Until the core can stream, search-scale single-run proofs need
> either a large-memory host or the cube decomposition."

The core was buffering the entire proof in RAM as a `Vec<DratStep>`. Streaming
emission was landed *to fix precisely this*. So the paper cites a product
defect we repaired as though it were a property of the problem.

**Nobody re-measured after the fix.** Searched `docs/plan/` — no
post-streaming monolithic measurement exists anywhere. The paper's assertion
was therefore unsupported, not merely stale.

**Re-measured on s0** (24 cores, 123 GiB; the solve is single-threaded so
cores are not the variable). Driver: `parse_dimacs` + streaming solve with
`TextProofSink` to disk, `scratchpad/monolithic/`.

| | pre-streaming (ADR-0381) | post-streaming (measured now) |
|---|---|---|
| peak RSS | **27.6 GiB → OOM-killed** | **1.38 GiB** (VmHWM 1,448,920 kB) |
| proof | held in RAM | streamed to disk (GiB-scale, growing) |
| verdict at 2.5 h | none (killed) | run in progress |

**~20x memory reduction, and flat.** The memory failure mode is gone. Whatever
the paper ends up saying about monolithic refutation, *"killed by the OOM
killer"* cannot be the reason.

Instance confirmed as the ledger's: 904 variables, 35,858 clauses — the
35,858 matches ADR-0381 exactly.

Awaiting the time verdict. Three possible outcomes, all of which change the
paper:
1. finishes UNSAT → the monolithic claim is simply **false** and the
   justification must be rewritten around parallelism/checking, not feasibility;
2. hits the deadline with flat memory → the honest reason is **time**, not
   memory, and the sentence must say so;
3. OOMs again → streaming did not fix it, which would be a product finding.

**Process note.** This is the second time this session a paper claim rested on
a measurement taken before the defect it describes was repaired (the first was
the stale `R_5 > 319` where the ledger had a checked 350). Both were caught by
a human reading the prose, not by a gate. `check_claims_complete.py` covers
the two exact values only — it does not police *narrative* claims about
performance or feasibility, and those have now drifted twice.

## Entry 21 — the monolithic feasibility LADDER (much better than the binary test)

Entry 20's single re-measurement answers "does F_226 finish". A ladder across
instance sizes answers the question the paper actually needs: **where does
monolithic refutation stop being feasible?** All runs use axeyum's own
proof-producing CDCL with streaming DRAT to disk.

| instance | (a,b) | clauses | verdict | wall | peak RSS |
|---|---|---|---|---|---|
| F_56 | (2,1) | 5,206 | **UNSAT** | **0.0 s** | 0.00 GiB |
| F_81 | (3,1) | 8,044 | **UNSAT** | **0.8 s** | 0.02 GiB |
| F_103 | (3,2) | 10,276 | **UNSAT** | **7.2 s** | 0.10 GiB |
| F_226 | (2,3) | 35,858 | running | >1,566 s | 5.46 GiB |
| F_313 | (4,3) | 63,812 | running | — | — |

Hosts: small ladder on s6 (16 cores, 26 GiB), F_226 on s4 `/data0`, F_313 on
s0 home. The solve is single-threaded, so core counts are not a variable.

**The shape is a cliff, not a slope.** Across 5.2k → 8.0k → 10.3k clauses the
time is 0.0 → 0.8 → 7.2 s: roughly **9x per ~25% more clauses**. Memory tracks
it: 0.00 → 0.02 → 0.10 GiB. Then F_226 at 3.5x the clause count of F_103 has
not finished in 26 minutes.

**Correction to Entry 20.** I described post-streaming memory as "flat". It is
not: 1.38 → 2.08 → 5.46 GiB over 26 minutes on F_226. Streaming removed the
*proof* from RAM — ADR-0381 called it "the dominant consumer" at 27.6 GiB —
but the clause database still grows. The honest statement is **~5x lower and
growing more slowly**, not flat. This also rules out s5/s6/s7 (26 GiB) as
hosts for long monolithic runs.

**What the paper can now say**, once the two large runs report, is a measured
boundary rather than an assertion: monolithic refutation is cheap through
~10^4 clauses and the headline instances sit beyond it — with the reason being
**time**, not the out-of-memory kill that ADR-0381 already repaired.

## Entry 22 — suspected P0 frontier regression: bisected, NOT ours

Both CAS agents were killed when the previous process exited. The bridge
agent's main work had already landed as `175372bdc`; the benchmark agent's
corpus is on disk uncommitted. On inspection **all five frontier ratchet JSONs
were dirty**, with `bv_reduction` at 26 against a committed baseline of 30.

**Treated as a possible P0** — a new route in the dispatch path could plausibly
push borderline instances over budget.

**Bisect (each an isolated worktree, `frontier_bv_reduction` only):**

| commit | what it is | result |
|---|---|---|
| `175372bdc` | CAS bridge (both new routes) | FAIL, frontier 26 |
| `9f0f4ed00` | the merge, **before** the bridge | FAIL, frontier 26 |
| `61ee26217` | my lane **before** the merge; solver untouched | FAIL, frontier **25** |

**Verdict: nothing in this session caused it.** The ratchet reads 25–26 on
this box at every point tested, including before any of today's work.

**Why: it is a wall-clock measurement on a 4-core box.** The lost instances
(N = 27–30) each returned `unknown` at ~4009 ms against a **4000 ms budget** —
at the measurement's resolution limit, which is exactly the failure mode the
test's own panic message warns about ("if the lost instances sit within 20 % of
the budget, the measurement is at its resolution limit, not the solver"). Each
was already retried 3 times at load ~1.0, and the top local process was Claude
itself at 8.8 % CPU, so the box was genuinely quiet. The baseline of 30 (and
the recorded 38) was surely captured on a 16–24 core host.

Corroborating: only the two *uncapped* families moved (bv_reduction 38→26,
lia_cuts 35→26); the three sitting at 40 are capped and could not drop. And
`lia_cuts` actually **passes** — its baseline is 26, so 26 ≥ 26.

**Action: restored all five JSONs.** The 25/26 values must not be committed —
they would ratchet the roadmap floor down on the basis of a slow-machine
measurement.

**Honest gap I cannot close here:** I never obtained a *passing* bv_reduction
measurement on this box, so I cannot rule out a genuine regression somewhere in
the 60 merged commits from the other machine. What is established is only that
**no work from this session introduced it**. Confirming requires running the
ratchet on a 16+ core host; the other lane already runs full gates on s5 and is
the natural place to check.

---

## Open threads I am carrying

- Whether a period-18 or period-27 unit colouring, combined with valuation
  strata, beats 318 at `k = 5`. This is a SAT-shaped search and the natural
  thing to point axeyum at.
- Whether Entry 6's exhaustion generalises: is the shell family also exhausted
  at `(4,3,4)`, where it IS tight (312, `R = 313`)? That contrast would be
  worth stating.
