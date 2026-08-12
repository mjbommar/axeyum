# Route A — report

Deliverable: `proof.tex` (compiles with `pdflatex`, 8 pages, amsart, no packages
beyond amsmath/amsthm/amssymb; `proof.pdf` is built).
Evidence of how it was reached: `LOG.md` (append-only lab notebook).
Reproduce every number below with `./run_all.sh` (~10 s, one core, Python only).

**Bottom line.** Theorem 1 is proved in full, with no gap I am aware of, under
exactly the hypotheses `a >= 2, b >= 1, gcd(a,b) = 1, b < a, k >= 2`.
Theorem 2 is proved in a **stronger form than requested** — and the form I was
asked to prove is **false for k >= 4**; see §3. Together they give an exact
characterisation: the shell colouring is solution-free **iff `b < a` or `k = 2`**.

---

## 1. Exact theorem statements proved

Notation: `v = v_a` is the a-adic valuation (`v(j) = 0` for units);
`Sigma_m = a + a^2 + ... + a^m`, `Sigma_0 = 0`; `L_i = a^(i-1) b`;
`N = 2(L_2 + ... + L_{k-1}) + L_k = b(a^(k-1) + 2 Sigma_{k-2})`;
`c_1 = 0`, `c_i = c_{i-1} + L_i = b Sigma_{i-1}`;
`Sh_i = [c_{i-1}+1, c_i] U [N-c_i+1, N-c_{i-1}]` for `2 <= i <= k-1`;
`Core = [c_{k-1}+1, N-c_{k-1}]`; and chi is the shell colouring of the brief.

### Theorem 1 (main)

> Let `a >= 2`, `b >= 1`, `gcd(a,b) = 1`, `b < a`, `k >= 2`. Then `[1, N]`
> contains no monochromatic solution of `a(x-y) = bz` under chi. Consequently
> `R_k(a(x-y) = bz) >= N + 1 = b(a^(k-1) + 2 Sigma_{k-2}) + 1`.

Hypotheses used, and where:
- `gcd(a,b) = 1` — everywhere (solution form; `v(bt) = v(t)`).
- `a >= 2` — everywhere.
- `b < a` — in exactly **two** places: Lemma 4 (shell gap) and Lemma 5 (size).
  Every other branch of the case analysis needs only `gcd(a,b) = 1`.
- `k >= 2` — needed so that colour 1 means `v = 1` exactly.
- **No further hypothesis is required.** In particular `a = 2, b = 1` is
  covered, and no lower bound on `k` beyond 2 and no extra gcd condition is
  needed.

Proof shape (the shape suggested in the task, with the inequality found):
take `x - y = bt`, `z = at`, `t >= 1`; since `a | z` always, `chi(z) =
min(v(z), k)` pins `v(t) = c - 1` (for `c <= k-1`) or `v(t) >= k-1` (for
`c = k`). Then split on `c` and on whether each of `x, y` is a multiple of `a`
or a unit — seven branches, labelled B1..B7 in `verify_casetree.py`:

| branch | case | killed by |
|---|---|---|
| B1 | `c = 1`, both `v = 1` | valuation: `v(x-y) >= 1` but `v(t) = 0` |
| B2 | `2 <= c <= k-1`, both `v = c` | valuation: `v(x-y) >= c` but `v(t) = c-1` |
| B3 | any `c >= 2`, one multiple / one unit | valuation: `v(x-y) = 0` but `v(t) >= 1` |
| B4 | `2 <= c <= k-1`, both units, same interval of `Sh_c` | width: `x-y <= L_c - 1 < L_c <= x-y` |
| B5 | `2 <= c <= k-1`, both units, opposite ends of `Sh_c` | **Lemma 4** |
| B6 | `c = k`, both `v >= k` | **Lemma 5**: `[1,N]` holds `<= 1` multiple of `a^k` |
| B7 | `c = k`, both units in `Core` | width: `x-y <= L_k - 1 < L_k <= x-y` |

**Lemma 4 (shell gap).** For `a >= 2`, `1 <= b <= a-1`, `2 <= c <= k-1`, and any
integer `s >= 1` with `a^c s <= N`:  `b a^(c-1) s <= N - 2 c_c`.

**Lemma 5 (size).** For `1 <= b <= a-1`: `N <= a^k + a^(k-1) - 2a < 2 a^k`.

### Theorem 2 (sharpness) — proved in a stronger form than asked

> Let `a >= 2`, `b >= 1`, `gcd(a,b) = 1`, `k >= 3`. Put
> `W = a^(k-1) + 2 Sigma_{k-2} - a`,  `X = N - ab + 1`,  `Y = 1`,  `Z = aW`.
> Then `a(X-Y) = bZ`, and `chi(X) = chi(Y) = chi(Z) = 2`. Also `X, Y in [1,N]`
> always, and `Z <= N` iff `N(a-b) <= a^2 b`, which holds whenever `b > a`.
> Hence for every `b > a` coprime to `a` and every `k >= 3` the shell colouring
> is defective.

This covers **all** `b > a`, not just `b = a+1`. At `k = 3` it specialises to
`(X,Y,Z) = (ab(a+1)+1, 1, a^2(a+1))`, and further to `(ab^2+1, 1, a^2 b)` when
`b = a+1` — recovering the brief's family exactly.

### Proposition (k = 2)

> For `k = 2` and **every** `b >= 1` coprime to `a >= 2`, chi is solution-free
> on `[1, ab]`.

### Corollary (exact characterisation)

> `gcd(a,b) = 1` and `a >= 2` force `b != a`. The shell colouring of
> `[1, N(a,b,k)]` is solution-free **iff `b < a` or `k = 2`**.

### Proposition (when the bound is worth having)

> For `a >= 2`, `1 <= b <= a-1`, `gcd(a,b) = 1`, `k >= 2`:
> `N + 1 > a^k`  **iff**  `b = a-1` and `k >= 3`.
> At `b = a-1`, `N = a^k + a^(k-1) - 2a`, so
> `R_k(a(x-y) = (a-1)z) >= a^k + a^(k-1) - 2a + 1`.

---

## 2. Computational stress tests, per lemma

All commands run from `route-a/`. Every count below is nonzero and was read off
the actual output (see `LOG.md` for verbatim transcripts).

| # | Claim | Command | Range | Cases | Result |
|---|---|---|---|---|---|
| 1 | Theorem 1 conclusion (brute force) | `verify_bruteforce.py 10 5 12 blt` | `2<=a<=10`, `b<a` coprime, `2<=k<=5` | 124 parameter points / **2,329,779,230 solution triples** | 0 monochromatic |
| 2 | Sharpness picture (brute force) | `verify_bruteforce.py 6 5 14 bgt` | `2<=a<=6`, `a<b<=14` coprime, `2<=k<=5` | 89 parameter points | every `k=2` free; every `k>=3` defective |
| 3 | `N = b(a^(k-1)+2 Sigma_{k-2})` | `verify_lemmas.py 80 14` | `a<=80,k<=14` | 25,545 | PASS |
| 4 | `c_i = b Sigma_{i-1}` | same | same | 25,545 | PASS |
| 5 | `(a-1) Sigma_m = a^(m+1) - a` | same | `a<=80,m<=14` | 1,185 | PASS |
| 6 | core width `N - 2c_{k-1} = L_k` | same | `a<=80,k<=14` | 25,545 | PASS |
| 7 | splitting identity `N - 2c_c = b a^(k-1) + 2b a^c T` | same | `a<=80,k<=14,2<=c<=k-1` | 153,270 | PASS |
| 8 | `T = 0` iff `c=k-1`; `Sigma_{k-2} = Sigma_{c-1} + a^c T` | same | same | 153,270 | PASS |
| 9 | Lemma 2: chi array == definition pointwise | same | `a<=8,k<=5`, all `j in [1,N]` | 82 points, all j | PASS |
| 10 | Lemma 2: colour 1 = `{v(j)=1}`, no unit coloured 1 | same | same | 82 points, all j | PASS |
| 11 | Lemma 2: units coloured k iff in `Core` | same | same | 82 points, all j | PASS |
| 12 | Lemma 4 precondition `0 < theta < 2` | same | `a<=80,k<=14,c` | 153,270 | PASS |
| 13 | **Lemma 4** (floor form) | same | same | 153,270 | PASS |
| 14 | **Lemma 4** (explicit `s` form, cross-check) | same | `a<=7,k<=5,c` | 102 | PASS |
| 15 | **Negative control**: Lemma 4 FAILS at `c=2` when `b>a,k>=3` | same | `a<=80`, `b>a`, `k<=14` | 115,440 | PASS (all fail, as required) |
| 16 | **Lemma 5** `N <= a^k + a^(k-1) - 2a` | same | `a<=80,k<=14` | 25,545 | PASS |
| 17 | `N < 2a^k`, `N < a^k(1+b)` | same | same | 25,545 each | PASS |
| 18 | B6 vacuity: `#{j<=N : a^k divides j} <= 1` | same | same | 25,545 | PASS |
| 19 | `k=2`, any `b`: `N = ab < a^2 b` | same | `a<=80`, all coprime `b<=242` | 11,585 | PASS |
| 20 | **Case-tree exhaustiveness** | `verify_casetree.py 7 5 1400` | `a<=7`, `b<a`, `k<=5`, `N<=1400` | 53 points / **1,466,700 monochromatic pairs** | 0 UNCOVERED, 0 branch-claim failures, 0 admissible `t` |
| 21 | Theorem 2 family is colour-2 mono solution | `verify_theorem2.py 12 40 8` | `a<=12`, `a<b<=40` coprime, `3<=k<=8` | 1,290 | 0 failures |
| 22 | k=3, `b=a+1` reduces to `(ab^2+1,1,a^2 b)` | same | `a<=12` | 11 | 0 failures |
| 23 | k=3, general `b>a`: `X=ab(a+1)+1, Z=a^2(a+1)` | same | `a<=12,b<=40` | 215 | 0 failures |
| 24 | For `b<a` the family has `Z > N` (consistent with Thm 1) | same | `a<=12,b<a,k<=8` | 270 | 0 violations |
| 25 | `Z <= N` iff `N(a-b) <= a^2 b` | same | `a<=12`, all coprime `b<=40`, `k<=8` | 1,560 | 0 failures |
| 26 | `k=2`: `N=ab` and `X = 1 = Y` (family degenerates) | same | `a<=12,b<=40` | 260 | 0 failures |
| 27 | `N = a^k + a^(k-1) - 2a` at `b=a-1` | `compare_bounds.py` | `a<=59,k<=14` | 754 | 0 failures |
| 28 | lifting bound `a^(k-1)(b+1)-1 <= a^k - 1`, eq iff `b=a-1` | same | `a<=39,b<a,k<=12` | 5,203 | 0 failures |
| 29 | **Proposition 'beat'**: `N+1 > a^k` iff `b=a-1, k>=3`; plus `(a-1)N = b(a^k+a^(k-1)-2a)` | same | `a<=59,b<a,k<=14` | 14,105 | 0 failures |
| 30 | Lemma 4 equality holds **exactly** at `b=a-1, c=k-1` | ad hoc (logged, E16) | `a<=29,k<=11` | 12,105 instances | 252 equalities, all at `b=a-1,c=k-1`; 0 elsewhere; 0 misses |
| 31 | Cut-vector uniqueness at `b=a-1` (reproduces orchestrator) | `verify_rigidity.py` | 6 points `b=a-1`, 3 points `b<a-1` | 53,606 cut vectors enumerated | canonical unique at all 6; 1125/64/3 feasible at the 3 slack points — matches orchestrator exactly |
| 32 | Which branch refutes each single-cut perturbation | same | 6 points, all legal ±1 moves | 20 perturbations | all refuted; histogram `{B4:14, B7:6}`; **B5 never fires** |
| 33 | `a^k <= N` iff `b=a-1, k>=3` (core constraint active) | same | `a<=59,b<a,k<=14` | 14,105 | 0 failures |
| 34 | `a^c <= N` for all `2<=c<=k-1` (inner constraints always active) | same | `a<=39,b<a,k<=12` | 26,015 | 0 failures |
| 35 | `a\|N`, `a\|c_i`, shell endpoints `= 1 mod a` (units) | ad hoc (logged, E18) | `a<=29,b<a,k<=10` | 2,152 points | 0 failures |

Checks 15 and 30 deserve emphasis. Check 15 is a **negative control**: if
Lemma 4 held on both sides of `b = a`, I would have isolated the wrong
statement and the sharpness would be unexplained. It fails precisely where the
colouring fails. Check 30 shows Lemma 4 is *exactly tight* at `b = a-1`,
`c = k-1` — which is exactly the line where the construction is worth having.
There is no slack in the argument to absorb an error.

### One refuted conjecture, recorded

**Conjecture A (FALSE).** In branch B5, bound over the reals: `z <= N` and
`x-y = (b/a) z` give `x-y <= (b/a) N`, so it would suffice that
`N(a-b) > 2ab Sigma_{c-1}`.
**Refuted**: `2ab Sigma_{k-2} - N = ab(a^(k-2) - 2) > 0` for all `a >= 2,
k >= 4`. Witness `(a,b,k) = (3,2,4)`: `N = 102`, `N(a-b) = 102`,
`2ab Sigma_2 = 144`. The integrality of `s = t/a^(c-1)` is essential, not
cosmetic; see check 30 (`theta >= 1` in 6,075 of 12,105 instances, so the `+1`
in the floor bound is genuinely needed). This is recorded as a Remark in the
paper so a reader does not retry it.

---

## 3. Correction to the task brief: Theorem 2 as stated is false for k >= 4

I was asked to prove that for `b = a+1` and **`k >= 3`** the triple
`(x,y,z) = (a b^2 + 1, 1, a^2 b)` is monochromatic. It is **not**, for `k >= 4`.

- The **arithmetic** identity `a(x-y) = bz` does hold for all `a, b, k` (the
  script asserts it), which is presumably why the family looked general.
- The **colour** claim fails. The triple is *fixed* while `N` grows with `k`, so
  it slides out of the outermost shell into an inner shell or the core.
- Witness, `(a,b,k) = (2,3,4)`: `N = 60`, `Sh_2 = [1,6] U [55,60]`,
  `Sh_3 = [7,18] U [43,54]`, `Core = [19,42]`. Then `ab^2+1 = 19` is the first
  element of the core, so `chi(19) = 4`, while `chi(1) = chi(12) = 2`.
- Measured over `a in {2,..,6}`, `b = a+1`, `k in {3,..,6}`:
  **k=3: 5/5 monochromatic; k=4: 0/5; k=5: 0/5; k=6: 0/5.**

The correct statement, proved and much stronger, is Theorem 2 above with the
*moving* witness `X = N - ab + 1`. Cross-check that this is the right
generalisation: the brief separately notes that `(a,b,k) = (3,5,3)` is defective
at `(61,1,36)` and observes this does **not** match `ab^2+1 = 76`. My formula
gives `X = N - ab + 1 = 75 - 15 + 1 = 61` and `Z = a(a+a^2) = 36` — exact match.
So the brief's own "anomalous" example is explained by, and is evidence for, the
general form.

**Net effect: the requested result is strengthened, not weakened.** The task
wanted "an infinite family for `b = a+1`"; what is proved is an infinite family
for *every* `b > a` and *every* `k >= 3`.

## 4. Is `b < a` the exact hypothesis, or merely sufficient?

**Exact**, given the (forced) convention that `b != a`. Precisely:

- `b < a` => solution-free for all `k >= 2` (Theorem 1).
- `b > a` and `k >= 3` => **defective** (Theorem 2). Not "unknown", not "not
  covered by the proof" — an explicit monochromatic solution exists.
- `k = 2` => solution-free for **every** `b` coprime to `a` (Proposition).
- `b = a` is impossible under `gcd(a,b) = 1`, `a >= 2`.

So: solution-free **iff** `b < a` **or** `k = 2`. No condition on `a` beyond
`a >= 2` and none on `k` beyond `k >= 2` is needed, and no small-`a` exception
arises — `a = 2, b = 1` is covered by the general argument.

**Why `k = 2` escapes**, two independent reasons, both in the paper:
1. The shell index runs `2 <= i <= k-1`, which is empty at `k = 2`. There are no
   shells; every unit is coloured `k = 2` and the core is all of `[1,N]`. The
   two-sided geometry that `b > a` breaks is simply absent.
2. The defect family degenerates: at `k = 2`, `N = ab`, so
   `X = N - ab + 1 = 1 = Y`, i.e. `t = 0`, which is not a solution (verified,
   260 cases).
   The `c = k = 2` branch of the proof also needs a different argument at
   `k = 2` — `a^2 | x-y = bt` forces `a^2 | t` hence `x-y >= a^2 b > ab = N` —
   which is valid for **all** `b`, unlike the `N < 2a^k` route.

## 5. Gaps and non-claims

I am not aware of any gap in Theorem 1, Theorem 2, the `k=2` Proposition, the
characterisation Corollary, or Proposition 'beat'. Each is a finite chain of
elementary steps; the two non-trivial inequalities are stress-tested at 153,270
and 25,545 parameter points, and the case analysis is confirmed exhaustive on
1,466,700 concrete monochromatic pairs (0 uncovered).

Explicitly **not** claimed:

1. **No tightness / upper bounds.** Nothing here shows `R_k = N+1` for any
   parameter triple. The brief reports tightness at `(3,2,3)`, `(4,3,3)`,
   `(3,2,4)`, `(4,3,4)` and explicit failure at `(3,2,5)` (a solution-free
   5-colouring of `[1,350]` exists while `N+1 = 319`). I did not attempt upper
   bounds and the paper says any exactness claim is scoped to small `k`.
2. **Citation not verified.** The attribution of the `a^k - 1` baseline to
   Chang-De Loera-Wesley Lemma 4.1 is taken on trust from the brief. The
   *mathematics* (that `min(v(j),k-1)` is solution-free on `[1, a^k - 1]`) I did
   check; the *citation* I did not.
3. **Nothing was verified by axeyum.** No cargo was run, no solver invoked, no
   DRAT certificate produced. Route A is pencil-and-paper; the Python is a
   stress test of the proof, not a proof, and cannot be presented as one.
4. **The 2.33 billion enumerated triples prove nothing on their own.** They
   check that the written proof concerns the same object the brief measured.
   The theorem's content is that it covers infinitely many `(a,b,k)`.
5. **Shape-optimality is not proved.** The orchestrator's `feasible @ N+1 = 0`
   (the shell shape cannot be stretched past `N_shell`) was reproduced at six
   parameter points but not proved; see §7. It is also shape-local, not global:
   at `(3,2,5)` a solution-free 5-colouring of `[1,350]` exists while
   `N_shell = 318`.

## 6. Relation to the orchestrator's FACT 1 and FACT 2

- **FACT 1 (`a | z` always) — used, and it is the engine.** I derived it
  independently before the message arrived (LOG entry E1, Decision point 1). In
  the proof it appears as: `a | z` makes `chi(z) = min(v(z), k)` *unconditional*,
  which pins `v(t) = c-1` (or `>= k-1`). Everything else follows from that pin.
  The orchestrator's consequence — that a colour class of units alone is
  automatically safe — is subsumed: in the shell colouring no class is units
  alone, and the mixed branches (B3) die on valuation with no inequality, which
  is the same observation applied one level down.
- **FACT 2 — my proof is INDEPENDENT of it and does not subsume it, nor does it
  need to.** Theorem 1 is a direct case analysis, not an induction; it never
  uses the lifting. After the orchestrator's correction (`f(k) = a^k - 1`, i.e.
  the known baseline), the lifting is not a rival bound at all: I verified
  `a^(k-1)(b+1) - 1 <= a^k - 1` with equality iff `b = a-1` (5,203 cases, 0
  failures), so the retracted expression is dominated everywhere. The paper
  therefore uses `a^k - 1` as the sole baseline and records the lifting only as
  a remark — it gives a clean inductive proof of the *known* bound and isolates
  the self-similarity the shell colouring has to work around. **I did not
  re-derive `a^k - 1` from the lifting in full rigour**; it is stated as a
  remark, not as a theorem of this paper.
  My draft did briefly lean on the retracted figure; corrected on receipt and
  logged (E12).

## 7. The orchestrator's rigidity finding: cross-checked, and explained by the proof

The orchestrator freed the cut vector `(0, c_2, ..., c_{k-1})` (valuation strata
fixed, which is forced) and found the canonical vector is the **unique** feasible
one at `b = a-1`, while for `b < a-1` the shape is slack. Attached advice: my
inequality should be exactly tight, and slack would signal a weaker-than-true
result. I checked this rather than accepting it (`verify_rigidity.py`).

**Reproduced independently** (my own definitions, my own enumerator). All nine
rows match the orchestrator's counts exactly:

| (a,b,k) | N | canonical | tested | feas@N | feas@N+1 |
|---|---|---|---|---|---|
| (3,2,3) | 30 | (6,) | 14 | 1 | 0 |
| (4,3,3) | 72 | (12,) | 35 | 1 | 0 |
| (5,4,3) | 140 | (20,) | 69 | 1 | 0 |
| (6,5,3) | 240 | (30,) | 119 | 1 | 0 |
| (3,2,4) | 102 | (6,24) | 1,225 | 1 | 0 |
| (4,3,4) | 312 | (12,60) | 11,935 | 1 | 0 |
| (5,3,4) | 555 | (15,90) | 38,226 | 1,125 | 1,125 |
| (4,1,4) | 104 | (4,20) | 1,275 | 64 | 64 |
| (3,1,3) | 15 | (3,) | 7 | 3 | 3 |

(I skipped `(5,4,4)` and `(3,2,5)` — 67,896 and 644,956 vectors — as too
expensive on a shared box. The orchestrator has those two.)

**Which inequality is actually tight — the advice pointed at the wrong one.**
For each canonical vector I perturbed one cut by ±1 and identified which branch
of my case tree refutes the result. Over all 20 legal perturbations:

    branch histogram: {B4: 14, B7: 6}

**B5 — the Lemma 4 branch — never fires.** Rigidity is governed entirely by the
*width* branches B4 (two units in the same interval of a shell) and B7 (two
units in the core), each tight by exactly one: `x-y <= L_c - 1` versus
`x-y >= L_c`. Lemma 4 constrains the *cross-shell* distance, not the individual
widths, and correctly has slack for `c < k-1` (tight only at `c = k-1`,
check 30). So the slack in Lemma 4 is not a symptom of a weak result; the
equalities the rigidity demands are elsewhere in the case tree, and they are
exactly tight for every `c` and every `b < a`.

**Why rigidity is a `b = a-1` phenomenon — and it is Proposition 'beat' again.**
A width constraint at colour `c` bites only if its minimal witness fits: take
`s = 1`, giving a pair at distance `L_c` with `z = a^c`, a genuine solution iff
`a^c <= N`.

- For `2 <= c <= k-1`: automatic, since `N >= b a^(k-1) >= a^(k-1) >= a^c`
  (26,015 cases, 0 failures). Inner widths are always pinned.
- For `c = k`: needs `a^k <= N`, and `a^k <= N` **iff** `b = a-1` and `k >= 3`
  (14,105 cases, 0 failures) — **exactly Proposition 'beat'**.

So for `b <= a-2` the core-width constraint is vacuous, the core can grow, and
the shape deforms; at `b = a-1` it bites and every width is pinned. The
orchestrator's rigidity and my Proposition 'beat' are the same statement.
Verified on all 9 points: `B7-active == (b=a-1 and k>=3) == (unique feasible
vector)`, 0 mismatches.

**What the two-sidedness is for.** The offending pair must consist of *units*.
Since `a | N` and `a | c_i` (2,152 points, 0 failures), the interval endpoints
`c_{i-1}+1` and `N-c_i+1` are `= 1 mod a`, hence units. Widening a shell exposes
the bad unit pair in its **left** interval; narrowing a cut exposes one in the
**right** interval of the next shell (the left one would begin at `c_i = 0 mod a`,
a non-unit, and produce no monochromatic pair). Both directions are refuted only
because the shells are two-sided. This is now Remark 'rigid' in the paper.

**Not proved.** The orchestrator's `feasible @ N+1 = 0` — that the shell *shape*
cannot be stretched past `N_shell` — is an upper-bound-flavoured claim. I
reproduced it at 6 points but did **not** prove it; it is not in the paper as a
theorem, and Theorem 1 does not cover it. Flagged as the natural next result.
It is also shape-local, not global: at `(3,2,5)` the brief records a
solution-free 5-colouring of `[1,350]` while `N_shell = 318`.

## 8. Files

| file | what |
|---|---|
| `proof.tex` / `proof.pdf` | the paper (8 pp, amsart, compiles clean, 0 errors, 0 undefined refs) |
| `LOG.md` | append-only lab notebook: failed attempts, decisions, verbatim outputs, corrections |
| `shell.py` | definitions only, transcribed from the brief; no claims |
| `verify_bruteforce.py` | exhaustive search for monochromatic solutions |
| `verify_lemmas.py` | per-lemma stress tests incl. the negative control |
| `verify_casetree.py` | case-tree exhaustiveness + per-branch audit |
| `verify_theorem2.py` | defect family; also the refutation of the brief's `k>=4` claim |
| `compare_bounds.py` | shell vs `a^k`; Proposition 'beat' pivots |
| `verify_rigidity.py` | cut-vector enumeration; which branch refutes each perturbation |
| `run_all.sh` | runs all of the above; exit 0 |
