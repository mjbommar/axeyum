# Route B lab notebook — append-only

Machine: 4 cores (`nproc` = 4), three agents sharing it. **All wall times in
this log are upper bounds on the true single-tenant cost**; the box was
contended for the whole session (`uptime` load average 1.74 at 19:07).

Convention: entries are appended with a `date -Is` stamp. Corrections are
appended as new entries, never edited into old ones.

---

## 2026-08-12T19:07:10-04:00 — notebook opened (retroactive preamble)

The notebook requirement arrived while the B1 build was running. Everything
below this heading up to the next `date -Is` stamp is a retroactive record of
work already done in this session, flagged as such. Everything after is
recorded live.

### Retroactive: what was done before the notebook existed (18:58–19:07)

**Step 1 — locate the precedent.** The brief claims the solution-form lemma
was discharged unbounded over ℤ. Searched the repo:

```sh
grep -rn "solution.form\|solution_form\|solution-form" --include=*.rs \
  --include=*.py --include=*.md --include=*.smt2 --include=*.txt .
```

One hit only:

```
docs/plan/claim-ledger-and-rado-frontier-2026-08-12.md:260:   solution-form lemma is separately machine-proved, bounded and unbounded
```

So the artefact is not in the repo. Found it in the session scratchpad at
`scratchpad/multilayer/` — a standalone cargo crate depending on the axeyum
crates by path. The relevant binary is
`multilayer/src/bin/layer2_lia.rs`, mode `param`, section "2b. The
parameterisation lemma".

**Step 2 — read what was actually posed.** `layer2_lia.rs:150`
`fn parameterisation(a, b, n, bounded)`. Confirmed by reading the source that
when `bounded == false` the function pushes **no** `in_range` constraints — the
three variables are plain `ar.int_var("x"/"y"/"z")` of `Sort::Int`, and the only
assertions are the equation and the negated claim. So the *encoding* is
genuinely unbounded. Whether the *solver* treats it as unbounded is a separate
question and is the whole point of B1; see below.

**Step 3 — reproduce.** Ran the already-built binary:

```sh
cd .../scratchpad/multilayer && time ./target/release/layer2_lia param
```

Output (verbatim, tail):

```
2b. PARAMETERISATION LEMMA  (x-y = b't, z = a't)
  a=1 b=1 (a'=1 b'=1) over [1,30]^3       : a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=2 b=3 (a'=2 b'=3) over [1,30]^3       : a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=3 b=2 (a'=3 b'=2) over [1,30]^3       : a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=4 b=3 (a'=4 b'=3) over [1,30]^3       : a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=6 b=4 (a'=3 b'=2) over [1,30]^3       : a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=6 b=9 (a'=2 b'=3) over [1,30]^3       : a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  -- unbounded (all of Z), expected to be harder --
  a=1 b=1 (a'=1 b'=1) over Z^3 (unbounded): a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=2 b=3 (a'=2 b'=3) over Z^3 (unbounded): a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)
  a=6 b=4 (a'=3 b'=2) over Z^3 (unbounded): a'|z -> unsat                  (0.00s)   x-y=b'(z/a') -> unsat                  (0.00s)

real	0m0.023s
```

Reproduces exactly. **23 milliseconds for all 18 queries.**

### SUSPICION LOGGED AT 19:07, BEFORE ANY FURTHER MEASUREMENT

Two things smell wrong and I am recording them now so the record shows the
suspicion preceded the check:

1. **The unbounded queries are not slower than the bounded ones.** Both print
   `0.00s`. The source's own banner says "expected to be harder". A genuine
   ℤ-refutation of a divisibility fact is cheap if done by a gcd/congruence
   argument, so this is *consistent* with a real proof — but it is equally
   consistent with a route that decides the query by some shortcut that has
   nothing to do with ℤ.
2. **The precedent has NO unbounded false-variant control.** Reading
   `fn parameterisation_control` (`layer2_lia.rs:288`), every control is run at
   `n = 30`, i.e. **bounded**. `main` calls `parameterisation_control(a, b, 30)`
   only. So the claim "unsat unbounded over ℤ" rests on a gate that was never
   shown to be capable of returning `sat` in the unbounded configuration. Per
   this repo's own rule (a gate that never fires proves nothing), the unbounded
   result as it stands is **not yet evidence**. This is the single most
   important gap for B1 and it is what my `b1_audit` binary is built to close.

**Step 4 — build the audit harness.** Created `route-b/` as a standalone crate
(`Cargo.toml` depends on `axeyum-ir`, `axeyum-cas`, `axeyum-solver` with
`features = ["full"]`, by path, `[workspace]` empty table so it does not join
the main workspace). Wrote `route-b/src/bin/b1_audit.rs`. It differs from the
precedent in three ways that matter:

- uses `check_auto_explained` instead of `check_auto`, so the **dispatch route
  trace** is printed for every query — this answers "which route decided it,
  and was that route a finite-domain one";
- adds FALSE-variant controls **in the unbounded configuration**;
- adds anti-bounding controls: satisfiable unbounded queries whose only
  solutions have |z| ≈ 10^18, and ones forcing `z < 0 ∧ x < 0`. A silently
  bounded abstraction would return `unsat` or `unknown` on these.

Build:

```sh
cd route-b && export CARGO_BUILD_JOBS=1 \
  && export CARGO_TARGET_DIR=$PWD/target \
  && cargo build --release --bin b1_audit
```

```
    Finished `release` profile [optimized] target(s) in 5m 59s
real	5m59.409s
```

(Cold build of the whole axeyum dependency chain at `-j1` on a contended box.)

Not yet run. Next entry records the run.

---

## 2026-08-12T19:08:30-04:00 — B1 audit run. The precedent SURVIVES the audit.

```sh
cd route-b && ./target/release/b1_audit | tee b1_audit.out
real	0m0.014s
```

Full output in `route-b/b1_audit.out` (20 queries over 5 parameter pairs
(2,3),(3,2),(4,3),(6,4),(5,3)). Tally:

```
=== MISMATCH COUNT ===
0
=== verdict tally ===
     14 expect=sat        OK
      6 expect=unsat      OK
```

**Finding 1 — the deciding route is `lia-dpll`, not a bounded one.** Verbatim
trace for the headline query:

```
  TRUE  claim1: a(x-y)=bz /\ NOT(2 | z)                      -> unsat                        (0.002s)  expect=unsat      OK
      route| probe: fragment {int}
      route| dl-online: declined (not-applicable)
      route| lia-simplex: declined (unsupported)
      route| lia-dpll: decided unsat
```

`lia-dpll` is `crates/axeyum-solver/src/dpll_lia.rs`, whose module doc reads
"Boolean-structured linear arithmetic (`QF_LIA` …) by lazy-SMT / DPLL(T) over
the **exact-rational** simplices" and "A round budget bounds the search
(`unknown`, never wrong)". So the search is bounded, the *domain* is not: the
budget can only cost completeness (`unknown`), never soundness. No
bit-blasting, no finite-domain split, no bit-vector route appears in any trace.

**Finding 2 — the false-variant controls FIRE in the unbounded configuration.**
This is the gap in the precedent (which only ran controls at `n = 30`). Three
deliberately-false variants of the same query shape, unbounded:

```
  FALSE ctrlA: a(x-y)=bz /\ NOT(3 | z)                       -> sat    ... model| x=Some(6) y=Some(0) z=Some(4)
  FALSE ctrlB: ... /\ 2|z /\ x-y != 3*(z/2)+1                -> sat    ... model| x=Some(0) y=Some(0) z=Some(0)
  FALSE ctrlC: a(x-y)=bz /\ NOT(3 | z)                       -> sat    ... model| x=Some(6) y=Some(0) z=Some(4)
```

Hand-replay of ctrlA (a=2,b=3): 2(6−0) = 12 = 3·4 ✓, and 3∤4 ✓. A genuine
counterexample to the false claim. So the gate is not vacuous — it returns
`sat` when the claim is false and `unsat` when it is true, in the *same*
unbounded configuration.

**Finding 3 — anti-bounding controls pass; witnesses exceed any plausible box.**

```
  SAT   big: z=2*(1000000000000000000), x-y=3*(1000000000000000000), y=1 -> sat
      route| int-box-eval: decided sat
      model| x=Some(3000000000000000001) y=Some(1) z=Some(2000000000000000000)
  SAT   big: z=2*(-1000000000000000000), ...                             -> sat
      model| x=Some(-2999999999999999999) y=Some(1) z=Some(-2000000000000000000)
  SAT   negatives: a(x-y)=bz /\ z<0 /\ x<0                   -> sat
      model| x=Some(-1) y=Some(2) z=Some(-2)
```

Witnesses at ±3·10^18 and genuinely negative solutions. A silently-bounded or
wrapping abstraction could not produce these. Note the route for the big ones is
`int-box-eval`, a different route from the lemma's — worth noting but harmless
here (these are the controls, not the theorem).

**Verdict on B1: the precedent is real. It is NOT bit-vector-bounded.** The
paper's claim stands. Caveat recorded: I have not yet stressed `lia-dpll` on a
SAT query whose witness must be *searched for* rather than pinned by an
equation. Doing that next (`b1_hard`), because "returns sat only when the
answer is handed to it" would be a real weakness.

Suspicion from the 19:07 entry item 1 (unbounded no slower than bounded)
RESOLVED as benign: a congruence/gcd refutation genuinely is O(1) work for
DPLL(T)+simplex; the bounded version is not doing more work, it is doing the
same work with three redundant range atoms.
Suspicion item 2 (no unbounded control) RESOLVED by adding the controls above.

---

## 2026-08-12T19:14:00-04:00 — B2/B3 groundwork by enumeration (no solver)

Before encoding anything I re-derived the construction from the brief in
`route-b/shell_groundwork.py` and enumerated it. Full output in
`route-b/groundwork.out`. Command:

```sh
cd route-b && python3 shell_groundwork.py | tee groundwork.out
```

Three results that DIRECTLY shape the encodings:

**G2 — gcd(a,b)=1 cannot be dropped.** The brief invited me to check whether the
coprimality hypothesis could be avoided. It cannot:

```
  k=2 b<a gcd=1: 21/21 solution-free
  k=2 b<a gcd>1: 0/7 solution-free   DEFECTS: [(4, 2), (6, 2), (6, 3), (6, 4), (8, 2), (8, 4), (8, 6)]
  k=3 b<a gcd=1: 21/21 solution-free
  k=3 b<a gcd>1: 0/7 solution-free   DEFECTS: [(4, 2), (6, 2), (6, 3), (6, 4), (8, 2), (8, 4), (8, 6)]
```

Every single non-coprime `b<a` pair in range is defective, at both k. So the
gcd hypothesis is load-bearing and must appear in the encoding. **Decision:
encode gcd(a,b)=1 as Bezout, `∃u,v. a·u + b·v = 1`.** This is the right
direction: the theorem is posed as a *refutation* (an existential query), so an
existential hypothesis is just two more free variables — no quantifier
alternation, stays in QF_NIA. This is the single design choice that makes B3
tractable at all.

**G3 — the b=a+1 counterexample family, closed forms.** Verified a=2..11:

```
  a   b       N   x=ab^2+1   z=a^2 b  chi(x)  chi(1)  chi(z)   N-ab+1  in range
  2   3      24         19        12       2       2       2       19      True   eq=True mono=True  x==N-ab+1? True
  3   4      60         49        36       2       2       2       49      True   eq=True mono=True  x==N-ab+1? True
 ...
 11  12    1716       1585      1452       2       2       2     1585      True   eq=True mono=True  x==N-ab+1? True
```

with (asserted exactly for a=2..11)

```
    N        = 2ab + a^2 b = a(a+1)(a+2) = a^3+3a^2+2a
    x        = a b^2 + 1   = a(a+1)^2+1  = a^3+2a^2+a+1
    N-ab+1   = a^3+2a^2+a+1   == x   <-- x is EXACTLY the left endpoint of the
                                          right-hand shell
```

That `x = N − ab + 1` coincidence is the reason the family works, and it turns
B2 from "an identity" into a full theorem: not just `a(x−y)=bz`, but *in range
and monochromatic*, for all a.

**G4 — the k=2 refutation needs far less than I feared.** Worked the case
analysis by hand and cross-checked by brute force (`k=2, all coprime b<a with
2<=a<=9: NO monochromatic solution. OK`). Then noticed something the brief did
not claim: at k=2 the enumeration shows **every coprime pair is solution-free,
including b > a** — look at the k=2 rows, `(2,3) (2,5) (2,7) (3,4) (3,5) (3,7)
(3,8) (4,5) (4,7) (5,6) (5,7) (5,8) (6,7) (7,8)` are all FREE. So at k=2 the
`b<a` hypothesis appears unnecessary. Re-derived the proof and it is uniform:

    z = a·t ≤ N = a·b  ⇒  t ≤ b.
    CASE all-colour-1: a|x ∧ a|y ⇒ a | (x−y) = b·t ⇒ (Bezout) a|t ⇒ t = a·w
        ⇒ x−y = b·t = a·b·w = N·w ≥ N.  But x ≤ N and y ≥ 1 so x−y ≤ N−1.  ⊥
    CASE all-colour-2: a|z always, so colour 2 forces a²|z ⇒ a|t ⇒ t = a·q
        ⇒ x−y = b·t = N·q ≥ N > N−1 ≥ x−y.  ⊥

Both branches end at the *same* inequality and **neither uses b < a**. So I will
attempt the STRONGER k=2 theorem (no b<a hypothesis) and report which version
axeyum actually discharges.

**Encoding trick decided here (important for the paper).** Both `a | j` and its
negation `a ∤ j` must appear, and a negated divisibility is normally a universal
(`∀p. j ≠ a·p`), which would push the query out of QF. Avoided by witnessing the
remainder:

    a | j    ⟺  ∃p.       j = a·p
    a ∤ j    ⟺  ∃s,r.     j = a·s + r  ∧  1 ≤ r ≤ a−1

Both existential. Combined with Bezout for gcd, the ENTIRE colouring predicate
becomes quantifier-free NIA with extra free variables. No quantifier alternation
anywhere in route B.

**Control design fixed here, before running anything.** For k=2 the sharp
false-variant is *drop the Bezout hypothesis* — G2 says it must then be
satisfiable. Hand-checked a witness in advance so I can tell a real `sat` from a
lucky one: (a,b)=(4,2), t=2 ⇒ z=8, x−y=4, x=8, y=4; 4(8−4)=16=2·8 ✓; N=8;
v_4(4)=1, v_4(8)=1 so χ(8)=χ(4)=1 — all colour 1, a genuine defect of exactly
the parameterised shape. For k=3 the sharp false-variant is *drop b<a* (G1 shows
every coprime b>a row defects at k=3).

---

## 2026-08-12T19:18:10-04:00 — B2 first run. 17/20 matched, 3 informative FAILURES.

```sh
cd route-b && ./target/release/b2_family | tee b2_family.out
real	1m21.934s     # 81s of which 60s is ONE query's timeout; contended box
```

Full output in `route-b/b2_family.out`. Tally:

```
  [B2] matched=17 mismatched=3
      MISMATCH: iii.y1 -> unknown(Timeout)
      MISMATCH: iii.z2 -> unknown(Incomplete)
      MISMATCH: iii.x1 -> unknown(Incomplete)
```

### What WORKED (all with `a` a free unbounded Int, nothing sampled)

```
  TRUE  (i)  refute: a(x-y) != b*z                               unsat    0.00s
      via | int-real-relax: decided unsat
  TRUE  (i') refute: general b, a(x-y) != b*z                    unsat    0.00s
  TRUE  (ii) refute: NOT(x <= N)                                 unsat    0.00s
  TRUE  (ii) refute: NOT(z <= N)                                 unsat    0.00s
  TRUE  (ii) refute: NOT(x >= 1)                                 unsat    0.00s
  TRUE  (ii) refute: NOT(z >= 1)                                 unsat    0.00s
  TRUE  (iii.y2) refute: a*b < 1                                 unsat    0.00s
  TRUE  (iii.z1) refute: z != a^2*b                              unsat    0.00s
      via | term-identity-refuter: decided unsat
  TRUE  (iii.x2) refute: x < N-ab+1                              unsat    0.00s
  TRUE  (iii.x3) refute: x != N-ab+1                             unsat    0.00s
  TRUE  (iv) refute: NOT(identity /\ range /\ x in right shell)  unsat    0.14s
      via | int-real-relax: decided unsat
```

The deciding route for the polynomial facts is `int-real-relax`. Degree-3
polynomial identities and inequalities in one and two free integer variables are
discharged in milliseconds. `(iv)` is the whole arithmetic half of the theorem
as ONE query and it goes through.

**Every one of these is paired with a control that came back `sat`:**

```
  FALSE ctrl(i):     refute: a(x-y) != b*(z+1)          sat  0.01s  wit | a=2
  FALSE ctrl(ii):    refute: z < x                      sat  0.00s  wit | a=2
  FALSE ctrl(iii.z): refute: a^2 | z                    sat  0.02s  wit | a=2 pz=3
  FALSE ctrl(iii.x): refute: x != N-ab                  sat  0.00s  wit | a=2
  FALSE ctrl(iv):    conjunction + false conjunct z>=x  sat  0.01s  wit | a=2
```

`ctrl(iii.z)` returning `wit | a=2 pz=3` is a *correct* witness: a=2, b=3,
z = a^2 b = 12 = a^2 * 3, so pz = b = 3. The controls are not just firing, they
are firing with meaningful models.

### ENCODING FAILURE 1 (my bug, deliberately kept in the run)

I originally posed "a^2 | z" as `NOT(divides(a^2, z))` where `divides` witnesses
the quotient with a FREE variable `pz`. That is wrong: `pz` is implicitly
EXISTENTIAL at query level, so `not(z = a^2*pz)` says "there exists pz with
z != a^2*pz" — trivially satisfiable, and no evidence for anything. I caught
this by inspection BEFORE the first run and kept it in as a live demonstration:

```
  BUG   (iii.z1-bad) refute: NOT(a^2|z) -- negated existential   sat  0.00s
      wit | a=2 pz=1
```

Exactly as predicted (a=2, pz=1: z=12 != 4·1). **Rule extracted: a witnessed
existential predicate may only appear POSITIVELY in a refutation query.** Its
negation must be certified a different way.

### ENCODING FAILURE 2 (axeyum's reach — the real finding)

All three mismatches are the same shape: **refuting a divisibility to establish
a NON-divisibility.**

```
  TRUE  (iii.y1) refute: a | 1     unknown(Timeout)      60.00s
      via | int-blast-ladder: declined (budget: combined-theory timeout after scalar backend)
  TRUE  (iii.z2) refute: a^3 | z   unknown(Incomplete)   20.81s
      via | int-blast-ladder: declined (incomplete: no model within the bounded integer width 32; widen the bound)
  TRUE  (iii.x1) refute: a | x     unknown(Incomplete)    0.92s
      via | int-blast-ladder: declined (incomplete: no model within the bounded integer width 32; widen the bound)
```

`∃a,p. a ≥ 2 ∧ a·p = 1` — a fact a first-year student closes in one line —
routes to `int-blast-ladder`, which bit-blasts integers at a bounded width,
finds no model within width 32, and correctly declines as **`unknown`, never a
wrong `unsat`**. Soundness is intact; this is a *completeness* limit, and it is
the sharpest boundary of axeyum's arithmetic reach I have hit so far. Recorded
as a product finding.

### The fix, and why it is not a cheat

The three failures share a root cause that is MY encoding's fault, not only
axeyum's: I was trying to establish a *positive existential* fact
(`a ∤ j`, which by the remainder characterisation means "∃s,r. j = a·s+r ∧
1 ≤ r ≤ a−1") by *refuting its negation*, which is the hard direction. A
positive existential should be certified by **exhibiting the witness**, exactly
as `(iii.z1)` already does (witness p = b, decided by `term-identity-refuter` in
0.00s after the same claim in the wrong direction had failed).

Witnesses, all forced and none free-chosen:
  a ∤ 1        : s = 0, r = 1.  Need 1 ≤ 1 ≤ a−1, i.e. a ≥ 2.  LINEAR.
  a ∤ a·b²+1   : s = b², r = 1. Need 1 ≤ 1 ≤ a−1, i.e. a ≥ 2.  LINEAR.
  a³ ∤ a²(a+1) : z = a³ + a², so s = 1, r = a². Need 1 ≤ a² ≤ a³−1,
                 i.e. a²(a−1) ≥ 1.  Degree 3, one variable.

This is not weakening the theorem: `a ∤ j` is *defined* by the existence of such
an (s,r), so producing the witness and proving its side conditions IS the proof.
Rewriting `b2_family.rs` accordingly and re-running. Both the failed and the
fixed encodings stay in the file so the run shows both.

---

## 2026-08-12T19:20:00-04:00 — B2 re-run with witness-direction encodings. B2 DONE.

```sh
cd route-b && cargo build --release --bin b2_family && ./target/release/b2_family | tee b2_family2.out
```

```
(v) NON-DIVISIBILITY VIA EXPLICIT REMAINDER WITNESSES
  TRUE  (v.y1) a nmid 1   witness s=0,r=1                        unsat    0.00s  want=unsat      OK
      via | lia-dpll: decided unsat
  TRUE  (v.x1) a nmid x   witness s=b^2,r=1                      unsat    0.00s  want=unsat      OK
      via | dl-online: decided unsat
  TRUE  (v.z2) a^3 nmid z witness s=1,r=a^2                      unsat    0.00s  want=unsat      OK
      via | int-real-relax: decided unsat
  FALSE ctrl(v): bogus 'a^2 nmid z' witness r=a^2 out of range   sat      0.01s  want=sat        OK
      via | nia-linearize: decided sat

  [B2] matched=21 mismatched=3
      MISMATCH: iii.y1 -> unknown(Timeout)      <- the hard-direction encodings,
      MISMATCH: iii.z2 -> unknown(Incomplete)      deliberately retained
      MISMATCH: iii.x1 -> unknown(Incomplete)
```

All three facts that were `unknown` in the refute-the-divisibility direction are
`unsat` in **0.00 s** in the exhibit-the-witness direction. The three remaining
"mismatches" are the OLD encodings, kept in the file on purpose as the record of
where the tool's reach ends. **B2 is complete.**

---

## 2026-08-12T19:33:00-04:00 — B3 k=2, attempt 1 (monolithic). FAILS, soundly.

```sh
cd route-b && ./target/release/b3_k2 | tee b3_k2.out
real	15m51.578s     # contended box; 8 queries hit their 120s budget
```

```
  [B3 k=2] matched=3 mismatched=9
      MISMATCH: A1 -> unknown(Incomplete)     MISMATCH: B1 -> unknown(Timeout)
      MISMATCH: A2 -> unknown(Incomplete)     MISMATCH: B2 -> unknown(Timeout)
      MISMATCH: A2f -> unknown(Incomplete)    MISMATCH: B2f -> unknown(Timeout)
      MISMATCH: A3 -> unknown(Incomplete)     MISMATCH: B3 -> unknown(Timeout)
                                              MISMATCH: C2 -> unknown(Timeout)
```

Every theorem attempt routes to `int-blast-ladder` and returns `unknown`:

```
      via | int-blast-ladder: declined (incomplete: bounded integer model overflowed at width 32 (assertion #151 is false over exact semantics); widen the bound)
      via | int-blast-ladder: declined (budget: integer bit-blast width ladder: wall-clock timeout reached)
```

**No wrong answer anywhere** — the failure mode is `unknown`, exactly as
ADR-discipline requires. But no theorem either.

The controls DID fire, and informatively:

```
  FALSE C1 case1, NO coprimality, b<a       sat   0.80s   wit | a=6 b=3 t=2 y=6 px=2 py=1
  FALSE C3 FULL single query, NO coprimality, b<a   sat  40.25s
      wit | a=4 b=2 t=2 y=4 c1dx=2 c1nx_s=0 c1nx_r=8 ...
  FALSE C4 case1, NO coprimality, no b<a    sat   0.15s   wit | a=2 b=2 t=1 y=2 px=2 py=1
```

C3's witness is `a=4, b=2, t=2, y=4` — **exactly the (4,2) defect I predicted by
hand at 19:14 before running anything** (x = y+bt = 8, z = at = 8, N = ab = 8,
4·(8−4) = 16 = 2·8, χ(8)=χ(4)=1). The fully faithful colouring encoding
reproduces the enumerated defect. That is strong evidence the ENCODING is
right and only the solver's reach is short.

---

## 2026-08-12T19:45:00-04:00 — B3 k=2, attempt 2 (chain, full hypotheses). FAILS.

```sh
cd route-b && ./target/release/b3_k2_chain | tee b3_k2_chain.out
real	14m17.754s
```

Only T1, T3, cT3, cTAIL matched. **And I caught a methodological error of my own
here, which is the important part of this entry:**

```
  TRUE  T1: t=a*w, t>=1, a>=2 |= w>=1       unsat                 0.30s  OK
  FALSE cT1: same but claim w>=2 [FALSE]    unknown(Incomplete)  78.14s  *** MISMATCH ***
```

T1 came back `unsat` but **its control did not come back `sat`** — so by this
project's own rule that entry was NOT evidence. Worse, on inspection the control
was not merely unlucky, it was **wrong**: I built cT1 on the FULL hypothesis set
H, and H ∧ (t = a·w) is contradictory (that is exactly what TAIL asserts), so
every "control" derived from it is unsatisfiable by construction. A control that
cannot possibly return `sat` is not a control. Same defect in cT2 and cC2.1.

Root cause of BOTH problems (the timeouts and the dead controls): I dragged all
~10 of H's nonlinear atoms into every link, when each link needs three or four.
Fix: pose every lemma with **minimal hypotheses**, as a universally valid
implication over ℤ, then instantiate.

---

## 2026-08-12T19:47:30-04:00 — B3 k=2, attempt 3 (minimal hypotheses). 4 of 6 land.

```sh
cd route-b && ./target/release/b3_k2_min | tee b3_k2_min.out
real	2m0.106s
```

```
  TRUE  L1  a>=2, a*t = a^2*q |= t = a*q              unsat  0.00s  via int-real-relax
  FALSE cL1 claim t = a*q+1                           sat    0.00s  wit | a=2 t=0 q=0
  TRUE  L2  a>=2, t>=1, t = a*w |= w >= 1             unsat  0.00s  via int-real-relax
  FALSE cL2 claim w >= 2                              sat    0.00s  wit | a=2 t=2 w=1
  TRUE  L3  ... |= b*t >= a*b                         unknown(Timeout)  60.01s  *** MISMATCH ***
  FALSE cL3 claim b*t > a*b strictly                  sat    0.03s  wit | a=2 b=1 t=2 w=1
  TRUE  L4  y>=1,x=y+P,P>=M,x<=M |= false             unsat  0.00s  via lia-simplex
  FALSE cL4 weakened to P >= M-1                      sat    0.00s  wit | y=1 P=0 M=1
  TRUE  L5  a|x,a|y |= bt = a*(px-py)                 unsat  0.00s  via int-real-relax
  FALSE cL5 claim bt = a*(px-py)+1                    sat    0.01s
  TRUE  L6  Bezout |= t = a*(t*u+v*d)                 unknown(Timeout)  60.00s  *** MISMATCH ***
  FALSE cL6 witness perturbed by +1                   sat    0.03s
  FALSE cL6' no Bezout hypothesis                     sat    0.02s  wit | a=4 b=2 t=-2 u=-1 v=4 d=-1

  [B3 k=2 minimal lemmas] matched=11 mismatched=2
```

Minimal hypotheses turn 0.30 s + timeouts into 0.00 s. L1, L2, L4, L5 proved,
**each with a control that fired**. L3 (degree-3 monotonicity) and L6 (the
Bezout identity) still time out. `cL6'` is the sharp necessity check: drop the
Bezout hypothesis and the same query is satisfiable — so the gcd assumption is
load-bearing in the machine proof exactly as it is in the mathematics.

---

## 2026-08-12T19:50:00-04:00 — B3 k=2, attempt 4 (micro-lemmas). ALL LAND.

L3 and L6 split into steps that are each a pure ring identity or a
two-variable inequality:

```sh
cd route-b && ./target/release/b3_k2_micro | tee b3_k2_micro.out
real	0m0.057s      # sixteen queries, 57 milliseconds total
```

```
  TRUE  M5: a>=2, b>=1 |= a*b >= 1                               unsat  0.00s
  FALSE cM5: claim a*b >= 3                                      sat    0.00s  wit | a=2 b=1
  TRUE  M7: b*(a*w) = (a*b)*w  [ring identity]                   unsat  0.00s
  FALSE cM7: b*(a*w) = (a*b)*w + 1                               sat    0.00s
  TRUE  M6: M>=1, w>=1 |= M*w >= M                               unsat  0.00s
  FALSE cM6: claim M*w > M strictly                              sat    0.00s  wit | M=1 w=1
  TRUE  M2: s=1 |= t*s = t                                       unsat  0.00s
  FALSE cM2: s=2 |= t*s = t                                      sat    0.00s  wit | s=2 t=-1
  TRUE  M1: p=r |= v*p = v*r  [congruence]                       unsat  0.00s
  FALSE cM1: p=r+1 |= v*p = v*r                                  sat    0.00s  wit | p=2 r=1 v=1
  TRUE  M1': p=r |= p*v = r*v  [orientation used]                unsat  0.00s
  FALSE cM1': p=r+1 |= p*v = r*v                                 sat    0.00s
  TRUE  M3: t*(a*u+b*v) = a*(t*u) + (b*t)*v  [identity]          unsat  0.00s
  FALSE cM3: same identity + 1                                   sat    0.02s
  TRUE  M4: a*(t*u) + (a*d)*v = a*(t*u + d*v)  [identity]        unsat  0.00s
  FALSE cM4: same identity + 1                                   sat    0.02s

  [B3 k=2 micro-lemmas] matched=16 mismatched=0
```

**16/16, every `unsat` with a firing control, 57 ms total.** M1' was added after
I noticed the chain consumes `(b*t)*v` (from M3) and `(a*d)*v` (into M4) while
M1 as first written proves the `v*p = v*r` orientation. Rather than assume
commutativity silently, M1' proves the orientation actually used.

**k = 2 is now fully proved.** Composition written out in REPORT.md.

### Honest note on where the theorem's difficulty actually lives

The 57 ms is not the cost of the theorem. The cost was four attempts and ~32
minutes of solver time discovering *which decomposition axeyum can take*. The
mathematical content (the case analysis, the Bezout witness, the choice to drop
the a²∤ conjuncts) was supplied by me; axeyum checked each step. That is a real
and useful division of labour, but it is not "axeyum proved the theorem".

---

## 2026-08-12T19:51:00-04:00 — independent wide cross-check of the PROVED claim

A machine proof that disagrees with enumeration means a bug. Checked the exact
statement claimed, by full scan over all (x,y,z) — **not** via the
parameterisation, so it does not even assume the B1 solution-form lemma:

```sh
cd route-b && python3 verify_k2_wide.py
```

```
coprime (a,b) pairs tested (2<=a<=30, 1<=b<=60, N<=1200): 973
NO monochromatic solution found in any tested pair.
=> consistent with the machine-proved k=2 theorem (incl. b>a).

NON-coprime pairs (2<=a,b<=12): 53/53 have a monochromatic solution
=> the gcd hypothesis is sharp; the proof MUST use it (and it does, via Bezout).
```

973 coprime pairs, zero counterexamples — including the `b > a` pairs, which the
brief never claimed and which my proof covers. 53/53 non-coprime pairs defective
— the hypothesis is not just used, it is exactly sharp.

---

## 2026-08-12T19:52:30-04:00 — bonus: the COLOUR-1 LEMMA holds for EVERY k

Noticed while writing the k=2 proof: colour 1 is `{j : v_a(j) = 1}` for every k
(the brief says so explicitly), so the all-colour-1 case mentions no N, no shell
cut, no k. It can be refuted once for all k.

```sh
cd route-b && ./target/release/b3_colour1 | tee b3_colour1.out
real	0m45.044s     # 45s of which is M8's single timeout
```

```
  TRUE  M8   M>=1, 1 <= M*c <= M-1 |= false      unknown(Timeout)  45.00s  *** MISMATCH ***
  FALSE cM8  window widened to 1 <= M*c <= M     sat    0.00s  wit | M=1 c=1
  TRUE  M10  a>=2 |= a^2 >= 1                    unsat  0.00s
  FALSE cM10 claim a^2 >= 5                      sat    0.00s  wit | a=2
  TRUE  M9   z=a*t, t=a*w |= z = a^2*w           unsat  0.00s
  FALSE cM9  claim z = a^2*w + 1                 sat    0.00s
  TRUE  M11  z=a^2*w, z=a^2*s+r |= r = a^2*(w-s) unsat  0.00s
  FALSE cM11 claim r = a^2*(w-s) + 1             sat    0.01s
  TRUE  ASM  a>=2, r=a^2(w-s), 1<=r<=a^2-1 |= false   unsat  0.01s  via nia-linearize
  FALSE cASM window widened to 1 <= r <= a^2          sat    0.01s  wit | a=2 w=1 s=0 r=4

  [B3 colour-1 lemma (all k)] matched=9 mismatched=1
```

**A genuinely surprising data point worth the paper's space:** `M8` in its
ABSTRACT form (`M` an opaque free variable) times out at 45 s, while `ASM` —
literally the same fact instantiated at `M := a²` with `a ≥ 2` — is decided
`unsat` in **0.01 s** by `nia-linearize`. Generalising a lemma made it *harder*,
not easier. The proof only ever needs the concrete form, so the chain is
complete; but the abstract-is-harder effect is a real characterisation of this
solver's arithmetic and I did not expect it.

`cASM` fires with `a=2 w=1 s=0 r=4`: widening the remainder window to include
a² = 4 admits r = 4, exactly the boundary case the real window excludes. The
control is testing precisely the load-bearing inequality.

---

## 2026-08-12T19:53:00-04:00 — k = 3: NOT ATTEMPTED IN CODE. Honest status.

I worked out the k=3 case analysis on paper (it is in REPORT.md) and did not
encode it. Reasons, recorded rather than dressed up:

- k=3 has three colours and two shell strata, so the monochromatic condition is
  a disjunction over roughly 10 leaf cases (colour 1: 1; colour 2: the 3×3
  stratum combinations that survive; colour 3: 4), each needing its own chain.
- Cases 2 and 3 both genuinely need `b < a` (unlike k=2), and both need new
  inequality lemmas of degree 3–4 in three variables — the exact shape that
  `int-blast-ladder` has failed on all session.
- The colour-1 case of k=3 IS proved, as a special case of the all-k colour-1
  lemma above.

So the honest k=3 status is: **1 of ~3 cases proved (colour 1, and it is proved
for every k), 2 cases not attempted.** I would rather report that than encode
ten cases at the end of a session and risk an unchecked composition error, which
is the failure mode this notebook exists to prevent.

---

## 2026-08-12T19:56:00-04:00 — closing note on the deliverable

`REPORT.md` could not be written: the harness blocks subagents from writing
report/summary/findings files, and instructed that the conclusions be returned
as the final response text instead. The report content was therefore delivered
to the orchestrator verbatim in the task response rather than as a file in this
directory. **This notebook (LOG.md) plus the `.out` files are the complete
primary evidence** and are self-sufficient — every claim in the report is
reproducible from the commands recorded here.

Final inventory of primary evidence in route-b/:
  b1_audit.out       20/20 matched   B1 precedent audit, route traces + controls
  b2_family2.out     21/3            B2 theorem (3 = retained failing encodings)
  b3_k2.out          3/9             B3 monolithic (all failures = unknown)
  b3_k2_chain.out    4/8             B3 chain w/ full hypotheses (failed)
  b3_k2_min.out      11/2            B3 minimal-hypothesis lemmas
  b3_k2_micro.out    16/0            B3 micro-lemmas — the completed k=2 proof
  b3_colour1.out     9/1             colour-1 lemma, all k
  groundwork.out                     enumeration, closed forms, case analysis
  verify_k2_wide.py                  973-pair independent cross-check
