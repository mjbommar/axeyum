use super::{
    BinderInfo, DIO_UNIT_MAX, ExprId, IntReconstructCtx, NameId, Op, ReconstructError, SymbolId,
    TermArena, TermId, TermNode, ZExpr, intlit_zexpr, lin_to_canon_gens, lin_to_zexpr,
};

// =============================================================================
// Integer-INEQUALITY infeasibility reconstruction (ADR-0042, the integer-cut
// payoff for the single-variable `c ≤ k·x ≤ d` shape).
// =============================================================================

/// The identity of the single integer "variable" an interval/equality atom is over.
///
/// Either a genuine integer [`SymbolId`] (`Σ … x …`) or an **opaque integer
/// application** `(f args)` keyed by its structurally-hashed [`TermId`] — the latter
/// lets the integer reconstructor treat a maximal non-arithmetic `Int`-sorted subterm
/// `(f c)` (an uninterpreted-function application) as a fresh opaque integer, exactly
/// as the conjunctive `QF_UFLIA` interpolant's congruence-free refutations require.
///
/// **Soundness of the opaque case.** An `(f args)` application is `Int`-sorted, so it
/// denotes *some* integer. Treating it as a fresh integer variable `y` GENERALIZES the
/// atom: the original (with `y := f(args)`) is a special case of the free-`y` system.
/// If the free-`y` system is integer-infeasible (which the discreteness reconstruction
/// proves over an opaque `Z` axiom — [`IntReconstructCtx::var_const_for`] already maps
/// every variable to one opaque `Z` constant), then a fortiori the original is. So an
/// opaque atom can only make UNSAT *harder* to witness, never spuriously UNSAT — and
/// the kernel gate (`infer` + `def_eq False`) remains the sole authority. The two
/// equal `TermId`s of a shared `(f c)` (structural hashing) compare equal here, so the
/// "same variable" detector checks hold for a shared opaque application.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AtomVar {
    /// A genuine integer symbol.
    Sym(SymbolId),
    /// An opaque integer application `(f args)`, keyed by its `TermId`.
    Opaque(TermId),
}

/// The detected single-variable integer-interval shape `c ≤ k·x ≤ d` with `k > 0`,
/// over one integer variable `x`, where **no multiple of `k` lies in `[c, d]`** (so
/// the system is integer-infeasible while its LP relaxation is feasible).
///
/// The discreteness reduction picks the integer `m` with `k·m < c` and `d < k·(m+1)`
/// (forced and unique when one exists): then `m < x < m+1`, i.e. `0 < x − m < 1`,
/// refuted by `no_int_between (x − m)`.
#[derive(Debug, Clone, Copy)]
struct IntInterval {
    /// The single integer variable (a symbol or an opaque application).
    var: AtomVar,
    /// The positive multiplier `k`.
    k: i128,
    /// The lower bound `c` (so `c ≤ k·x`).
    c: i128,
    /// The upper bound `d` (so `k·x ≤ d`).
    d: i128,
    /// The reduction offset `m` with `k·m < c` and `d < k·(m+1)`.
    m: i128,
}

/// A single-variable integer interval with **distinct** lower/upper multipliers:
/// `c ≤ k_lo·x` and `k_hi·x ≤ d` (`k_lo, k_hi > 0`, `k_lo ≠ k_hi`). Integer-infeasible
/// because the implied integer window `(m_lo, m_lo+1)` on `x` contains no integer,
/// while it is LP-feasible (genuinely needs an integer cut, not a Farkas/LRA close).
#[derive(Debug, Clone, Copy)]
struct IntIntervalDiff {
    var: AtomVar,
    /// Lower multiplier `k_lo > 0` (so `c ≤ k_lo·x`).
    k_lo: i128,
    c: i128,
    /// Upper multiplier `k_hi > 0` (so `k_hi·x ≤ d`).
    k_hi: i128,
    d: i128,
    /// Lower reduction offset: `m_lo = ⌊(c−1)/k_lo⌋`, the forced `lt m_lo x`.
    m_lo: i128,
    /// Upper reduction offset: `m_hi = ⌊d/k_hi⌋`, the forced `lt x (m_hi+1)`.
    m_hi: i128,
}

/// A single-variable integer **equality combined with a unit-multiplier bound** that is
/// **real-infeasible**: an equality `k·x = b` (`k > 0`) together with a bound `c ≤ x`
/// (lower) or `x ≤ c` (upper). The equality pins `x = b/k` (a rational); the bound
/// excludes it, so the conjunction is unsatisfiable already over ℝ — yet neither
/// dedicated integer reconstructor covers it: the Diophantine path ignores the inequality
/// and the equality alone (`k | b` permitted) is feasible, and the interval detectors
/// require **two** inequalities (no equality atom). The refutation scales the bound by
/// `k` and chains through the equality to a literal `b ⋈ k·c` contradiction.
///
/// Lower-bound infeasibility: `c ≤ x ⟹ k·c ≤ k·x = b`, contradicting `b < k·c`.
/// Upper-bound infeasibility: `x ≤ c ⟹ b = k·x ≤ k·c`, contradicting `k·c < b`.
#[derive(Debug, Clone, Copy)]
struct IntEqBound {
    var: AtomVar,
    /// The positive equality multiplier `k > 0` (oriented), so `k·x = b`.
    k: i128,
    /// The equality right-hand value `b`.
    b: i128,
    /// The bound constant `c`: `c ≤ x` when `lower`, else `x ≤ c`.
    c: i128,
    /// Whether the bound is a lower bound (`c ≤ x`) or an upper bound (`x ≤ c`).
    lower: bool,
}

/// A bound atom recovered from one assertion: `lower` ⇒ `k·x ≥ c` (i.e. `c ≤ k·x`),
/// `!lower` ⇒ `k·x ≤ d`. Both sides are normalized so the variable side is exactly
/// `k·x` (`k > 0`) and the bound is the integer constant on the other side.
#[derive(Debug, Clone, Copy)]
struct BoundAtom {
    var: AtomVar,
    k: i128,
    bound: i128,
    lower: bool,
}

/// Parse a linear integer term into `(coeff·var, constant)` for a **single** variable
/// (or a pure constant). The "variable" is either a genuine integer symbol or an
/// **opaque integer application** `(f args)` treated as a fresh opaque integer (see
/// [`AtomVar`] for the soundness of the opaque case). Returns `None` for
/// multi-variable / nonlinear / multi-term forms — this slice handles only the
/// single-variable interval shape.
fn single_var_linear(arena: &TermArena, t: TermId) -> Option<(Option<(AtomVar, i128)>, i128)> {
    match arena.node(t) {
        TermNode::IntConst(n) => Some((None, *n)),
        TermNode::Symbol(s) => Some((Some((AtomVar::Sym(*s), 1)), 0)),
        // A maximal non-arithmetic `Int`-sorted subterm `(f args)` is an opaque integer
        // variable, keyed by its (structurally-hashed) `TermId`.
        TermNode::App {
            op: Op::Apply(_), ..
        } => Some((Some((AtomVar::Opaque(t), 1)), 0)),
        TermNode::App { op, args } => match (op, &args[..]) {
            (Op::IntNeg, [x]) => {
                let (v, k) = single_var_linear(arena, *x)?;
                let v = match v {
                    Some((s, c)) => Some((s, c.checked_neg()?)),
                    None => None,
                };
                Some((v, k.checked_neg()?))
            }
            (Op::IntAdd | Op::IntSub, [x, y]) => {
                let sub = matches!(op, Op::IntSub);
                let (vx, kx) = single_var_linear(arena, *x)?;
                let (vy, ky) = single_var_linear(arena, *y)?;
                let ky = if sub { ky.checked_neg()? } else { ky };
                let var = match (vx, vy) {
                    (None, None) => None,
                    (Some(p), None) => Some(p),
                    (None, Some((s, c))) => Some((s, if sub { c.checked_neg()? } else { c })),
                    (Some((sx, cx)), Some((sy, cy))) => {
                        if sx != sy {
                            return None; // two distinct variables — out of scope
                        }
                        let cy = if sub { cy.checked_neg()? } else { cy };
                        Some((sx, cx.checked_add(cy)?))
                    }
                };
                Some((var, kx.checked_add(ky)?))
            }
            (Op::IntMul, [x, y]) => {
                let (vx, kx) = single_var_linear(arena, *x)?;
                let (vy, ky) = single_var_linear(arena, *y)?;
                match (vx, vy) {
                    (None, Some((s, c))) => {
                        Some((Some((s, c.checked_mul(kx)?)), ky.checked_mul(kx)?))
                    }
                    (Some((s, c)), None) => {
                        Some((Some((s, c.checked_mul(ky)?)), kx.checked_mul(ky)?))
                    }
                    (None, None) => Some((None, kx.checked_mul(ky)?)),
                    (Some(_), Some(_)) => None, // nonlinear (var·var)
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// Parse one assertion into a [`BoundAtom`] of the form `c ≤ k·x` or `k·x ≤ d`
/// (`k > 0`, single variable `x`). Recognizes `IntLe`/`IntGe`/`IntLt`/`IntGt` and
/// rewrites strict integer bounds to non-strict ones (`k·x > c ⟺ k·x ≥ c+1`,
/// `k·x < d ⟺ k·x ≤ d−1`). Returns `None` on any other shape.
fn parse_bound_atom(arena: &TermArena, t: TermId) -> Option<BoundAtom> {
    let TermNode::App { op, args } = arena.node(t) else {
        return None;
    };
    let [a, b] = &args[..] else {
        return None;
    };
    let (a, b) = (*a, *b);
    // Normalize each comparison `lhs ⋈ rhs` to `var_side ⋈' bound`, with `var_side`
    // the side carrying the variable. We collect `lhs − rhs = k·x + const ⋈ 0` and
    // read off the bound on `x` directly.
    let (la, ka) = single_var_linear(arena, a)?;
    let (lb, kb) = single_var_linear(arena, b)?;
    // Move everything to the left: `(lhs − rhs) ⋈ 0`, i.e. `kx·x + (ka − kb) ⋈ 0`.
    let (var, coeff) = match (la, lb) {
        (Some((s, c)), None) => (s, c),
        (None, Some((s, c))) => (s, c.checked_neg()?),
        (Some((sx, cx)), Some((sy, cy))) if sx == sy => (sx, cx.checked_sub(cy)?),
        _ => return None,
    };
    if coeff == 0 {
        return None;
    }
    let konst = ka.checked_sub(kb)?; // `coeff·x + konst ⋈ 0`

    // Direction of the relation as `coeff·x + konst R 0` with R ∈ {≤,<,≥,>}.
    // We rewrite to an oriented `k·x ⋈ bound` with `k > 0`.
    // op compares `a R b`, i.e. `(a − b) R 0`.
    let (mut k, mut konst, mut rel) = (coeff, konst, *op);
    // If coeff < 0, multiply the inequality by −1, flipping the relation.
    if k < 0 {
        k = k.checked_neg()?;
        konst = konst.checked_neg()?;
        rel = flip_rel(rel)?;
    }
    // Now `k·x + konst R 0`, k > 0. Rearrange to `k·x R (−konst)`.
    let rhs = konst.checked_neg()?;
    // Map to a lower/upper non-strict bound on `k·x`.
    // k·x ≤ rhs (Le), k·x < rhs (Lt ⇒ ≤ rhs−1), k·x ≥ rhs (Ge), k·x > rhs (Gt ⇒ ≥ rhs+1).
    let (bound, lower) = match rel {
        Op::IntLe => (rhs, false),
        Op::IntLt => (rhs.checked_sub(1)?, false),
        Op::IntGe => (rhs, true),
        Op::IntGt => (rhs.checked_add(1)?, true),
        _ => return None,
    };
    Some(BoundAtom {
        var,
        k,
        bound,
        lower,
    })
}

/// Flip a comparison `Op` under negation of both sides (`a R b` ⟺ `−a R' −b`).
fn flip_rel(op: Op) -> Option<Op> {
    Some(match op {
        Op::IntLe => Op::IntGe,
        Op::IntLt => Op::IntGt,
        Op::IntGe => Op::IntLe,
        Op::IntGt => Op::IntLt,
        _ => return None,
    })
}

/// Detect the canonical single-variable integer-interval shape `c ≤ k·x ≤ d` (k > 0,
/// one variable, LP-feasible `c ≤ d`, integer-infeasible: no multiple of `k` in
/// `[c, d]`). On a match returns the [`IntInterval`] with the forced reduction offset
/// `m` (`k·m < c` and `d < k·(m+1)`). `None` otherwise (declines — never fabricates).
fn detect_int_interval(arena: &TermArena, assertions: &[TermId]) -> Option<IntInterval> {
    let [a1, a2] = assertions else {
        return None;
    };
    let b1 = parse_bound_atom(arena, *a1)?;
    let b2 = parse_bound_atom(arena, *a2)?;
    if b1.var != b2.var || b1.lower == b2.lower {
        return None; // need exactly one lower and one upper bound on the same var
    }
    let (lo, hi) = if b1.lower { (b1, b2) } else { (b2, b1) };
    // Require the SAME positive multiplier on both sides for the clean `c ≤ k·x ≤ d`
    // reduction (a later slice may rescale to a common multiple).
    if lo.k != hi.k || lo.k <= 0 {
        return None;
    }
    let k = lo.k;
    let c = lo.bound; // c ≤ k·x
    let d = hi.bound; // k·x ≤ d
    if c > d {
        return None; // LP-infeasible — an LRA (not integer-cut) refutation; decline
    }
    // The infeasible-interval reduction: find integer m with k·m < c and d < k·(m+1).
    // m is forced: m = ⌊(c−1)/k⌋ (Euclidean, k > 0). Verify both strict bounds; if
    // they hold there is no multiple of k in [c, d] and we have a discreteness proof.
    let m = (c.checked_sub(1)?).div_euclid(k);
    let km = k.checked_mul(m)?;
    let km1 = k.checked_mul(m.checked_add(1)?)?;
    if !(km < c && d < km1) {
        return None; // some multiple of k lies in [c, d] — integer-feasible; decline
    }
    Some(IntInterval {
        var: b1.var,
        k,
        c,
        d,
        m,
    })
}

/// Detect the **different-multiplier** single-variable integer interval `c ≤ k_lo·x`
/// and `k_hi·x ≤ d` (`k_lo, k_hi > 0`, `k_lo ≠ k_hi`) that is LP-feasible yet
/// integer-infeasible: the lower bound forces `x ≥ m_lo+1` and the upper `x ≤ m_hi`
/// with `m_hi ≤ m_lo`, leaving the empty open window `(m_lo, m_lo+1)`. Returns the
/// [`IntIntervalDiff`] on a match, `None` otherwise (declines — never fabricates).
/// (The equal-multiplier case is owned by [`detect_int_interval`].)
fn detect_int_interval_diff_mult(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<IntIntervalDiff> {
    let [a1, a2] = assertions else {
        return None;
    };
    let b1 = parse_bound_atom(arena, *a1)?;
    let b2 = parse_bound_atom(arena, *a2)?;
    if b1.var != b2.var || b1.lower == b2.lower {
        return None; // need exactly one lower and one upper bound on the same var
    }
    let (lo, hi) = if b1.lower { (b1, b2) } else { (b2, b1) };
    if lo.k <= 0 || hi.k <= 0 || lo.k == hi.k {
        return None; // equal multiplier → detect_int_interval; non-positive → reject
    }
    let (k_lo, c) = (lo.k, lo.bound); // c ≤ k_lo·x
    let (k_hi, d) = (hi.k, hi.bound); // k_hi·x ≤ d
    // Lower forces x > m_lo with m_lo = ⌊(c−1)/k_lo⌋ (k_lo·m_lo < c ≤ k_lo·(m_lo+1)).
    let m_lo = (c.checked_sub(1)?).div_euclid(k_lo);
    if k_lo.checked_mul(m_lo)? >= c {
        return None;
    }
    // Upper forces x < m_hi+1 with m_hi = ⌊d/k_hi⌋ (k_hi·m_hi ≤ d < k_hi·(m_hi+1)).
    let m_hi = d.div_euclid(k_hi);
    if d >= k_hi.checked_mul(m_hi.checked_add(1)?)? {
        return None;
    }
    // Integer-infeasible iff the forced lower `x ≥ m_lo+1` exceeds the upper `x ≤ m_hi`,
    // i.e. m_hi ≤ m_lo (the open window `(m_lo, m_lo+1)` then holds no integer).
    if m_hi > m_lo {
        return None; // some integer lies in [m_lo+1, m_hi] — integer-feasible; decline
    }
    Some(IntIntervalDiff {
        var: lo.var,
        k_lo,
        c,
        k_hi,
        d,
        m_lo,
        m_hi,
    })
}

/// Parse one assertion into a single-variable integer equality `k·x = b` (`k > 0`).
/// Recognizes the generic [`Op::Eq`] over a single-variable linear term on one side and
/// a value on the other (in either orientation), normalizes so the variable coefficient
/// is positive, and returns `(var, k, b)`. Returns `None` on any other shape (multiple
/// variables, a zero coefficient, a non-equality, or an overflow) — never fabricates.
fn parse_int_equality(arena: &TermArena, t: TermId) -> Option<(AtomVar, i128, i128)> {
    let TermNode::App { op, args } = arena.node(t) else {
        return None;
    };
    if *op != Op::Eq {
        return None;
    }
    let [a, b] = &args[..] else {
        return None;
    };
    let (la, ka) = single_var_linear(arena, *a)?;
    let (lb, kb) = single_var_linear(arena, *b)?;
    // Move to `coeff·x + konst = 0`, i.e. `coeff·x = −konst`.
    let (var, coeff) = match (la, lb) {
        (Some((s, c)), None) => (s, c),
        (None, Some((s, c))) => (s, c.checked_neg()?),
        (Some((sx, cx)), Some((sy, cy))) if sx == sy => (sx, cx.checked_sub(cy)?),
        _ => return None, // two distinct variables or a pure-constant equality
    };
    if coeff == 0 {
        return None;
    }
    let konst = ka.checked_sub(kb)?; // `coeff·x + konst = 0`
    // Orient so the multiplier is positive (negate both coeff and the moved constant).
    let (k, rhs) = if coeff < 0 {
        (coeff.checked_neg()?, konst) // (−coeff)·x = konst
    } else {
        (coeff, konst.checked_neg()?) // coeff·x = −konst
    };
    Some((var, k, rhs))
}

/// Detect the single-variable integer **equality-and-unit-bound** refutation shape: an
/// equality `k·x = b` (`k > 0`) and a **unit-multiplier** bound (`c ≤ x` or `x ≤ c`) on
/// the same variable, whose conjunction is **real-infeasible** (the rational point
/// `x = b/k` violates the bound). Returns the [`IntEqBound`] on a match, `None` otherwise.
///
/// Real-infeasibility (`k > 0`, so multiplying the bound by `k` preserves direction):
/// a lower bound `c ≤ x` forces `k·c ≤ b`, so it is refuted iff `b < k·c`; an upper
/// bound `x ≤ c` forces `b ≤ k·c`, refuted iff `k·c < b`. Declines (never fabricates)
/// on any other shape, a non-unit bound multiplier, or a feasible conjunction.
fn detect_int_eq_bound(arena: &TermArena, assertions: &[TermId]) -> Option<IntEqBound> {
    let [a1, a2] = assertions else {
        return None; // exactly one equality + one bound
    };
    // Identify which assertion is the equality and which is the inequality (either order).
    let (eq_term, bound_term) = match (
        parse_int_equality(arena, *a1),
        parse_int_equality(arena, *a2),
    ) {
        (Some(_), None) => (*a1, *a2),
        (None, Some(_)) => (*a2, *a1),
        _ => return None, // zero or two equalities — out of this shape's scope
    };
    let (var, k, b) = parse_int_equality(arena, eq_term)?;
    if k <= 0 {
        return None;
    }
    let bound = parse_bound_atom(arena, bound_term)?;
    if bound.var != var || bound.k != 1 {
        return None; // different variable, or a non-unit-multiplier bound (later slice)
    }
    let c = bound.bound;
    let kc = k.checked_mul(c)?;
    // Real-infeasible test (see the type docs); feasible ⇒ decline.
    let infeasible = if bound.lower { b < kc } else { kc < b };
    if !infeasible {
        return None;
    }
    Some(IntEqBound {
        var,
        k,
        b,
        c,
        lower: bound.lower,
    })
}

impl IntReconstructCtx {
    /// Build the kernel `False` proof for a single-variable integer
    /// equality-and-unit-bound [`IntEqBound`] (`k·x = b` with `c ≤ x` or `x ≤ c`,
    /// real-infeasible).
    ///
    /// Mirrors the equality as `h_eq : Eq Z (k·x) b` and the bound as a hypothesis over
    /// `Z`, scales the bound by the positive `k` (`mul_le_mul_of_nonneg_left`), rewrites
    /// the scaled literal `k·c` through the ring normalizer, and chains through the
    /// equality (recast `k·x → b`) to a literal `b ⋈ k·c` contradiction closed by
    /// `lt_irrefl`.
    fn build_int_eq_bound_false(&mut self, iv: &IntEqBound) -> Result<ExprId, ReconstructError> {
        let decline = |d: &str| ReconstructError::UnsupportedTerm {
            term: format!("integer equality-bound reconstruction declined: {d}"),
        };
        let bound = DIO_UNIT_MAX.unsigned_abs();
        let kc =
            iv.k.checked_mul(iv.c)
                .ok_or_else(|| decline("k·c overflow"))?;
        if iv.k > DIO_UNIT_MAX
            || iv.b.unsigned_abs() > bound
            || iv.c.unsigned_abs() > bound
            || kc.unsigned_abs() > bound
        {
            return Err(decline("k / b / c / k·c exceed the unit-expansion bound"));
        }
        // The literal `lt` facts need non-negative operands for `lt_lit_lit`.
        if iv.b < 0 || kc < 0 {
            return Err(decline("a literal bound is negative (later slice)"));
        }

        let x_name = self.var_const_for(iv.var);
        let xe = self.kernel.const_(x_name, vec![]);
        let k_lit = self.mk_intlit(iv.k);
        let gx = self.mk_mul(k_lit, xe); // k·x
        let b_lit = self.mk_intlit(iv.b);
        let c_lit = self.mk_intlit(iv.c);

        // h_eq : Eq Z (k·x) b (the asserted equality, mirrored verbatim).
        let eq_prop = self.mk_eq(gx, b_lit);
        let h_eq = self.hyp_axiom(eq_prop)?;

        // 0 ≤ k (k > 0), for the positive scaling of the bound.
        let zero = self.mk_zero();
        let lt_zero_k = self.lt_zero_intlit(iv.k)?;
        let le_zero_k = self.le_of_lt_app(zero, k_lit, lt_zero_k);

        if iv.lower {
            self.close_eq_bound_lower(iv, xe, gx, k_lit, b_lit, c_lit, h_eq, le_zero_k)
        } else {
            self.close_eq_bound_upper(iv, xe, gx, k_lit, b_lit, c_lit, h_eq, le_zero_k)
        }
    }

    /// Lower-bound close: from `h_eq : Eq Z (k·x) b`, `c ≤ x`, and `b < k·c`, derive
    /// `False`. Scales `c ≤ x` to `k·c ≤ k·x`, recasts the RHS to `b` through `h_eq`,
    /// rewrites the literal `k·c`, and closes `b < k·c ≤ b ⇒ b < b`.
    #[allow(clippy::too_many_arguments)]
    fn close_eq_bound_lower(
        &mut self,
        iv: &IntEqBound,
        xe: ExprId,
        gx: ExprId,
        k_lit: ExprId,
        b_lit: ExprId,
        c_lit: ExprId,
        h_eq: ExprId,      // Eq Z (k·x) b
        le_zero_k: ExprId, // le 0 k
    ) -> Result<ExprId, ReconstructError> {
        let kc = iv.k * iv.c;
        let kc_lit = self.mk_intlit(kc);
        // h_bound : le c x.
        let bound_prop = self.mk_le(c_lit, xe);
        let h_bound = self.hyp_axiom(bound_prop)?;
        // le (k·c)(k·x) by scaling; recast (mul k c) → literal k·c on the left.
        let le_kc_kx = self.mul_le_mul_left_app(k_lit, c_lit, xe, le_zero_k, h_bound);
        let mul_kc = self.mk_mul(k_lit, c_lit);
        let eq_mul_kc = self.eq_mul_lit_lit(iv.k, iv.c); // Eq Z (mul k c)(intlit k·c)
        let le_kclit_kx = self.le_cast_left(mul_kc, kc_lit, gx, le_kc_kx, eq_mul_kc);
        // recast (k·x) → b on the right via h_eq : le (intlit k·c) b.
        let le_kclit_b = self.le_cast_right(kc_lit, gx, b_lit, le_kclit_kx, h_eq);
        // lt b (k·c) literal (b < k·c by infeasibility) ∘ le (k·c) b ⇒ lt b b.
        let lt_b_kc = self.lt_lit_lit(iv.b, kc)?;
        let lt_b_b = self.lt_of_lt_of_le_app(b_lit, kc_lit, b_lit, lt_b_kc, le_kclit_b);
        let irr = self.lt_irrefl_app(b_lit);
        Ok(self.kernel.app(irr, lt_b_b))
    }

    /// Upper-bound close: from `h_eq : Eq Z (k·x) b`, `x ≤ c`, and `k·c < b`, derive
    /// `False`. Scales `x ≤ c` to `k·x ≤ k·c`, recasts the LHS to `b` through `h_eq`,
    /// rewrites the literal `k·c`, and closes `b ≤ k·c < b ⇒ b < b`.
    #[allow(clippy::too_many_arguments)]
    fn close_eq_bound_upper(
        &mut self,
        iv: &IntEqBound,
        xe: ExprId,
        gx: ExprId,
        k_lit: ExprId,
        b_lit: ExprId,
        c_lit: ExprId,
        h_eq: ExprId,      // Eq Z (k·x) b
        le_zero_k: ExprId, // le 0 k
    ) -> Result<ExprId, ReconstructError> {
        let kc = iv.k * iv.c;
        let kc_lit = self.mk_intlit(kc);
        // h_bound : le x c.
        let bound_prop = self.mk_le(xe, c_lit);
        let h_bound = self.hyp_axiom(bound_prop)?;
        // le (k·x)(k·c) by scaling; recast (mul k c) → literal k·c on the right.
        let le_kx_kc = self.mul_le_mul_left_app(k_lit, xe, c_lit, le_zero_k, h_bound);
        let mul_kc = self.mk_mul(k_lit, c_lit);
        let eq_mul_kc = self.eq_mul_lit_lit(iv.k, iv.c); // Eq Z (mul k c)(intlit k·c)
        let le_kx_kclit = self.le_cast_right(gx, mul_kc, kc_lit, le_kx_kc, eq_mul_kc);
        // recast (k·x) → b on the left via h_eq : le b (intlit k·c).
        let le_b_kclit = self.le_cast_left(gx, b_lit, kc_lit, le_kx_kclit, h_eq);
        // le b (k·c) ∘ lt (k·c) b literal (k·c < b) ⇒ lt b b.
        let lt_kc_b = self.lt_lit_lit(kc, iv.b)?;
        let lt_b_b = self.lt_of_le_of_lt_app(b_lit, kc_lit, b_lit, le_b_kclit, lt_kc_b);
        let irr = self.lt_irrefl_app(b_lit);
        Ok(self.kernel.app(irr, lt_b_b))
    }

    /// Build the kernel `False` proof for a detected [`IntInterval`] `c ≤ k·x ≤ d`.
    ///
    /// Mirrors the asserted atoms as hypothesis axioms `h_lo : le c (k·x)` and
    /// `h_hi : le (k·x) d`, derives the strict literal facts `lt (k·m) (k·x)` and
    /// `lt (k·x) (k·(m+1))`, cancels the positive `k` (via `le_total` + the forward
    /// scaling axiom, exactly as the Diophantine discreteness closers) to obtain
    /// `lt m x` and `lt x (m+1)`, shifts by `−m` to `lt 0 (x−m)` / `lt (x−m) 1`, and
    /// closes with `no_int_between (x−m)`. For `m = 0` the shift is the identity and
    /// the close is `no_int_between x` directly.
    fn build_int_interval_false(&mut self, iv: &IntInterval) -> Result<ExprId, ReconstructError> {
        let decline = |d: &str| ReconstructError::UnsupportedTerm {
            term: format!("integer-interval reconstruction declined: {d}"),
        };
        let bound = DIO_UNIT_MAX.unsigned_abs();
        if iv.k > DIO_UNIT_MAX
            || iv.c.unsigned_abs() > bound
            || iv.d.unsigned_abs() > bound
            || iv.m.unsigned_abs() > bound
        {
            return Err(decline("k / c / d / m exceed the unit-expansion bound"));
        }
        // Dense index 0 for the single variable; `x` as a kernel constant.
        let x_name = self.var_const_for(iv.var);
        let xe = self.kernel.const_(x_name, vec![]);
        let k_lit = self.mk_intlit(iv.k);
        let gx = self.mk_mul(k_lit, xe); // k·x
        let c_lit = self.mk_intlit(iv.c);
        let d_lit = self.mk_intlit(iv.d);

        // --- mirror the asserted atoms as hypotheses over Z -------------------
        // h_lo : le c (k·x) ; h_hi : le (k·x) d.
        let lo_prop = self.mk_le(c_lit, gx);
        let h_lo = self.hyp_axiom(lo_prop)?;
        let hi_prop = self.mk_le(gx, d_lit);
        let h_hi = self.hyp_axiom(hi_prop)?;

        // --- 0 ≤ k (k > 0) ----------------------------------------------------
        let zero = self.mk_zero();
        let lt_zero_k = self.lt_zero_intlit(iv.k)?; // lt zero k
        let le_zero_k = self.le_of_lt_app(zero, k_lit, lt_zero_k); // le zero k

        // --- strict literal facts about k·x ----------------------------------
        let km = iv.k * iv.m;
        let km1 = iv.k * (iv.m + 1);
        // Require non-negative bounds for the `lt_intlit_intlit` literal facts (true
        // whenever m ≥ 0, i.e. c ≥ 1); decline otherwise.
        if km < 0 || iv.d < 0 || km1 < 0 {
            return Err(decline(
                "reduction offset yields a negative bound (later slice)",
            ));
        }
        // --- cancel the positive k : lt m x and lt x (m+1) -------------------
        let lt_m_x = self.derive_lt_m_x(iv.k, iv.c, iv.m, c_lit, gx, xe, k_lit, h_lo, le_zero_k)?;
        let lt_x_m1 =
            self.derive_lt_x_m1(iv.k, iv.d, iv.m, d_lit, gx, xe, k_lit, h_hi, le_zero_k)?;

        // --- shift by −m, then close with no_int_between ----------------------
        self.close_no_int_between(xe, zero, iv.m, lt_m_x, lt_x_m1)
    }

    /// From `h_lo : le c (k·x)` and `le_zero_k : le 0 k` (with `k·m < c`, `0 ≤ k·m`),
    /// derive `lt (intlit m) x` by chaining `lt (k·m) c ∘ le c (k·x)`, recasting the
    /// literal `k·m` to `mul k m`, and cancelling the positive `k`. The lower half of
    /// the interval reduction, parametric in the multiplier `k` so the
    /// different-multiplier path can reuse it with its own lower multiplier.
    #[allow(clippy::too_many_arguments)]
    fn derive_lt_m_x(
        &mut self,
        k: i128,
        c: i128,
        m: i128,
        c_lit: ExprId,
        gx: ExprId, // mul k x
        xe: ExprId,
        k_lit: ExprId,
        h_lo: ExprId,      // le c (k·x)
        le_zero_k: ExprId, // le 0 k
    ) -> Result<ExprId, ReconstructError> {
        let km = k * m;
        let km_lit = self.mk_intlit(km);
        let m_lit = self.mk_intlit(m);
        // lt (k·m) c (literal) ∘ le c (k·x) : lt (intlit (k·m)) (k·x); recast left.
        let lt_km_c = self.lt_lit_lit(km, c)?;
        let lt_kmlit_gx = self.lt_of_lt_of_le_app(km_lit, c_lit, gx, lt_km_c, h_lo);
        let mul_km = self.mk_mul(k_lit, m_lit); // mul k m
        let eq_mul_km = self.eq_mul_lit_lit(k, m); // Eq Z (mul k m)(intlit (k·m))
        let eq_kmlit_mul = self.eq_symm(mul_km, km_lit, eq_mul_km);
        let lt_km_gx = self.lt_cast_left(km_lit, mul_km, gx, lt_kmlit_gx, eq_kmlit_mul);
        Ok(self.cancel_pos_mul_lt_lower(k_lit, m_lit, xe, le_zero_k, lt_km_gx))
    }

    /// From `h_hi : le (k·x) d` and `le_zero_k : le 0 k` (with `d < k·(m+1)`,
    /// `0 ≤ k·(m+1)`), derive `lt x (intlit (m+1))` symmetrically to
    /// [`Self::derive_lt_m_x`]: the upper half of the interval reduction.
    #[allow(clippy::too_many_arguments)]
    fn derive_lt_x_m1(
        &mut self,
        k: i128,
        d: i128,
        m: i128,
        d_lit: ExprId,
        gx: ExprId, // mul k x
        xe: ExprId,
        k_lit: ExprId,
        h_hi: ExprId,      // le (k·x) d
        le_zero_k: ExprId, // le 0 k
    ) -> Result<ExprId, ReconstructError> {
        let km1 = k * (m + 1);
        let km1_lit = self.mk_intlit(km1);
        let m1_lit = self.mk_intlit(m + 1);
        // le (k·x) d ∘ lt d (intlit (k·(m+1))) : lt (k·x)(intlit …); recast right.
        let lt_d_km1 = self.lt_lit_lit(d, km1)?;
        let lt_gx_km1lit = self.lt_of_le_of_lt_app(gx, d_lit, km1_lit, h_hi, lt_d_km1);
        let mul_km1 = self.mk_mul(k_lit, m1_lit); // mul k (m+1)
        let eq_mul_km1 = self.eq_mul_lit_lit(k, m + 1);
        let eq_km1lit_mul = self.eq_symm(mul_km1, km1_lit, eq_mul_km1);
        let lt_gx_km1 = self.lt_cast_right(gx, km1_lit, mul_km1, lt_gx_km1lit, eq_km1lit_mul);
        Ok(self.cancel_pos_mul_lt_upper(k_lit, xe, m1_lit, le_zero_k, lt_gx_km1))
    }

    /// Close a single-variable discreteness contradiction: from `lt_m_x : lt m x`
    /// and `lt_x_m1 : lt x (m+1)` (both literals `m`, `m+1` ≥ 0), derive `False` by
    /// `no_int_between`. For `m = 0` the bounds are already `lt 0 x`/`lt x 1`; for
    /// `m ≠ 0` it shifts both by `−m` to the unit window `0 < x−m < 1`. Shared by the
    /// common-multiplier and different-multiplier interval reconstructors.
    fn close_no_int_between(
        &mut self,
        xe: ExprId,
        zero: ExprId,
        m: i128,
        lt_m_x: ExprId,  // lt (intlit m) x
        lt_x_m1: ExprId, // lt x (intlit (m+1))
    ) -> Result<ExprId, ReconstructError> {
        if m == 0 {
            // lt_m_x : lt zero x and lt_x_m1 : lt x one already (mk_intlit 0/1 fold to
            // zero/one) — close with `no_int_between x (And.intro (lt 0 x)(lt x 1))`.
            let one = self.mk_one();
            let p_prop = self.mk_lt(zero, xe);
            let q_prop = self.mk_lt(xe, one);
            let and_proof = self.and_intro(p_prop, q_prop, lt_m_x, lt_x_m1);
            return Ok(self.no_int_between_app(xe, and_proof));
        }
        // General m ≠ 0: w = x + (−m) = x − m. Prove lt 0 w from lt m x, and lt w 1
        // from lt x (m+1), by adding (−m) to both sides (additive shift), then close.
        let m_lit = self.mk_intlit(m);
        let m1_lit = self.mk_intlit(m + 1);
        let neg_m_lit = self.mk_intlit(-m);
        let w = self.mk_add(xe, neg_m_lit); // x + (−m)

        // lt 0 w :  from lt m x add (−m): lt (m + (−m)) (x + (−m)); normalize lhs → 0.
        let lt_zero_w = self.shift_lt_lower(m_lit, xe, neg_m_lit, m, lt_m_x)?;
        // lt w 1 :  from lt x (m+1) add (−m): lt (x + (−m)) ((m+1) + (−m)); rhs → 1.
        let lt_w_one = self.shift_lt_upper(xe, m1_lit, neg_m_lit, m, lt_x_m1)?;

        let one = self.mk_one();
        let p_prop = self.mk_lt(zero, w);
        let q_prop = self.mk_lt(w, one);
        let and_proof = self.and_intro(p_prop, q_prop, lt_zero_w, lt_w_one);
        Ok(self.no_int_between_app(w, and_proof))
    }

    /// Build the kernel `False` proof for a [`IntIntervalDiff`] `c ≤ k_lo·x`,
    /// `k_hi·x ≤ d` (distinct positive multipliers).
    ///
    /// Mirrors the asserted atoms verbatim as hypotheses `h_lo : le c (k_lo·x)` and
    /// `h_hi : le (k_hi·x) d`, derives `lt m_lo x` from the lower (cancelling `k_lo`)
    /// and `lt x (m_hi+1)` from the upper (cancelling `k_hi`) — each via the SAME
    /// half-reduction the equal-multiplier path uses, but with its own multiplier.
    /// When `m_hi < m_lo` it weakens the upper to `lt x (m_lo+1)` by transitivity
    /// through the literal fact `lt (m_hi+1) (m_lo+1)`, so both bounds share the
    /// offset `m_lo`, then closes with [`Self::close_no_int_between`].
    fn build_int_interval_diff_mult_false(
        &mut self,
        iv: &IntIntervalDiff,
    ) -> Result<ExprId, ReconstructError> {
        let decline = |d: &str| ReconstructError::UnsupportedTerm {
            term: format!("different-multiplier interval reconstruction declined: {d}"),
        };
        let bound = DIO_UNIT_MAX;
        if iv.k_lo > bound
            || iv.k_hi > bound
            || iv.c.unsigned_abs() > bound.unsigned_abs()
            || iv.d.unsigned_abs() > bound.unsigned_abs()
            || iv.m_lo.unsigned_abs() > bound.unsigned_abs()
            || iv.m_hi.unsigned_abs() > bound.unsigned_abs()
        {
            return Err(decline(
                "k_lo / k_hi / c / d / m exceed the unit-expansion bound",
            ));
        }
        // Require non-negative bounds for the literal `lt` facts (true when c ≥ 1, d ≥ 0).
        if iv.k_lo * iv.m_lo < 0 || iv.d < 0 || iv.k_hi * (iv.m_hi + 1) < 0 {
            return Err(decline("a reduction bound is negative (later slice)"));
        }

        let x_name = self.var_const_for(iv.var);
        let xe = self.kernel.const_(x_name, vec![]);
        let zero = self.mk_zero();

        // --- lower half: h_lo : le c (k_lo·x) ⟹ lt m_lo x -------------------
        let klo_lit = self.mk_intlit(iv.k_lo);
        let glo = self.mk_mul(klo_lit, xe); // k_lo·x
        let c_lit = self.mk_intlit(iv.c);
        let lo_prop = self.mk_le(c_lit, glo);
        let h_lo = self.hyp_axiom(lo_prop)?;
        let lt_zero_klo = self.lt_zero_intlit(iv.k_lo)?;
        let le_zero_klo = self.le_of_lt_app(zero, klo_lit, lt_zero_klo);
        let lt_m_x = self.derive_lt_m_x(
            iv.k_lo,
            iv.c,
            iv.m_lo,
            c_lit,
            glo,
            xe,
            klo_lit,
            h_lo,
            le_zero_klo,
        )?;

        // --- upper half: h_hi : le (k_hi·x) d ⟹ lt x (m_hi+1) ---------------
        let khi_lit = self.mk_intlit(iv.k_hi);
        let ghi = self.mk_mul(khi_lit, xe); // k_hi·x
        let d_lit = self.mk_intlit(iv.d);
        let hi_prop = self.mk_le(ghi, d_lit);
        let h_hi = self.hyp_axiom(hi_prop)?;
        let lt_zero_khi = self.lt_zero_intlit(iv.k_hi)?;
        let le_zero_khi = self.le_of_lt_app(zero, khi_lit, lt_zero_khi);
        let lt_x_mhi1 = self.derive_lt_x_m1(
            iv.k_hi,
            iv.d,
            iv.m_hi,
            d_lit,
            ghi,
            xe,
            khi_lit,
            h_hi,
            le_zero_khi,
        )?;

        // --- align the offsets at m_lo, then close --------------------------
        // m_hi ≤ m_lo (detector invariant). If equal, the upper is already
        // `lt x (m_lo+1)`. Otherwise weaken via `lt (m_hi+1)(m_lo+1)` (literals).
        let lt_x_mlo1 = if iv.m_hi == iv.m_lo {
            lt_x_mhi1
        } else {
            let mhi1_lit = self.mk_intlit(iv.m_hi + 1);
            let mlo1_lit = self.mk_intlit(iv.m_lo + 1);
            // 0 ≤ m_hi+1 < m_lo+1, so the literal `lt` and its `le` weakening hold.
            let lt_mhi1_mlo1 = self.lt_lit_lit(iv.m_hi + 1, iv.m_lo + 1)?;
            let le_mhi1_mlo1 = self.le_of_lt_app(mhi1_lit, mlo1_lit, lt_mhi1_mlo1);
            self.lt_of_lt_of_le_app(xe, mhi1_lit, mlo1_lit, lt_x_mhi1, le_mhi1_mlo1)
        };
        self.close_no_int_between(xe, zero, iv.m_lo, lt_m_x, lt_x_mlo1)
    }

    /// Get (declaring lazily) the opaque `Z`-typed constant for the single interval
    /// variable, using a fixed dense index `0`. The variable identity ([`AtomVar`] —
    /// a symbol or an opaque application) is irrelevant to the proof: the
    /// single-variable shape always maps to the one opaque `Z` constant, which is
    /// exactly why an opaque application reconstructs identically to a symbol.
    fn var_const_for(&mut self, _var: AtomVar) -> NameId {
        self.var_const(0)
    }

    /// `Eq Z (mul (intlit a)(intlit b)) (intlit (a·b))` via the ring normalizer (the
    /// kernel term `mul (mk_intlit a)(mk_intlit b)` hash-conses with the normalizer's
    /// `kexpr`). Handles `a = 0` or `b = 0` (product `zero`) through the normalizer's
    /// `Zero`/`mul_zero` path; both nonzero go through the literal-product distribution.
    fn eq_mul_lit_lit(&mut self, a: i128, b: i128) -> ExprId {
        let za = intlit_zexpr(a);
        let zb = intlit_zexpr(b);
        let prod = ZExpr::Mul(Box::new(za), Box::new(zb));
        let (gens, kexpr, proof) = self
            .normalize(&prod)
            .expect("literal·literal normalizer never declines (degree ≤ 1)");
        let prod_val = a.checked_mul(b).expect("k·m within i128");
        debug_assert_eq!(gens, lin_to_canon_gens(&[], prod_val));
        let canon = self.gens_to_expr(&gens);
        let lit = self.mk_intlit(prod_val);
        let bridge = self.intlit_eq_canon(prod_val); // Eq Z lit canon
        let bridge_sym = self.eq_symm(lit, canon, bridge); // canon = lit
        // proof : Eq Z kexpr canon ; kexpr == mul (mk_intlit a)(mk_intlit b).
        self.eq_trans(kexpr, canon, lit, proof, bridge_sym)
    }

    /// `lt (intlit a)(intlit b)` for arbitrary `a < b`, dispatching the `a = 0`
    /// case to [`Self::lt_zero_intlit`].
    pub(super) fn lt_lit_lit(&mut self, a: i128, b: i128) -> Result<ExprId, ReconstructError> {
        debug_assert!(b > a);
        if a == 0 {
            self.lt_zero_intlit(b)
        } else {
            self.lt_intlit_intlit(a, b)
        }
    }

    /// From `h_lt : lt (k·m) (k·x)` and `h_k : le 0 k` derive `lt m x` — cancel the
    /// positive multiplier `k`. Pure forward scaling + total order + irreflexivity (no
    /// strict-cancel axiom), mirroring `prove_m_prime_lt_one`.
    fn cancel_pos_mul_lt_lower(
        &mut self,
        k_lit: ExprId,
        m_lit: ExprId,
        xe: ExprId,
        h_k: ExprId,
        h_lt: ExprId, // lt (mul k m) (mul k x)
    ) -> ExprId {
        // le_total m x : Or (le m x)(le x m).
        let a_prop = self.mk_le(m_lit, xe);
        let b_prop = self.mk_le(xe, m_lit);
        let or_proof = {
            let ax = self.kernel.const_(self.int.le_total, vec![]);
            let e = self.kernel.app(ax, m_lit);
            self.kernel.app(e, xe)
        };
        let target = self.mk_le(m_lit, xe);
        let minor_inl = {
            let fid = self.fresh_fvar();
            let h = self.kernel.fvar(fid);
            let body = self.kernel.abstract_fvars(h, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, a_prop, body, BinderInfo::Default)
        };
        let minor_inr = {
            let fid = self.fresh_fvar();
            let h_le_x_m = self.kernel.fvar(fid); // le x m
            // mul_le_mul_of_nonneg_left k x m h_k h_le_x_m : le (k·x)(k·m).
            let le_kx_km = self.mul_le_mul_left_app(k_lit, xe, m_lit, h_k, h_le_x_m);
            // lt (k·m)(k·x) ∘ le (k·x)(k·m) : lt (k·m)(k·m).
            let km = self.mk_mul(k_lit, m_lit);
            let kx = self.mk_mul(k_lit, xe);
            let lt_km_km = self.lt_of_lt_of_le_app(km, kx, km, h_lt, le_kx_km);
            let irr = self.lt_irrefl_app(km);
            let false_proof = self.kernel.app(irr, lt_km_km);
            let exf = self.ex_falso(target, false_proof);
            let body = self.kernel.abstract_fvars(exf, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, b_prop, body, BinderInfo::Default)
        };
        let le_m_x = self.or_rec_le(a_prop, b_prop, target, minor_inl, minor_inr, or_proof);
        // m ≠ x : else k·m = k·x contradicts lt (k·m)(k·x).
        let not_eq = {
            let fid = self.fresh_fvar();
            let h_eq = self.kernel.fvar(fid); // Eq Z m x
            let cong = self.congr_mul_right(k_lit, m_lit, xe, h_eq); // mul k m = mul k x
            let km = self.mk_mul(k_lit, m_lit);
            let kx = self.mk_mul(k_lit, xe);
            // cast lt (k·m)(k·x) on the LEFT km → kx ⇒ lt (k·x)(k·x).
            let lt_kx_kx = self.lt_cast_left(km, kx, kx, h_lt, cong);
            let irr = self.lt_irrefl_app(kx);
            let false_proof = self.kernel.app(irr, lt_kx_kx);
            let body = self.kernel.abstract_fvars(false_proof, &[fid]);
            let anon = self.kernel.anon();
            let eq_m_x = self.mk_eq(m_lit, xe);
            self.kernel.lam(anon, eq_m_x, body, BinderInfo::Default)
        };
        self.lt_of_le_of_ne_app(m_lit, xe, le_m_x, not_eq)
    }

    /// From `h_lt : lt (k·x) (k·(m+1))` and `h_k : le 0 k` derive `lt x (m+1)` — cancel
    /// the positive multiplier on the upper bound. Symmetric to
    /// [`Self::cancel_pos_mul_lt_lower`].
    fn cancel_pos_mul_lt_upper(
        &mut self,
        k_lit: ExprId,
        xe: ExprId,
        m1_lit: ExprId,
        h_k: ExprId,
        h_lt: ExprId, // lt (mul k x) (mul k (m+1))
    ) -> ExprId {
        let a_prop = self.mk_le(xe, m1_lit); // le x (m+1)
        let b_prop = self.mk_le(m1_lit, xe); // le (m+1) x
        let or_proof = {
            let ax = self.kernel.const_(self.int.le_total, vec![]);
            let e = self.kernel.app(ax, xe);
            self.kernel.app(e, m1_lit)
        };
        let target = self.mk_le(xe, m1_lit);
        let minor_inl = {
            let fid = self.fresh_fvar();
            let h = self.kernel.fvar(fid);
            let body = self.kernel.abstract_fvars(h, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, a_prop, body, BinderInfo::Default)
        };
        let minor_inr = {
            let fid = self.fresh_fvar();
            let h_le_m1_x = self.kernel.fvar(fid); // le (m+1) x
            // mul_le_mul_of_nonneg_left k (m+1) x h_k h_le_m1_x : le (k·(m+1))(k·x).
            let le_km1_kx = self.mul_le_mul_left_app(k_lit, m1_lit, xe, h_k, h_le_m1_x);
            let kx = self.mk_mul(k_lit, xe);
            let km1 = self.mk_mul(k_lit, m1_lit);
            // lt (k·x)(k·(m+1)) ∘ le (k·(m+1))(k·x) : lt (k·x)(k·x).
            let lt_kx_kx = self.lt_of_lt_of_le_app(kx, km1, kx, h_lt, le_km1_kx);
            let irr = self.lt_irrefl_app(kx);
            let false_proof = self.kernel.app(irr, lt_kx_kx);
            let exf = self.ex_falso(target, false_proof);
            let body = self.kernel.abstract_fvars(exf, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, b_prop, body, BinderInfo::Default)
        };
        let le_x_m1 = self.or_rec_le(a_prop, b_prop, target, minor_inl, minor_inr, or_proof);
        // x ≠ (m+1) : else k·x = k·(m+1) contradicts lt (k·x)(k·(m+1)).
        let not_eq = {
            let fid = self.fresh_fvar();
            let h_eq = self.kernel.fvar(fid); // Eq Z x (m+1)
            let cong = self.congr_mul_right(k_lit, xe, m1_lit, h_eq); // mul k x = mul k (m+1)
            let kx = self.mk_mul(k_lit, xe);
            let km1 = self.mk_mul(k_lit, m1_lit);
            // cast lt (k·x)(k·(m+1)) on the RIGHT km1 → kx ⇒ lt (k·x)(k·x).
            let cong_sym = self.eq_symm(kx, km1, cong); // mul k (m+1) = mul k x
            let lt_kx_kx = self.lt_cast_right(kx, km1, kx, h_lt, cong_sym);
            let irr = self.lt_irrefl_app(kx);
            let false_proof = self.kernel.app(irr, lt_kx_kx);
            let body = self.kernel.abstract_fvars(false_proof, &[fid]);
            let anon = self.kernel.anon();
            let eq_x_m1 = self.mk_eq(xe, m1_lit);
            self.kernel.lam(anon, eq_x_m1, body, BinderInfo::Default)
        };
        self.lt_of_le_of_ne_app(xe, m1_lit, le_x_m1, not_eq)
    }

    /// `Or.rec` over `le`-valued props: from `minor_inl : a → target`,
    /// `minor_inr : b → target`, and `or_proof : Or a b`, build `target`.
    fn or_rec_le(
        &mut self,
        a_prop: ExprId,
        b_prop: ExprId,
        target: ExprId,
        minor_inl: ExprId,
        minor_inr: ExprId,
        or_proof: ExprId,
    ) -> ExprId {
        let anon = self.kernel.anon();
        let or_ab = {
            let or_c = self.kernel.const_(self.int.logic.or, vec![]);
            let e = self.kernel.app(or_c, a_prop);
            self.kernel.app(e, b_prop)
        };
        let motive = self.kernel.lam(anon, or_ab, target, BinderInfo::Default);
        let rec = self.kernel.const_(self.int.logic.or_rec, vec![]);
        let e = self.kernel.app(rec, a_prop);
        let e = self.kernel.app(e, b_prop);
        let e = self.kernel.app(e, motive);
        let e = self.kernel.app(e, minor_inl);
        let e = self.kernel.app(e, minor_inr);
        self.kernel.app(e, or_proof)
    }

    /// From `h : lt (intlit m) x` derive `lt zero (add x (neg (intlit m)))` by adding
    /// `neg (intlit m)` to both sides and normalizing the lhs `m + (−m) → 0`.
    fn shift_lt_lower(
        &mut self,
        m_lit: ExprId,
        xe: ExprId,
        neg_m_lit: ExprId,
        m: i128,
        h: ExprId, // lt m x
    ) -> Result<ExprId, ReconstructError> {
        // h_le : le (neg m)(neg m)  (le_refl).
        let h_le = self.le_refl_app(neg_m_lit);
        // add_lt_add_of_le_of_lt (neg m)(neg m) m x h_le h : lt (add (neg m) m)(add (neg m) x).
        let combined = self.add_lt_add_of_le_of_lt_app(neg_m_lit, neg_m_lit, m_lit, xe, h_le, h);
        // lhs (add (neg m) m) → zero ; rhs (add (neg m) x) → (add x (neg m)) (= w).
        let lhs = self.mk_add(neg_m_lit, m_lit); // (−m) + m
        let rhs = self.mk_add(neg_m_lit, xe); // (−m) + x
        let zero = self.mk_zero();
        // Eq Z ((−m) + m) zero via the ring normalizer (neg_m_lit is the *literal*
        // `intlit (−m)`, not `neg (intlit m)`, so we normalize the literal sum).
        let lhs_eq_zero = self.intlit_pair_sum_eq_zero(neg_m_lit, m_lit, -m, m)?;
        let lt_zero_rhs = self.lt_cast_left(lhs, zero, rhs, combined, lhs_eq_zero); // lt zero ((−m)+x)
        // rhs ((−m)+x) → w = (x + (−m)) by commutativity.
        let w = self.mk_add(xe, neg_m_lit);
        let comm2 = self.add_comm_eq(neg_m_lit, xe); // (−m)+x = x+(−m)
        Ok(self.lt_cast_right(zero, rhs, w, lt_zero_rhs, comm2))
    }

    /// From `h : lt x (intlit (m+1))` derive `lt (add x (neg (intlit m))) one` by adding
    /// `neg (intlit m)` to both sides and normalizing the rhs `(m+1) + (−m) → 1`.
    fn shift_lt_upper(
        &mut self,
        xe: ExprId,
        m1_lit: ExprId,
        neg_m_lit: ExprId,
        m: i128,
        h: ExprId, // lt x (m+1)
    ) -> Result<ExprId, ReconstructError> {
        let h_le = self.le_refl_app(neg_m_lit);
        // add_lt_add_of_le_of_lt (neg m)(neg m) x (m+1) h_le h :
        //   lt (add (neg m) x)(add (neg m)(m+1)).
        let combined = self.add_lt_add_of_le_of_lt_app(neg_m_lit, neg_m_lit, xe, m1_lit, h_le, h);
        let lhs = self.mk_add(neg_m_lit, xe); // (−m)+x
        let rhs = self.mk_add(neg_m_lit, m1_lit); // (−m)+(m+1)
        let one = self.mk_one();
        // rhs ((−m)+(m+1)) → one (sum is 1).
        let rhs_eq_one = self.intlit_pair_sum_eq_one(neg_m_lit, m1_lit, -m, m + 1)?;
        let lt_lhs_one = self.lt_cast_right(lhs, rhs, one, combined, rhs_eq_one); // lt ((−m)+x) one
        // lhs ((−m)+x) → w = (x+(−m)) by commutativity.
        let w = self.mk_add(xe, neg_m_lit);
        let comm = self.add_comm_eq(neg_m_lit, xe); // (−m)+x = x+(−m)
        Ok(self.lt_cast_left(lhs, w, one, lt_lhs_one, comm))
    }

    /// `Eq Z (add (intlit a)(intlit b)) zero` when `a + b = 0` (both nonzero), via the
    /// ring normalizer (canonical form is the empty gen list = `zero`).
    fn intlit_pair_sum_eq_zero(
        &mut self,
        _a_lit: ExprId,
        _b_lit: ExprId,
        a: i128,
        b: i128,
    ) -> Result<ExprId, ReconstructError> {
        debug_assert_eq!(a + b, 0);
        self.intlit_pair_sum_eq(a, b, 0)
    }

    /// `Eq Z (add (intlit a)(intlit b)) one` when `a + b = 1` (both nonzero), via the
    /// ring normalizer.
    fn intlit_pair_sum_eq_one(
        &mut self,
        _a_lit: ExprId,
        _b_lit: ExprId,
        a: i128,
        b: i128,
    ) -> Result<ExprId, ReconstructError> {
        debug_assert_eq!(a + b, 1);
        self.intlit_pair_sum_eq(a, b, 1)
    }

    /// `Eq Z (add (intlit a)(intlit b)) (intlit s)` when `a + b = s` (`a`, `b` nonzero),
    /// via the ring normalizer (a generalization of [`Self::intlit_add_eq`] permitting
    /// `s = 0` or any `s`). Builds the faithful sum, normalizes, checks the canonical
    /// form matches `s`, and bridges to the `mk_intlit s` term.
    fn intlit_pair_sum_eq(
        &mut self,
        a: i128,
        b: i128,
        s: i128,
    ) -> Result<ExprId, ReconstructError> {
        debug_assert_eq!(a + b, s);
        let (Some(za), Some(zb)) = (lin_to_zexpr(&[], a), lin_to_zexpr(&[], b)) else {
            return Err(ReconstructError::UnsupportedTerm {
                term: "intlit_pair_sum requires both operands nonzero".to_owned(),
            });
        };
        let sum_zexpr = ZExpr::Add(Box::new(za), Box::new(zb));
        let (gens, kexpr, proof) =
            self.normalize(&sum_zexpr)
                .ok_or_else(|| ReconstructError::UnsupportedTerm {
                    term: "intlit_pair_sum normalizer declined".to_owned(),
                })?;
        let expected = lin_to_canon_gens(&[], s);
        if gens != expected {
            return Err(ReconstructError::UnsupportedTerm {
                term: "intlit_pair_sum did not canonicalize to the expected sum".to_owned(),
            });
        }
        let canon = self.gens_to_expr(&gens);
        let s_lit = self.mk_intlit(s);
        let bridge = self.intlit_eq_canon(s); // Eq Z (intlit s) canon
        let bridge_sym = self.eq_symm(s_lit, canon, bridge); // canon = intlit s
        Ok(self.eq_trans(kexpr, canon, s_lit, proof, bridge_sym))
    }
}

/// **Reconstruct an integer-inequality (interval) infeasibility to a kernel-checked
/// Lean `False`** (ADR-0042, the integer-cut payoff). Detects the single-variable
/// shape `c ≤ k·x ≤ d` (k > 0) with no multiple of `k` in `[c, d]`, reconstructs the
/// discreteness argument over [`super::IntPrelude`], and returns the assembled `False` proof
/// term (already `infer` + `def_eq False`-gated through the kernel).
///
/// # Errors
///
/// [`ReconstructError::UnsupportedTerm`] when the assertions do not match the detected
/// shape (multiple variables, non-unit multipliers, an integer-feasible interval, or a
/// coefficient/bound overflow) — never fabricated; [`ReconstructError::KernelRejected`]
/// when the assembled term does not kernel-check to `False`.
pub fn reconstruct_int_inequality_proof(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<ExprId, ReconstructError> {
    let (_, proof) = build_and_gate_int_interval(arena, assertions)?;
    Ok(proof)
}

/// The theorem name used for the exported integer-interval refutation Lean module.
const INT_INEQ_LEAN_THEOREM: &str = "axeyum_refutation";

/// **Like [`reconstruct_int_inequality_proof`], but also renders a self-contained Lean
/// module** re-proving the refutation. A successful return means the proof was emitted,
/// kernel-checked to `False`, and rendered to externally-checkable Lean source.
///
/// # Errors
///
/// Same as [`reconstruct_int_inequality_proof`].
pub fn reconstruct_int_inequality_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let (mut ctx, proof) = build_and_gate_int_interval(arena, assertions)?;
    let false_ = {
        let f = ctx.int().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    Ok(ctx
        .kernel()
        .render_lean_module(INT_INEQ_LEAN_THEOREM, false_, proof))
}

/// Shared core: detect the interval shape, build the `False` proof over a fresh
/// [`IntReconstructCtx`], and gate it through the kernel (`infer` + `def_eq False`).
fn build_and_gate_int_interval(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<(IntReconstructCtx, ExprId), ReconstructError> {
    // Build the (ungated) `False` proof: the equal-multiplier interval first, then
    // the different-multiplier interval. Either way the kernel gate below is the sole
    // soundness authority — a builder bug surfaces as `KernelRejected`, never accept.
    let mut ctx = IntReconstructCtx::new();
    let proof = if let Some(iv) = detect_int_interval(arena, assertions) {
        ctx.build_int_interval_false(&iv)?
    } else if let Some(iv) = detect_int_interval_diff_mult(arena, assertions) {
        ctx.build_int_interval_diff_mult_false(&iv)?
    } else if let Some(iv) = detect_int_eq_bound(arena, assertions) {
        ctx.build_int_eq_bound_false(&iv)?
    } else {
        return Err(ReconstructError::UnsupportedTerm {
            term: "no single-variable integer-interval (c ≤ k·x ≤ d) refutation".to_owned(),
        });
    };
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "int_inequality".to_owned(),
            detail: format!("infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.int().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok((ctx, proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "int_inequality".to_owned(),
            detail: "integer-interval refutation did not infer to False".to_owned(),
        })
    }
}

/// Detect the single-variable integer-interval refutation shape (used by the fragment
/// classifier to route to the integer-inequality reconstructor). Returns `true` iff the
/// equal-multiplier, the different-multiplier, or the equality-and-unit-bound
/// (`k·x = b` ∧ `c ≤ x`/`x ≤ c`, real-infeasible) integer matcher matches.
#[must_use]
pub fn is_int_inequality_refutation(arena: &TermArena, assertions: &[TermId]) -> bool {
    detect_int_interval(arena, assertions).is_some()
        || detect_int_interval_diff_mult(arena, assertions).is_some()
        || detect_int_eq_bound(arena, assertions).is_some()
}
