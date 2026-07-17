//! Model-based projection (MBP) for linear real arithmetic — `mbp_lra`.
//!
//! Every test independently re-verifies the three soundness conditions of a
//! returned projection `F'`:
//!
//! 1. `M ⊨ F'` (the model satisfies every returned literal);
//! 2. `var` is structurally absent from `F'`;
//! 3. `F' ⇒ ∃var. F`, established by computing the exact Fourier–Motzkin
//!    projection `∃var. F` HERE (independently of the solver) and asserting
//!    `F' ∧ ¬(∃var. F)` is UNSAT via `check_with_lra`.
//!
//! A `None` (decline) is always sound; an unsound `Some` is a hard failure.
#![cfg(feature = "full")]
#![allow(clippy::many_single_char_names, clippy::useless_vec)]

use std::collections::BTreeMap;

use axeyum_ir::{Rational, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
use axeyum_solver::{
    CheckResult, Model, SolverConfig, check_with_lia_dpll, check_with_lra, mbp_lia, mbp_lra,
};

// ---------------------------------------------------------------------------
// Test-side LRA literal machinery (independent of the implementation under
// test), used both to build inputs and to compute the exact projection.
// ---------------------------------------------------------------------------

/// A linear expression `Σ coeff·sym + constant`.
#[derive(Clone, Default, PartialEq, Eq)]
struct Lin {
    coeffs: BTreeMap<SymbolId, Rational>,
    constant: Rational,
}

impl Lin {
    fn k(c: i64) -> Self {
        Lin {
            coeffs: BTreeMap::new(),
            constant: Rational::integer(i128::from(c)),
        }
    }
    fn v(s: SymbolId) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(s, Rational::integer(1));
        Lin {
            coeffs,
            constant: Rational::zero(),
        }
    }
    fn coeff(&self, s: SymbolId) -> Rational {
        self.coeffs.get(&s).copied().unwrap_or_else(Rational::zero)
    }
    fn norm(mut self) -> Self {
        self.coeffs.retain(|_, c| !c.is_zero());
        self
    }
    fn scale(&self, f: Rational) -> Self {
        let mut coeffs = BTreeMap::new();
        for (&s, &c) in &self.coeffs {
            coeffs.insert(s, c.checked_mul(f).expect("scale overflow"));
        }
        Lin {
            coeffs,
            constant: self.constant.checked_mul(f).expect("scale overflow"),
        }
        .norm()
    }
    fn add(&self, o: &Self) -> Self {
        let mut coeffs = self.coeffs.clone();
        for (&s, &c) in &o.coeffs {
            let e = coeffs.entry(s).or_insert_with(Rational::zero);
            *e = e.checked_add(c).expect("add overflow");
        }
        Lin {
            coeffs,
            constant: self.constant.checked_add(o.constant).expect("add overflow"),
        }
        .norm()
    }
    fn sub(&self, o: &Self) -> Self {
        self.add(&o.scale(Rational::integer(-1)))
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Rel {
    Lt,
    Le,
    Eq,
    Ne,
}

#[derive(Clone)]
struct Lit {
    expr: Lin,
    rel: Rel,
}

/// `expr < 0`.
fn lt(e: Lin) -> Lit {
    Lit {
        expr: e,
        rel: Rel::Lt,
    }
}
/// `expr ≤ 0`.
fn le(e: Lin) -> Lit {
    Lit {
        expr: e,
        rel: Rel::Le,
    }
}
/// `a = b` ⟹ `a − b = 0`.
fn eq(a: &Lin, b: &Lin) -> Lit {
    Lit {
        expr: a.sub(b),
        rel: Rel::Eq,
    }
}

/// Builds the `TermId` for a linear expression.
fn emit_lin(arena: &mut TermArena, e: &Lin) -> TermId {
    let mut acc: Option<TermId> = None;
    for (&s, &c) in &e.coeffs {
        if c.is_zero() {
            continue;
        }
        let var = arena.var(s);
        let term = if c == Rational::integer(1) {
            var
        } else {
            let kc = arena.real_const(c);
            arena.real_mul(kc, var).expect("mul")
        };
        acc = Some(match acc {
            None => term,
            Some(p) => arena.real_add(p, term).expect("add"),
        });
    }
    if !e.constant.is_zero() || acc.is_none() {
        let kc = arena.real_const(e.constant);
        acc = Some(match acc {
            None => kc,
            Some(p) => arena.real_add(p, kc).expect("add"),
        });
    }
    acc.expect("nonempty")
}

/// Builds the `TermId` for a literal `expr ⋈ 0`.
fn emit_lit(arena: &mut TermArena, lit: &Lit) -> TermId {
    let lhs = emit_lin(arena, &lit.expr);
    let zero = arena.real_const(Rational::zero());
    match lit.rel {
        Rel::Lt => arena.real_lt(lhs, zero).expect("lt"),
        Rel::Le => arena.real_le(lhs, zero).expect("le"),
        Rel::Eq => arena.eq(lhs, zero).expect("eq"),
        Rel::Ne => {
            let e = arena.eq(lhs, zero).expect("eq");
            arena.not(e).expect("not")
        }
    }
}

/// The negation literal term for `¬(expr ⋈ 0)` as a single LRA literal.
fn emit_neg_lit(arena: &mut TermArena, lit: &Lit) -> TermId {
    // ¬(e<0)=e≥0=(−e)≤0; ¬(e≤0)=e>0=(−e)<0; ¬(e=0)=e≠0; ¬(e≠0)=e=0.
    let neg = match lit.rel {
        Rel::Lt => le(lit.expr.scale(Rational::integer(-1))),
        Rel::Le => lt(lit.expr.scale(Rational::integer(-1))),
        Rel::Eq => Lit {
            expr: lit.expr.clone(),
            rel: Rel::Ne,
        },
        Rel::Ne => Lit {
            expr: lit.expr.clone(),
            rel: Rel::Eq,
        },
    };
    emit_lit(arena, &neg)
}

// ---------------------------------------------------------------------------
// Independent exact Fourier–Motzkin projection (test oracle).
// ---------------------------------------------------------------------------

/// Exact `∃var. (⋀ lits)` by Fourier–Motzkin. Panics on a disequality on `var`
/// (the disjunctive case — callers avoid it). Returns the projection literals.
fn fm_project(lits: &[Lit], var: SymbolId) -> Vec<Lit> {
    let mut passthrough = Vec::new();
    let mut lowers: Vec<(Lin, bool)> = Vec::new(); // (e, strict): var > e / var ≥ e
    let mut uppers: Vec<(Lin, bool)> = Vec::new(); // (e, strict): var < e / var ≤ e
    let mut equality: Option<Lin> = None;
    for lit in lits {
        let c = lit.expr.coeff(var);
        if c.is_zero() {
            passthrough.push(lit.clone());
            continue;
        }
        // r = expr − c·var; e = −r/c.
        let mut r = lit.expr.clone();
        r.coeffs.remove(&var);
        let r = r.norm();
        let e = r
            .scale(Rational::integer(-1))
            .scale(Rational::new(1, 1).checked_div(c).expect("inv"));
        let c_neg = c.checked_cmp(&Rational::zero()).expect("cmp") == std::cmp::Ordering::Less;
        match lit.rel {
            Rel::Eq => equality = Some(e),
            Rel::Ne => panic!("fm_project: disequality on var is disjunctive"),
            Rel::Lt => {
                if c_neg {
                    lowers.push((e, true));
                } else {
                    uppers.push((e, true));
                }
            }
            Rel::Le => {
                if c_neg {
                    lowers.push((e, false));
                } else {
                    uppers.push((e, false));
                }
            }
        }
    }
    if let Some(e) = equality {
        let mut out = passthrough;
        for lit in lits {
            let c = lit.expr.coeff(var);
            if c.is_zero() {
                continue;
            }
            let sub = substitute(lit, var, &e);
            if !trivially_true(&sub) {
                out.push(sub);
            }
        }
        return out;
    }
    let mut out = passthrough;
    for (lo, ls) in &lowers {
        for (up, us) in &uppers {
            let strict = *ls || *us;
            let resolvent = Lit {
                expr: lo.sub(up),
                rel: if strict { Rel::Lt } else { Rel::Le },
            };
            if !trivially_true(&resolvent) {
                out.push(resolvent);
            }
        }
    }
    out
}

fn substitute(lit: &Lit, var: SymbolId, repl: &Lin) -> Lit {
    let c = lit.expr.coeff(var);
    let mut base = lit.expr.clone();
    base.coeffs.remove(&var);
    let base = base.norm();
    Lit {
        expr: base.add(&repl.scale(c)),
        rel: lit.rel,
    }
}

fn trivially_true(lit: &Lit) -> bool {
    if !lit.expr.coeffs.is_empty() {
        return false;
    }
    let o = lit
        .expr
        .constant
        .checked_cmp(&Rational::zero())
        .expect("cmp");
    match lit.rel {
        Rel::Lt => o == std::cmp::Ordering::Less,
        Rel::Le => o != std::cmp::Ordering::Greater,
        Rel::Eq => o == std::cmp::Ordering::Equal,
        Rel::Ne => o != std::cmp::Ordering::Equal,
    }
}

// ---------------------------------------------------------------------------
// Independent verification of a returned F'.
// ---------------------------------------------------------------------------

/// Asserts all three soundness conditions for a returned projection.
fn check_sound(
    arena: &mut TermArena,
    formula: &[Lit],
    model: &Model,
    var: SymbolId,
    fprime: &[TermId],
) {
    // (1) M ⊨ F'.
    let asg = model.to_assignment();
    for &lit in fprime {
        assert_eq!(
            eval(arena, lit, &asg).expect("eval"),
            Value::Bool(true),
            "M must satisfy every F' literal"
        );
    }
    // (2) var absent.
    for &lit in fprime {
        assert!(!mentions(arena, lit, var), "var must not occur in F'");
    }
    // (3) F' ⇒ ∃var. F: for each exact-projection literal p, F' ∧ ¬p is UNSAT.
    let projection = fm_project(formula, var);
    for plit in &projection {
        if trivially_true(plit) {
            continue;
        }
        let not_p = emit_neg_lit(arena, plit);
        let mut asserts = fprime.to_vec();
        asserts.push(not_p);
        assert!(
            matches!(check_with_lra(arena, &asserts), Ok(CheckResult::Unsat)),
            "F' must entail each projection literal (F' ∧ ¬p UNSAT)"
        );
    }
}

fn mentions(arena: &TermArena, term: TermId, var: SymbolId) -> bool {
    match arena.node(term) {
        TermNode::Symbol(s) => *s == var,
        TermNode::App { args, .. } => {
            let args = args.clone();
            args.iter().any(|&a| mentions(arena, a, var))
        }
        _ => false,
    }
}

/// Declares `n` real symbols, returning their `SymbolId`s.
fn real_syms(arena: &mut TermArena, names: &[&str]) -> Vec<SymbolId> {
    names
        .iter()
        .map(|n| {
            let t = arena.real_var(n).expect("declare real");
            match arena.node(t) {
                TermNode::Symbol(s) => *s,
                _ => unreachable!(),
            }
        })
        .collect()
}

fn model_real(pairs: &[(SymbolId, i64)]) -> Model {
    let mut m = Model::new();
    for &(s, v) in pairs {
        m.set(s, Value::Real(Rational::integer(i128::from(v))));
    }
    m
}

// ---------------------------------------------------------------------------
// Hand-built cases.
// ---------------------------------------------------------------------------

#[test]
fn equality_elimination() {
    // F = { x = y + 1, x ≤ 5 }, eliminate x, M = { y:2, x:3 }.
    let mut arena = TermArena::new();
    let s = real_syms(&mut arena, &["x", "y"]);
    let (x, y) = (s[0], s[1]);
    let formula = vec![
        eq(&Lin::v(x), &Lin::v(y).add(&Lin::k(1))), // x = y + 1
        le(Lin::v(x).sub(&Lin::k(5))),              // x − 5 ≤ 0
    ];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_lit(&mut arena, l)).collect();
    let model = model_real(&[(x, 3), (y, 2)]);

    let fprime = mbp_lra(&mut arena, &terms, &model, x).expect("should project");
    check_sound(&mut arena, &formula, &model, x, &fprime);

    // F' must imply `y + 1 ≤ 5`, i.e. F' ∧ (y + 1 > 5) is UNSAT.
    let viol = lt(Lin::k(5).sub(&Lin::v(y).add(&Lin::k(1)))); // 5 − (y+1) < 0 ⟺ y+1 > 5
    let viol_t = emit_lit(&mut arena, &viol);
    let mut asserts = fprime.clone();
    asserts.push(viol_t);
    assert!(matches!(
        check_with_lra(&arena, &asserts),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn interval_elimination() {
    // F = { x > y, x < z } with M making y < z; eliminate x ⟹ F' implies y < z.
    let mut arena = TermArena::new();
    let s = real_syms(&mut arena, &["x", "y", "z"]);
    let (x, y, z) = (s[0], s[1], s[2]);
    // x > y ⟺ y − x < 0 ; x < z ⟺ x − z < 0.
    let formula = vec![lt(Lin::v(y).sub(&Lin::v(x))), lt(Lin::v(x).sub(&Lin::v(z)))];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_lit(&mut arena, l)).collect();
    let model = model_real(&[(x, 5), (y, 1), (z, 9)]);

    let fprime = mbp_lra(&mut arena, &terms, &model, x).expect("should project");
    check_sound(&mut arena, &formula, &model, x, &fprime);

    // F' must imply y < z, i.e. F' ∧ (z ≤ y) is UNSAT.
    let viol = le(Lin::v(z).sub(&Lin::v(y))); // z − y ≤ 0
    let viol_t = emit_lit(&mut arena, &viol);
    let mut asserts = fprime.clone();
    asserts.push(viol_t);
    assert!(matches!(
        check_with_lra(&arena, &asserts),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn multiple_bounds_resolvent() {
    // Two lowers, one upper: x > y, x > 0, x < z. M: x=5, y=2, z=10.
    let mut arena = TermArena::new();
    let s = real_syms(&mut arena, &["x", "y", "z"]);
    let (x, y, z) = (s[0], s[1], s[2]);
    let formula = vec![
        lt(Lin::v(y).sub(&Lin::v(x))), // x > y
        lt(Lin::k(0).sub(&Lin::v(x))), // x > 0
        lt(Lin::v(x).sub(&Lin::v(z))), // x < z
    ];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_lit(&mut arena, l)).collect();
    let model = model_real(&[(x, 5), (y, 2), (z, 10)]);

    let fprime = mbp_lra(&mut arena, &terms, &model, x).expect("should project");
    check_sound(&mut arena, &formula, &model, x, &fprime);
    assert!(!fprime.is_empty());
}

#[test]
fn disequality_declines() {
    // F = { x > y, x < z, x ≠ w } — interval case with a disequality.
    // Our method declines disequalities in the interval case (sound None).
    let mut arena = TermArena::new();
    let s = real_syms(&mut arena, &["x", "y", "z", "w"]);
    let (x, y, z, w) = (s[0], s[1], s[2], s[3]);
    let formula = vec![
        lt(Lin::v(y).sub(&Lin::v(x))), // x > y
        lt(Lin::v(x).sub(&Lin::v(z))), // x < z
        Lit {
            expr: Lin::v(x).sub(&Lin::v(w)),
            rel: Rel::Ne,
        }, // x ≠ w
    ];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_lit(&mut arena, l)).collect();
    // M: x=5, y=1, z=9, w=2 (all literals true: 5>1, 5<9, 5≠2).
    let model = model_real(&[(x, 5), (y, 1), (z, 9), (w, 2)]);

    assert!(
        mbp_lra(&mut arena, &terms, &model, x).is_none(),
        "interval-case disequality must decline (sound None)"
    );
}

#[test]
fn x_free_passthrough() {
    // F = { y < z, y ≤ 4 } with x not occurring; eliminating x returns F unchanged.
    let mut arena = TermArena::new();
    let s = real_syms(&mut arena, &["x", "y", "z"]);
    let (x, y, z) = (s[0], s[1], s[2]);
    let formula = vec![lt(Lin::v(y).sub(&Lin::v(z))), le(Lin::v(y).sub(&Lin::k(4)))];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_lit(&mut arena, l)).collect();
    let model = model_real(&[(x, 0), (y, 1), (z, 3)]);

    let fprime = mbp_lra(&mut arena, &terms, &model, x).expect("should project");
    check_sound(&mut arena, &formula, &model, x, &fprime);
    assert_eq!(fprime.len(), 2, "x-free literals pass through");
}

#[test]
fn model_mismatch_declines() {
    // M does NOT satisfy F (x ≤ 5 but M(x) = 9) ⟹ decline.
    let mut arena = TermArena::new();
    let s = real_syms(&mut arena, &["x", "y"]);
    let (x, y) = (s[0], s[1]);
    let formula = vec![le(Lin::v(x).sub(&Lin::k(5)))];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_lit(&mut arena, l)).collect();
    let model = model_real(&[(x, 9), (y, 0)]);
    assert!(mbp_lra(&mut arena, &terms, &model, x).is_none());
}

#[test]
fn non_lra_declines() {
    // A Boolean (non-LRA) assertion ⟹ decline.
    let mut arena = TermArena::new();
    let s = real_syms(&mut arena, &["x"]);
    let x = s[0];
    let b = arena.declare("b", Sort::Bool).expect("bool");
    let bt = arena.var(b);
    let formula = vec![bt];
    let model = {
        let mut m = Model::new();
        m.set(b, Value::Bool(true));
        m.set(x, Value::Real(Rational::zero()));
        m
    };
    assert!(mbp_lra(&mut arena, &formula, &model, x).is_none());
}

// ---------------------------------------------------------------------------
// Deterministic LCG fuzz (no rand / no clock).
// ---------------------------------------------------------------------------

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        // Numerical Recipes LCG.
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn range(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn small(&mut self) -> i64 {
        i64::try_from(self.range(7)).unwrap() - 3 // -3..=3
    }
}

#[test]
fn fuzz_soundness() {
    let mut lcg = Lcg(0x1234_5678_9abc_def0);
    let mut projected = 0u32;
    let mut declined = 0u32;

    for _ in 0..400 {
        let mut arena = TermArena::new();
        let s = real_syms(&mut arena, &["x", "y", "z"]);
        let nvars = 3;
        let nlits = 2 + usize::try_from(lcg.range(3)).unwrap(); // 2..=4 literals
        let mut formula = Vec::new();
        for _ in 0..nlits {
            // Build a random linear expr over up to 3 vars + constant.
            let mut e = Lin::k(lcg.small());
            for &sym in &s {
                let c = lcg.small();
                if c != 0 {
                    e = e.add(&Lin::v(sym).scale(Rational::integer(i128::from(c))));
                }
            }
            // Random relation (avoid disequality to keep fm_project total).
            let rel = match lcg.range(3) {
                0 => Rel::Lt,
                1 => Rel::Le,
                _ => Rel::Eq,
            };
            // Express `e REL 0`. For Eq we need `lhs = rhs`; encode `e = 0` by
            // eq(e, 0).
            let lit = match rel {
                Rel::Lt => lt(e),
                Rel::Le => le(e),
                Rel::Eq => eq(&e, &Lin::k(0)),
                Rel::Ne => unreachable!(),
            };
            formula.push(lit);
        }
        let terms: Vec<TermId> = formula.iter().map(|l| emit_lit(&mut arena, l)).collect();

        // Find a model via check_with_lra; only proceed on Sat.
        let Ok(CheckResult::Sat(model)) = check_with_lra(&arena, &terms) else {
            continue;
        };
        // Ensure the model assigns all vars (fill missing with 0 for safety).
        let mut full = model.clone();
        for &sym in &s {
            if full.get(sym).is_none() {
                full.set(sym, Value::Real(Rational::zero()));
            }
        }

        // Eliminate a deterministically-chosen variable.
        let var = s[usize::try_from(lcg.range(u64::try_from(nvars).unwrap())).unwrap()];

        match mbp_lra(&mut arena, &terms, &full, var) {
            Some(fprime) => {
                projected += 1;
                check_sound(&mut arena, &formula, &full, var, &fprime);
            }
            None => declined += 1,
        }
    }

    assert!(
        projected > 0,
        "fuzz must exercise the projection path at least once (projected={projected}, declined={declined})"
    );
}

// ===========================================================================
// Integer model-based projection — `mbp_lia` tests.
//
// Each test independently re-verifies the three soundness conditions over ℤ:
//   1. M ⊨ F';
//   2. var structurally absent from F';
//   3. F' ⇒ ∃var∈ℤ. F, established by computing the exact integer (Omega)
//      projection HERE and asserting `F' ∧ ¬p` is UNSAT over ℤ via the
//      DPLL(T) integer decider (which handles the disequalities a substituted
//      equality may introduce).
// A None decline is always sound; an unsound Some is a hard failure.
// ===========================================================================

mod int_machinery {
    use super::{Lin, Rational, SymbolId};

    /// Integer literal relation (reuses the real `Rel` shape).
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub enum IRel {
        Lt,
        Le,
        Eq,
        Ne,
    }

    #[derive(Clone)]
    pub struct ILit {
        pub expr: Lin,
        pub rel: IRel,
    }

    /// `expr < 0`.
    pub fn ilt(e: Lin) -> ILit {
        ILit {
            expr: e,
            rel: IRel::Lt,
        }
    }
    /// `expr ≤ 0`.
    pub fn ile(e: Lin) -> ILit {
        ILit {
            expr: e,
            rel: IRel::Le,
        }
    }
    /// `a = b` ⟹ `a − b = 0`.
    pub fn ieq(a: &Lin, b: &Lin) -> ILit {
        ILit {
            expr: a.sub(b),
            rel: IRel::Eq,
        }
    }
    /// `a ≠ b` ⟹ `a − b ≠ 0`.
    pub fn ine(a: &Lin, b: &Lin) -> ILit {
        ILit {
            expr: a.sub(b),
            rel: IRel::Ne,
        }
    }

    pub fn trivially_true(lit: &ILit) -> bool {
        if !lit.expr.coeffs.is_empty() {
            return false;
        }
        let o = lit
            .expr
            .constant
            .checked_cmp(&Rational::zero())
            .expect("cmp");
        match lit.rel {
            IRel::Lt => o == std::cmp::Ordering::Less,
            IRel::Le => o != std::cmp::Ordering::Greater,
            IRel::Eq => o == std::cmp::Ordering::Equal,
            IRel::Ne => o != std::cmp::Ordering::Equal,
        }
    }

    fn substitute(lit: &ILit, var: SymbolId, repl: &Lin) -> ILit {
        let c = lit.expr.coeff(var);
        let mut base = lit.expr.clone();
        base.coeffs.remove(&var);
        let base = base.norm();
        ILit {
            expr: base.add(&repl.scale(c)),
            rel: lit.rel,
        }
    }

    /// Exact integer (Omega) projection `∃var∈ℤ. (⋀ lits)` for the
    /// unit-coefficient slice. Panics on a `var` disequality (disjunctive) or a
    /// non-unit `var` coefficient — callers avoid those, mirroring the
    /// implementation's decline boundary.
    pub fn omega_project(lits: &[ILit], var: SymbolId) -> Vec<ILit> {
        let one = Rational::integer(1);
        let mut passthrough = Vec::new();
        // (e, _): folded non-strict integer bounds var ≥ e / var ≤ e.
        let mut lowers: Vec<Lin> = Vec::new();
        let mut uppers: Vec<Lin> = Vec::new();
        let mut equality: Option<Lin> = None;
        for lit in lits {
            let c = lit.expr.coeff(var);
            if c.is_zero() {
                passthrough.push(lit.clone());
                continue;
            }
            assert!(
                c == one || c == Rational::integer(-1),
                "omega_project: non-unit coefficient"
            );
            let mut r = lit.expr.clone();
            r.coeffs.remove(&var);
            let r = r.norm();
            let e = r
                .scale(Rational::integer(-1))
                .scale(one.checked_div(c).expect("inv"));
            let c_neg = c.checked_cmp(&Rational::zero()).expect("cmp") == std::cmp::Ordering::Less;
            let one_lin = Lin::k(1);
            match lit.rel {
                IRel::Eq => equality = Some(e),
                IRel::Ne => panic!("omega_project: disequality on var is disjunctive"),
                // var < e ⟹ var ≤ e-1 (c>0); var > e ⟹ var ≥ e+1 (c<0).
                IRel::Lt => {
                    if c_neg {
                        lowers.push(e.add(&one_lin));
                    } else {
                        uppers.push(e.sub(&one_lin));
                    }
                }
                // var ≤ e (c>0) / var ≥ e (c<0): already non-strict integer.
                IRel::Le => {
                    if c_neg {
                        lowers.push(e);
                    } else {
                        uppers.push(e);
                    }
                }
            }
        }
        if let Some(e) = equality {
            let mut out = passthrough;
            for lit in lits {
                let c = lit.expr.coeff(var);
                if c.is_zero() {
                    continue;
                }
                let sub = substitute(lit, var, &e);
                if !trivially_true(&sub) {
                    out.push(sub);
                }
            }
            return out;
        }
        let mut out = passthrough;
        for lo in &lowers {
            for up in &uppers {
                // lo ≤ up (integer interval non-empty iff lo ≤ up).
                let resolvent = ILit {
                    expr: lo.sub(up),
                    rel: IRel::Le,
                };
                if !trivially_true(&resolvent) {
                    out.push(resolvent);
                }
            }
        }
        out
    }
}

use int_machinery::{ILit, IRel, ieq, ile, ilt, ine, omega_project, trivially_true as itriv};

/// Builds the `TermId` for an integer linear expression `Σ coeff·sym + const`.
fn emit_lin_int(arena: &mut TermArena, e: &Lin) -> TermId {
    let mut acc: Option<TermId> = None;
    for (&s, &c) in &e.coeffs {
        if c.is_zero() {
            continue;
        }
        assert!(c.is_integer(), "integer coefficient");
        let var = arena.var(s);
        let term = if c == Rational::integer(1) {
            var
        } else {
            let kc = arena.int_const(c.numerator());
            arena.int_mul(kc, var).expect("mul")
        };
        acc = Some(match acc {
            None => term,
            Some(p) => arena.int_add(p, term).expect("add"),
        });
    }
    if !e.constant.is_zero() || acc.is_none() {
        assert!(e.constant.is_integer(), "integer constant");
        let kc = arena.int_const(e.constant.numerator());
        acc = Some(match acc {
            None => kc,
            Some(p) => arena.int_add(p, kc).expect("add"),
        });
    }
    acc.expect("nonempty")
}

/// Builds the `TermId` for an integer literal `expr ⋈ 0`.
fn emit_ilit(arena: &mut TermArena, lit: &ILit) -> TermId {
    let lhs = emit_lin_int(arena, &lit.expr);
    let zero = arena.int_const(0);
    match lit.rel {
        IRel::Lt => arena.int_lt(lhs, zero).expect("lt"),
        IRel::Le => arena.int_le(lhs, zero).expect("le"),
        IRel::Eq => arena.eq(lhs, zero).expect("eq"),
        IRel::Ne => {
            let e = arena.eq(lhs, zero).expect("eq");
            arena.not(e).expect("not")
        }
    }
}

/// The negation literal term for `¬(expr ⋈ 0)` as a single integer literal.
fn emit_neg_ilit(arena: &mut TermArena, lit: &ILit) -> TermId {
    let neg = match lit.rel {
        IRel::Lt => ile(lit.expr.scale(Rational::integer(-1))),
        IRel::Le => ilt(lit.expr.scale(Rational::integer(-1))),
        IRel::Eq => ILit {
            expr: lit.expr.clone(),
            rel: IRel::Ne,
        },
        IRel::Ne => ILit {
            expr: lit.expr.clone(),
            rel: IRel::Eq,
        },
    };
    emit_ilit(arena, &neg)
}

/// Declares `n` integer symbols.
fn int_syms(arena: &mut TermArena, names: &[&str]) -> Vec<SymbolId> {
    names
        .iter()
        .map(|n| {
            let t = arena.int_var(n).expect("declare int");
            match arena.node(t) {
                TermNode::Symbol(s) => *s,
                _ => unreachable!(),
            }
        })
        .collect()
}

fn model_int(pairs: &[(SymbolId, i64)]) -> Model {
    let mut m = Model::new();
    for &(s, v) in pairs {
        m.set(s, Value::Int(i128::from(v)));
    }
    m
}

/// Asserts all three soundness conditions for a returned integer projection,
/// using the DPLL(T) integer decider for condition (3) over ℤ.
fn check_sound_int(
    arena: &mut TermArena,
    formula: &[ILit],
    model: &Model,
    var: SymbolId,
    fprime: &[TermId],
) {
    // (1) M ⊨ F'.
    let asg = model.to_assignment();
    for &lit in fprime {
        assert_eq!(
            eval(arena, lit, &asg).expect("eval"),
            Value::Bool(true),
            "M must satisfy every F' literal"
        );
    }
    // (2) var absent.
    for &lit in fprime {
        assert!(!mentions(arena, lit, var), "var must not occur in F'");
    }
    // (3) F' ⇒ ∃var∈ℤ. F: for each exact integer-projection literal p,
    // F' ∧ ¬p is UNSAT over ℤ.
    let config = SolverConfig::default();
    let projection = omega_project(formula, var);
    for plit in &projection {
        if itriv(plit) {
            continue;
        }
        let not_p = emit_neg_ilit(arena, plit);
        let mut asserts = fprime.to_vec();
        asserts.push(not_p);
        assert!(
            matches!(
                check_with_lia_dpll(arena, &asserts, &config),
                Ok(CheckResult::Unsat)
            ),
            "F' must entail each integer projection literal (F' ∧ ¬p UNSAT over ℤ)"
        );
    }
}

#[test]
fn int_equality_elimination() {
    // F = { x = y + 1, x ≤ 5 }, eliminate x, M = { y:2, x:3 }.
    let mut arena = TermArena::new();
    let s = int_syms(&mut arena, &["xi", "yi"]);
    let (x, y) = (s[0], s[1]);
    let formula = vec![
        ieq(&Lin::v(x), &Lin::v(y).add(&Lin::k(1))), // x = y + 1
        ile(Lin::v(x).sub(&Lin::k(5))),              // x − 5 ≤ 0
    ];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_ilit(&mut arena, l)).collect();
    let model = model_int(&[(x, 3), (y, 2)]);

    let fprime = mbp_lia(&mut arena, &terms, &model, x).expect("should project");
    check_sound_int(&mut arena, &formula, &model, x, &fprime);

    // F' must imply `y + 1 ≤ 5`, i.e. F' ∧ (y + 1 > 5 ⟺ y + 1 ≥ 6) is UNSAT.
    let config = SolverConfig::default();
    let viol = ile(Lin::k(6).sub(&Lin::v(y).add(&Lin::k(1)))); // 6 − (y+1) ≤ 0 ⟺ y ≥ 5
    let viol_t = emit_ilit(&mut arena, &viol);
    let mut asserts = fprime.clone();
    asserts.push(viol_t);
    assert!(matches!(
        check_with_lia_dpll(&mut arena, &asserts, &config),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn int_interval_resolvent() {
    // F = { x ≥ y, x ≤ z } integer bounds; eliminate x ⟹ F' implies y ≤ z.
    let mut arena = TermArena::new();
    let s = int_syms(&mut arena, &["xi", "yi", "zi"]);
    let (x, y, z) = (s[0], s[1], s[2]);
    // x ≥ y ⟺ y − x ≤ 0 ; x ≤ z ⟺ x − z ≤ 0.
    let formula = vec![
        ile(Lin::v(y).sub(&Lin::v(x))),
        ile(Lin::v(x).sub(&Lin::v(z))),
    ];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_ilit(&mut arena, l)).collect();
    let model = model_int(&[(x, 5), (y, 1), (z, 9)]);

    let fprime = mbp_lia(&mut arena, &terms, &model, x).expect("should project");
    check_sound_int(&mut arena, &formula, &model, x, &fprime);

    // F' must imply y ≤ z, i.e. F' ∧ (z < y ⟺ z − y ≤ -1) is UNSAT.
    let config = SolverConfig::default();
    let viol = ile(Lin::v(z).sub(&Lin::v(y)).add(&Lin::k(1))); // z − y + 1 ≤ 0 ⟺ z < y
    let viol_t = emit_ilit(&mut arena, &viol);
    let mut asserts = fprime.clone();
    asserts.push(viol_t);
    assert!(matches!(
        check_with_lia_dpll(&mut arena, &asserts, &config),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn int_multiple_bounds_resolvent() {
    // Two lowers, one upper: x ≥ y, x ≥ 1, x ≤ z. M: x=5, y=2, z=10.
    let mut arena = TermArena::new();
    let s = int_syms(&mut arena, &["xi", "yi", "zi"]);
    let (x, y, z) = (s[0], s[1], s[2]);
    let formula = vec![
        ile(Lin::v(y).sub(&Lin::v(x))), // x ≥ y
        ile(Lin::k(1).sub(&Lin::v(x))), // x ≥ 1
        ile(Lin::v(x).sub(&Lin::v(z))), // x ≤ z
    ];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_ilit(&mut arena, l)).collect();
    let model = model_int(&[(x, 5), (y, 2), (z, 10)]);

    let fprime = mbp_lia(&mut arena, &terms, &model, x).expect("should project");
    check_sound_int(&mut arena, &formula, &model, x, &fprime);
    assert!(!fprime.is_empty());
}

#[test]
fn int_strict_gap_respects_integrality() {
    // Integer-specific: x > y AND x < y+2 forces x = y+1 over ℤ (the only
    // integer in the open interval (y, y+2)). Over the REALS the interval is
    // wide; over ℤ the projection (∃x∈ℤ) is simply TRUE (always an integer
    // x=y+1 exists), so F' must be satisfiable and entail the exact integer
    // projection. M: x=3, y=2.
    let mut arena = TermArena::new();
    let s = int_syms(&mut arena, &["xi", "yi"]);
    let (x, y) = (s[0], s[1]);
    let formula = vec![
        ilt(Lin::v(y).sub(&Lin::v(x))),                 // x > y ⟺ y − x < 0
        ilt(Lin::v(x).sub(&Lin::v(y)).sub(&Lin::k(2))), // x < y+2 ⟺ x − y − 2 < 0
    ];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_ilit(&mut arena, l)).collect();
    let model = model_int(&[(x, 3), (y, 2)]);

    let fprime = mbp_lia(&mut arena, &terms, &model, x).expect("should project");
    // The strict bounds fold to x ≥ y+1 and x ≤ y+1, cross-feasibility
    // y+1 ≤ y+1 i.e. 0 ≤ 0 (trivially true and dropped). Condition (3) over ℤ
    // is verified inside check_sound_int.
    check_sound_int(&mut arena, &formula, &model, x, &fprime);
}

#[test]
fn int_nonunit_declines() {
    // F = { 2x = y, 2x ≤ z } — non-unit coefficient on x. The slice declines
    // (the Cooper divisibility boundary): returns None, soundly.
    let mut arena = TermArena::new();
    let s = int_syms(&mut arena, &["xi", "yi", "zi"]);
    let (x, y, z) = (s[0], s[1], s[2]);
    let two_x = Lin::v(x).scale(Rational::integer(2));
    let formula = vec![
        ieq(&two_x, &Lin::v(y)),    // 2x = y
        ile(two_x.sub(&Lin::v(z))), // 2x − z ≤ 0
    ];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_ilit(&mut arena, l)).collect();
    // M: x=3, y=6, z=10 (2·3=6, 6≤10).
    let model = model_int(&[(x, 3), (y, 6), (z, 10)]);

    assert!(
        mbp_lia(&mut arena, &terms, &model, x).is_none(),
        "non-unit coefficient must decline (sound None)"
    );
}

#[test]
fn int_disequality_declines() {
    // Interval case with a disequality on x → declines (sound None).
    let mut arena = TermArena::new();
    let s = int_syms(&mut arena, &["xi", "yi", "zi", "wi"]);
    let (x, y, z, w) = (s[0], s[1], s[2], s[3]);
    let formula = vec![
        ile(Lin::v(y).sub(&Lin::v(x))), // x ≥ y
        ile(Lin::v(x).sub(&Lin::v(z))), // x ≤ z
        ine(&Lin::v(x), &Lin::v(w)),    // x ≠ w
    ];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_ilit(&mut arena, l)).collect();
    let model = model_int(&[(x, 5), (y, 1), (z, 9), (w, 2)]);

    assert!(
        mbp_lia(&mut arena, &terms, &model, x).is_none(),
        "interval-case disequality must decline (sound None)"
    );
}

#[test]
fn int_x_free_passthrough() {
    // x not occurring: eliminating x returns F unchanged.
    let mut arena = TermArena::new();
    let s = int_syms(&mut arena, &["xi", "yi", "zi"]);
    let (x, y, z) = (s[0], s[1], s[2]);
    let formula = vec![
        ilt(Lin::v(y).sub(&Lin::v(z))),
        ile(Lin::v(y).sub(&Lin::k(4))),
    ];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_ilit(&mut arena, l)).collect();
    let model = model_int(&[(x, 0), (y, 1), (z, 3)]);

    let fprime = mbp_lia(&mut arena, &terms, &model, x).expect("should project");
    check_sound_int(&mut arena, &formula, &model, x, &fprime);
    assert_eq!(fprime.len(), 2, "x-free literals pass through");
}

#[test]
fn int_model_mismatch_declines() {
    // M does NOT satisfy F (x ≤ 5 but M(x) = 9) ⟹ decline.
    let mut arena = TermArena::new();
    let s = int_syms(&mut arena, &["xi", "yi"]);
    let (x, y) = (s[0], s[1]);
    let formula = vec![ile(Lin::v(x).sub(&Lin::k(5)))];
    let terms: Vec<TermId> = formula.iter().map(|l| emit_ilit(&mut arena, l)).collect();
    let model = model_int(&[(x, 9), (y, 0)]);
    assert!(mbp_lia(&mut arena, &terms, &model, x).is_none());
}

#[test]
fn int_non_lia_declines() {
    // A Boolean (non-LIA) assertion ⟹ decline.
    let mut arena = TermArena::new();
    let s = int_syms(&mut arena, &["xi"]);
    let x = s[0];
    let b = arena.declare("bi", Sort::Bool).expect("bool");
    let bt = arena.var(b);
    let formula = vec![bt];
    let model = {
        let mut m = Model::new();
        m.set(b, Value::Bool(true));
        m.set(x, Value::Int(0));
        m
    };
    assert!(mbp_lia(&mut arena, &formula, &model, x).is_none());
}

#[test]
fn fuzz_soundness_int() {
    // Deterministic LCG fuzz over small integer conjunctions. Whenever mbp_lia
    // returns Some(F'), independently assert all three conditions over ℤ. Zero
    // unsound projections; None is always acceptable.
    let mut lcg = Lcg(0x0bad_f00d_dead_beef);
    let mut projected = 0u32;
    let mut declined = 0u32;
    let config = SolverConfig::default();

    for _ in 0..400 {
        let mut arena = TermArena::new();
        let s = int_syms(&mut arena, &["xi", "yi", "zi"]);
        let nvars = 3;
        let nlits = 2 + usize::try_from(lcg.range(3)).unwrap(); // 2..=4 literals
        let mut formula: Vec<ILit> = Vec::new();
        for _ in 0..nlits {
            // Random linear expr; keep x's coefficient in {-1,0,1} most of the
            // time so the unit slice is exercised, but allow non-unit to test
            // the decline path too.
            let mut e = Lin::k(lcg.small());
            for &sym in &s {
                let c = lcg.small();
                if c != 0 {
                    e = e.add(&Lin::v(sym).scale(Rational::integer(i128::from(c))));
                }
            }
            // Avoid disequality so omega_project stays total for the verifier.
            let rel = match lcg.range(3) {
                0 => IRel::Lt,
                1 => IRel::Le,
                _ => IRel::Eq,
            };
            let lit = match rel {
                IRel::Lt => ilt(e),
                IRel::Le => ile(e),
                IRel::Eq => ieq(&e, &Lin::k(0)),
                IRel::Ne => unreachable!(),
            };
            formula.push(lit);
        }
        let terms: Vec<TermId> = formula.iter().map(|l| emit_ilit(&mut arena, l)).collect();

        // Find an integer model via the integer decider; only proceed on Sat.
        let Ok(CheckResult::Sat(model)) = check_with_lia_dpll(&mut arena, &terms, &config) else {
            continue;
        };
        let mut full = model.clone();
        for &sym in &s {
            if full.get(sym).is_none() {
                full.set(sym, Value::Int(0));
            }
        }

        let var = s[usize::try_from(lcg.range(u64::try_from(nvars).unwrap())).unwrap()];

        match mbp_lia(&mut arena, &terms, &full, var) {
            Some(fprime) => {
                projected += 1;
                check_sound_int(&mut arena, &formula, &full, var, &fprime);
            }
            None => declined += 1,
        }
    }

    assert!(
        projected > 0,
        "int fuzz must exercise the projection path at least once (projected={projected}, declined={declined})"
    );
}
