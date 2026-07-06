//! Word-level (string/sequence) refutation → kernel-checked Lean `False`
//! (P3.7 strings fragment).
//!
//! The in-tree word checker ([`axeyum_strings::refute_word_equations`], ADR-0053
//! T-B.7) certifies a string system `unsat` behind an independent re-derivation,
//! and [`crate::word_conflict_alethe`] already emits a self-validating **Alethe**
//! certificate for it. This module reconstructs that refutation over the **string
//! prelude** ([`StringPrelude`], the free monoid `Str = List Char`): it builds a
//! Lean proof term whose type is `False`, `infer`-checks it, and `def_eq`-compares
//! it to the prelude's `False`. A wrong reconstruction fails that gate and is
//! declined — never a wrong `False`.
//!
//! # What this slice covers — and what stays declined
//!
//! Two conflict classes are reconstructed, each by a self-evident argument the
//! kernel then re-checks by ι-computation:
//!
//! - **Contradicted disequality** (`a ≠ b` whose cited premises place `a` and `b`
//!   in one class): the premise equalities are hypotheses `hᵢ : Eq Str L(sᵢ) L(tᵢ)`
//!   over translated terms (string vars → opaque `Str` constants; literals →
//!   concrete `cons`-chains; `str.++` → the opaque `append`), a `trans`/`symm`
//!   chain along the union-find path derives `Eq Str L(a) L(b)`, and the
//!   disequality hypothesis `¬(Eq Str L(a) L(b))` applied to it is `False`. This is
//!   fully general over the premise chain (no string semantics needed — pure `Eq`
//!   congruence over opaque terms).
//!
//! - **Constant clash with concrete clashing members** (`x = "abc" ∧ x = "abd"`
//!   and its chained kin): the chain derives `Eq Str A B` between two **concrete**
//!   constant strings that differ at position `k` on two distinct code points, and
//!   the projection `g = is_{cA} ∘ head ∘ tailᵏ` (a fixed `Str.rec`/`Char.rec`
//!   application) ι-reduces `g A ↝ true`, `g B ↝ false`. A single `congrArg g`
//!   over the equality plus the `Bool.true ≠ Bool.false` discriminator closes to
//!   `False` — kernel-computed, no assumed axiom beyond the input equalities.
//!
//! **Declined (documented follow-ups):** a clash whose members share a *variable*
//! prefix that must be **cancelled** (`x ++ "a" = x ++ "b"`) — needs `append`'s
//! recursive definition and free-monoid left-cancellation; the **self-loop /
//! length** family (`x = "a" ++ x`) — needs the size-measure length argument; and
//! the **regex-derivative emptiness** certificates. Each is a safe decline to
//! `unknown` (an `Err` from this reconstructor), never a wrong verdict.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use axeyum_ir::{Assignment, Op, Sort, TermArena, TermId, TermNode, Value, eval};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, NameId, StringPrelude, build_logic_prelude,
    build_string_prelude,
};
use axeyum_strings::{RefuteOutcome, SearchBudget, refute_word_equations};

use crate::reconstruct::ReconstructError;

/// The rendered theorem name for a word-clash refutation module.
const WORD_LEAN_THEOREM: &str = "axeyum_word_refutation";

/// A generous, deadline-free node budget for the entry refutation gate (the
/// refutation itself is non-recursive and hard-bounded internally).
fn budget() -> SearchBudget {
    SearchBudget::new(50_000_000)
}

/// Whether `assertions` are a **pure word-equation shape** — every assertion is a
/// `Seq`-sorted equality `(= a b)` or disequality `(not (= a b))`, and there is at
/// least one — so the [`crate::reconstruct::scan_proof_fragment`] classifier can
/// route them here without a (mutable-arena) refutation call.
///
/// A non-word assertion (any other head, or a non-`Seq` equality) makes this
/// `false`, so a mixed problem is never misrouted; the real `unsat` gate is
/// [`refute_word_equations`], run inside [`reconstruct_word_clash_to_lean_module`].
#[must_use]
pub fn is_word_equation_shape(arena: &TermArena, assertions: &[TermId]) -> bool {
    if assertions.is_empty() {
        return false;
    }
    let mut saw = false;
    for &t in assertions {
        match classify_literal(arena, t) {
            Some(_) => saw = true,
            None => return false,
        }
    }
    saw
}

/// A single word literal: a `Seq` equality or disequality.
enum Literal {
    Eq(TermId, TermId),
    Diseq(TermId, TermId),
}

/// Classify a top-level assertion as a `Seq` equality / disequality, or `None`.
fn classify_literal(arena: &TermArena, t: TermId) -> Option<Literal> {
    match arena.node(t) {
        TermNode::App { op: Op::Eq, args } if args.len() == 2 && is_seq(arena, args[0]) => {
            Some(Literal::Eq(args[0], args[1]))
        }
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => match arena.node(args[0]) {
            TermNode::App {
                op: Op::Eq,
                args: inner,
            } if inner.len() == 2 && is_seq(arena, inner[0]) => {
                Some(Literal::Diseq(inner[0], inner[1]))
            }
            _ => None,
        },
        _ => None,
    }
}

fn is_seq(arena: &TermArena, t: TermId) -> bool {
    matches!(arena.sort_of(t), Sort::Seq(_))
}

/// A word system: the equality pairs and the disequality pairs.
type WordSystem = (Vec<(TermId, TermId)>, Vec<(TermId, TermId)>);

/// Extract the `(equalities, disequalities)` word system from `assertions`.
fn extract_system(arena: &TermArena, assertions: &[TermId]) -> Option<WordSystem> {
    let mut eqs = Vec::new();
    let mut diseqs = Vec::new();
    for &t in assertions {
        match classify_literal(arena, t)? {
            Literal::Eq(a, b) => eqs.push((a, b)),
            Literal::Diseq(a, b) => diseqs.push((a, b)),
        }
    }
    Some((eqs, diseqs))
}

/// Reconstruct a word-level refutation of `assertions` to a self-contained,
/// kernel-checked Lean module, or a [`ReconstructError`] if this slice declines.
///
/// The refutation is first re-established (and its premise core computed) by the
/// independent [`refute_word_equations`]; the reconstruction then targets a
/// contradicted disequality or a concrete constant clash (see the module docs) and
/// builds a `False` proof gated by the kernel (`infer` + `def_eq False`).
///
/// # Errors
///
/// - [`ReconstructError::UnsupportedTerm`] — no word refutation, no
///   reconstructable target for this slice (a cancellation/self-loop/regex shape),
///   or a term outside the renderable fragment;
/// - [`ReconstructError::KernelRejected`] — the assembled proof did not `infer` to
///   `False` (an emitter bug, declined — never a wrong certificate).
pub fn reconstruct_word_clash_to_lean_module(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let (equalities, disequalities) =
        extract_system(arena, assertions).ok_or_else(|| ReconstructError::UnsupportedTerm {
            term: "assertions are not a pure word-equation system".to_owned(),
        })?;

    // (1) The sole `unsat` gate: an independently re-checked refutation and its
    // minimal premise core. Anything else is a safe decline to `unknown`.
    let RefuteOutcome::Unsat { premises } =
        refute_word_equations(arena, &equalities, &disequalities, &budget())
    else {
        return Err(ReconstructError::UnsupportedTerm {
            term: "no independently-checked word refutation for these assertions".to_owned(),
        });
    };
    let cited: Vec<(TermId, TermId)> = premises.iter().map(|&i| equalities[i]).collect();

    // (2) Union-find over the cited premises + adjacency for chain paths.
    let mut uf = MiniUf::default();
    let mut adj: BTreeMap<TermId, Vec<(TermId, usize)>> = BTreeMap::new();
    for (idx, &(a, b)) in cited.iter().enumerate() {
        uf.union(a, b);
        adj.entry(a).or_default().push((b, idx));
        adj.entry(b).or_default().push((a, idx));
    }

    // (3) Pick a target: a contradicted disequality, else a concrete constant
    // clash between two provably-equal endpoints.
    if let Some((a, b)) = disequalities
        .iter()
        .copied()
        .find(|&(a, b)| uf.find(a) == uf.find(b))
    {
        return build_disequality_module(arena, &cited, &adj, a, b);
    }
    if let Some((u, v, pos)) = find_concrete_clash(arena, &cited, &uf) {
        return build_clash_module(arena, &cited, &adj, u, v, pos);
    }
    Err(ReconstructError::UnsupportedTerm {
        term: "word refutation is a cancellation/self-loop/length shape this slice defers"
            .to_owned(),
    })
}

/// Find two endpoints of the cited premises that are provably equal yet evaluate
/// to concrete constant strings differing at a position with **distinct code
/// points**, returning `(u, v, position)`. Length-only clashes (one a prefix of
/// the other) are declined here (the self-loop/length family).
fn find_concrete_clash(
    arena: &mut TermArena,
    cited: &[(TermId, TermId)],
    uf: &MiniUf,
) -> Option<(TermId, TermId, usize)> {
    let mut endpoints: BTreeSet<TermId> = BTreeSet::new();
    for &(a, b) in cited {
        endpoints.insert(a);
        endpoints.insert(b);
    }
    let concrete: Vec<(TermId, Vec<u128>)> = endpoints
        .iter()
        .filter_map(|&t| seq_codepoints(arena, t).map(|v| (t, v)))
        .collect();
    for i in 0..concrete.len() {
        for j in (i + 1)..concrete.len() {
            let (u, ref uv) = concrete[i];
            let (v, ref vv) = concrete[j];
            if uf.find(u) != uf.find(v) {
                continue;
            }
            if let Some(pos) = uv.iter().zip(vv.iter()).position(|(x, y)| x != y) {
                return Some((u, v, pos));
            }
        }
    }
    None
}

/// The concrete code-point sequence of `t` (each element a bit-vector value),
/// or `None` if `t` does not evaluate to a closed sequence of bit-vector values.
fn seq_codepoints(arena: &TermArena, t: TermId) -> Option<Vec<u128>> {
    let Ok(Value::Seq(elems)) = eval(arena, t, &Assignment::new()) else {
        return None;
    };
    elems.iter().map(value_codepoint).collect()
}

/// The unsigned code point of a scalar bit-vector [`Value`], or `None`.
fn value_codepoint(v: &Value) -> Option<u128> {
    match v {
        Value::Bv { value, .. } => Some(*value),
        Value::WideBv(w) => Some(w.to_u128()),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The reconstruction context: a kernel with the logic + string prelude.
// ---------------------------------------------------------------------------

/// A kernel seeded with the logical + string prelude, plus deterministic maps
/// from IR sequence/element terms to their kernel encodings.
struct WordCtx {
    kernel: Kernel,
    sp: StringPrelude,
    /// Distinct code point → alphabet index (`Char.c<idx>`).
    char_index: BTreeMap<u128, usize>,
    /// Sequence variable [`TermId`] → opaque `Str` axiom name.
    seq_vars: BTreeMap<TermId, NameId>,
    /// Element variable [`TermId`] → opaque `Char` axiom name.
    elem_vars: BTreeMap<TermId, NameId>,
    /// Translation memo: IR sequence term → its `Str` expression.
    translate_memo: BTreeMap<TermId, ExprId>,
    next_id: u64,
}

impl WordCtx {
    /// A fresh context whose alphabet has one `Char` constructor per distinct code
    /// point in `codepoints` (deterministic, ascending order).
    fn new(codepoints: &BTreeSet<u128>) -> Self {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel);
        let sp = build_string_prelude(&mut kernel, logic, codepoints.len());
        let char_index = codepoints
            .iter()
            .enumerate()
            .map(|(i, &c)| (c, i))
            .collect();
        Self {
            kernel,
            sp,
            char_index,
            seq_vars: BTreeMap::new(),
            elem_vars: BTreeMap::new(),
            translate_memo: BTreeMap::new(),
            next_id: 0,
        }
    }

    fn fresh_name(&mut self, base: &str) -> NameId {
        let anon = self.kernel.anon();
        let ns = self.kernel.name_str(anon, "axeyum.reconstruct.word");
        let id = self.next_id;
        self.next_id += 1;
        let with_base = self.kernel.name_str(ns, base);
        self.kernel.name_num(with_base, id)
    }

    /// Declare a fresh axiom `_ : ty` and return its `Const` proof/term.
    fn axiom(&mut self, base: &str, ty: ExprId) -> Result<ExprId, ReconstructError> {
        let name = self.fresh_name(base);
        self.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "word".to_owned(),
                detail: format!("axiom {base} did not admit: {e:?}"),
            })?;
        Ok(self.kernel.const_(name, vec![]))
    }

    /// The opaque `Str` constant for a sequence variable (declared lazily).
    fn seq_var(&mut self, t: TermId) -> Result<ExprId, ReconstructError> {
        if let Some(&name) = self.seq_vars.get(&t) {
            return Ok(self.kernel.const_(name, vec![]));
        }
        let str_ty = self.sp.str_const(&mut self.kernel);
        let name = self.fresh_name("s");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty: str_ty,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "word".to_owned(),
                detail: format!("seq var axiom did not admit: {e:?}"),
            })?;
        self.seq_vars.insert(t, name);
        Ok(self.kernel.const_(name, vec![]))
    }

    /// The opaque `Char` constant for an element variable (declared lazily).
    fn elem_var(&mut self, t: TermId) -> Result<ExprId, ReconstructError> {
        if let Some(&name) = self.elem_vars.get(&t) {
            return Ok(self.kernel.const_(name, vec![]));
        }
        let char_ty = self.sp.char_const(&mut self.kernel);
        let name = self.fresh_name("e");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty: char_ty,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "word".to_owned(),
                detail: format!("elem var axiom did not admit: {e:?}"),
            })?;
        self.elem_vars.insert(t, name);
        Ok(self.kernel.const_(name, vec![]))
    }

    /// A concrete code-point sequence as a flat `cons`-chain over the alphabet.
    fn concrete_str(&mut self, codepoints: &[u128]) -> Result<ExprId, ReconstructError> {
        let mut acc = self.sp.nil(&mut self.kernel);
        for &cp in codepoints.iter().rev() {
            let idx =
                *self
                    .char_index
                    .get(&cp)
                    .ok_or_else(|| ReconstructError::UnsupportedTerm {
                        term: format!("code point {cp} missing from alphabet"),
                    })?;
            let ch = self.sp.char(&mut self.kernel, idx);
            acc = self.sp.cons(&mut self.kernel, ch, acc);
        }
        Ok(acc)
    }

    /// Translate an IR `Seq`-sorted term to its `Str` expression. A term that
    /// evaluates to a **concrete** constant string is emitted as a flat `cons`-chain
    /// (so `head`/`tail` ι-reduce through it); otherwise it is built structurally
    /// (`seq.empty → nil`, `seq.unit → cons`, `str.++ → opaque append`, var →
    /// opaque `Str`).
    fn translate(&mut self, arena: &TermArena, t: TermId) -> Result<ExprId, ReconstructError> {
        if let Some(&e) = self.translate_memo.get(&t) {
            return Ok(e);
        }
        // Prefer the concrete flat encoding when the whole term evaluates closed.
        let out = if let Some(cps) = seq_codepoints(arena, t) {
            self.concrete_str(&cps)?
        } else {
            self.translate_structural(arena, t)?
        };
        self.translate_memo.insert(t, out);
        Ok(out)
    }

    fn translate_structural(
        &mut self,
        arena: &TermArena,
        t: TermId,
    ) -> Result<ExprId, ReconstructError> {
        match arena.node(t) {
            TermNode::Symbol(_) if is_seq(arena, t) => self.seq_var(t),
            TermNode::App { op, args } => match op {
                Op::SeqEmpty(_) if args.is_empty() => Ok(self.sp.nil(&mut self.kernel)),
                Op::SeqUnit if args.len() == 1 => {
                    let ch = self.translate_elem(arena, args[0])?;
                    let nil = self.sp.nil(&mut self.kernel);
                    Ok(self.sp.cons(&mut self.kernel, ch, nil))
                }
                Op::SeqConcat if args.len() == 2 => {
                    let a = self.translate(arena, args[0])?;
                    let b = self.translate(arena, args[1])?;
                    Ok(self.sp.append_app(&mut self.kernel, a, b))
                }
                _ => Err(ReconstructError::UnsupportedTerm {
                    term: "sequence term outside the renderable fragment".to_owned(),
                }),
            },
            _ => Err(ReconstructError::UnsupportedTerm {
                term: "sequence term outside the renderable fragment".to_owned(),
            }),
        }
    }

    /// Translate a scalar element term (inside `seq.unit`): a concrete bit-vector
    /// value is the matching `Char` constructor; anything else is an opaque `Char`.
    fn translate_elem(&mut self, arena: &TermArena, e: TermId) -> Result<ExprId, ReconstructError> {
        if let Ok(v) = eval(arena, e, &Assignment::new())
            && let Some(cp) = value_codepoint(&v)
            && let Some(&idx) = self.char_index.get(&cp)
        {
            return Ok(self.sp.char(&mut self.kernel, idx));
        }
        self.elem_var(e)
    }

    // ---- Eq/congr/discriminator term builders (carrier universe = 1) --------

    fn level_one(&mut self) -> axeyum_lean_kernel::LevelId {
        let z = self.kernel.level_zero();
        self.kernel.level_succ(z)
    }

    /// `Eq ty x y` for a `Sort 1` carrier `ty`.
    fn mk_eq(&mut self, ty: ExprId, x: ExprId, y: ExprId) -> ExprId {
        let lvl = self.level_one();
        let eq = self.kernel.const_(self.sp.logic.eq, vec![lvl]);
        let e = self.kernel.app(eq, ty);
        let e = self.kernel.app(e, x);
        self.kernel.app(e, y)
    }

    fn eq_refl(&mut self, ty: ExprId, a: ExprId) -> ExprId {
        let lvl = self.level_one();
        let refl = self.kernel.const_(self.sp.logic.eq_refl, vec![lvl]);
        let e = self.kernel.app(refl, ty);
        self.kernel.app(e, a)
    }

    /// `Eq.rec` transport over a `Sort 1` carrier into a `Prop` motive.
    fn eq_rec(
        &mut self,
        ty: ExprId,
        p: ExprId,
        motive: ExprId,
        refl_case: ExprId,
        q: ExprId,
        h: ExprId,
    ) -> ExprId {
        let z = self.kernel.level_zero();
        let one = self.level_one();
        let rec = self.kernel.const_(self.sp.logic.eq_rec, vec![z, one]);
        let e = self.kernel.app(rec, ty);
        let e = self.kernel.app(e, p);
        let e = self.kernel.app(e, motive);
        let e = self.kernel.app(e, refl_case);
        let e = self.kernel.app(e, q);
        self.kernel.app(e, h)
    }

    /// `Eq.symm`: `h : Eq ty a b ⇒ Eq ty b a`.
    fn eq_symm(&mut self, ty: ExprId, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let anon = self.kernel.anon();
        let motive = {
            let x1 = self.kernel.bvar(1);
            let eq_x_a = self.mk_eq(ty, x1, a);
            let x0 = self.kernel.bvar(0);
            let eq_a_x = self.mk_eq(ty, a, x0);
            let inner = self.kernel.lam(anon, eq_a_x, eq_x_a, BinderInfo::Default);
            self.kernel.lam(anon, ty, inner, BinderInfo::Default)
        };
        let refl_case = self.eq_refl(ty, a);
        self.eq_rec(ty, a, motive, refl_case, b, h)
    }

    /// `Eq.trans`: `h1 : Eq ty a b`, `h2 : Eq ty b c ⇒ Eq ty a c`.
    fn eq_trans(
        &mut self,
        ty: ExprId,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let anon = self.kernel.anon();
        let motive = {
            let x1 = self.kernel.bvar(1);
            let eq_a_x = self.mk_eq(ty, a, x1);
            let x0 = self.kernel.bvar(0);
            let eq_b_x = self.mk_eq(ty, b, x0);
            let inner = self.kernel.lam(anon, eq_b_x, eq_a_x, BinderInfo::Default);
            self.kernel.lam(anon, ty, inner, BinderInfo::Default)
        };
        self.eq_rec(ty, b, motive, h1, c, h2)
    }

    /// `congrArg`: given `f : dom → cod` and `h : Eq dom x y`, build
    /// `Eq cod (f x) (f y)` (both carriers `Sort 1`).
    fn congr_arg(
        &mut self,
        dom: ExprId,
        cod: ExprId,
        f: ExprId,
        x: ExprId,
        y: ExprId,
        h: ExprId,
    ) -> ExprId {
        let anon = self.kernel.anon();
        let fx = self.kernel.app(f, x);
        let motive = {
            let z1 = self.kernel.bvar(1);
            let fz = self.kernel.app(f, z1);
            let eq_fx_fz = self.mk_eq(cod, fx, fz);
            let z0 = self.kernel.bvar(0);
            let eq_x_z = self.mk_eq(dom, x, z0);
            let inner = self.kernel.lam(anon, eq_x_z, eq_fx_fz, BinderInfo::Default);
            self.kernel.lam(anon, dom, inner, BinderInfo::Default)
        };
        let refl_case = self.eq_refl(cod, fx);
        self.eq_rec(dom, x, motive, refl_case, y, h)
    }

    /// Given `lhs : Bool` that ι-reduces to `Bool.false` and `h : Eq Bool lhs
    /// Bool.true`, build `False` via the `Bool.true ≠ Bool.false` discriminator.
    fn bool_true_ne_false(&mut self, lhs: ExprId, h: ExprId) -> ExprId {
        let anon = self.kernel.anon();
        let bool_const = self.kernel.const_(self.sp.logic.bool_, vec![]);
        let prop = self.kernel.sort_zero();
        let true_const = self.kernel.const_(self.sp.logic.true_, vec![]);
        let false_const = self.kernel.const_(self.sp.logic.false_, vec![]);
        let z = self.kernel.level_zero();
        let one = self.level_one();
        let rec = self.kernel.const_(self.sp.logic.bool_rec, vec![one]);
        let motive = self.kernel.lam(anon, bool_const, prop, BinderInfo::Default);
        let discr = {
            let e = self.kernel.app(rec, motive);
            let e = self.kernel.app(e, false_const); // minor for Bool.true
            let e = self.kernel.app(e, true_const); // minor for Bool.false
            let b = self.kernel.bvar(0);
            let body = self.kernel.app(e, b);
            self.kernel.lam(anon, bool_const, body, BinderInfo::Default)
        };
        let bool_true = self.kernel.const_(self.sp.logic.bool_true, vec![]);
        let transport_motive = {
            let x = self.kernel.bvar(1);
            let discr_x = self.kernel.app(discr, x);
            let eq = self.kernel.const_(self.sp.logic.eq, vec![one]);
            let x0 = self.kernel.bvar(0);
            let eq_lhs_x = {
                let e = self.kernel.app(eq, bool_const);
                let e = self.kernel.app(e, lhs);
                self.kernel.app(e, x0)
            };
            let inner = self
                .kernel
                .lam(anon, eq_lhs_x, discr_x, BinderInfo::Default);
            self.kernel
                .lam(anon, bool_const, inner, BinderInfo::Default)
        };
        let refl_case = self.kernel.const_(self.sp.logic.true_intro, vec![]);
        let rec_eq = self.kernel.const_(self.sp.logic.eq_rec, vec![z, one]);
        let e = self.kernel.app(rec_eq, bool_const);
        let e = self.kernel.app(e, lhs);
        let e = self.kernel.app(e, transport_motive);
        let e = self.kernel.app(e, refl_case);
        let e = self.kernel.app(e, bool_true);
        self.kernel.app(e, h)
    }

    /// Gate the assembled proof through the kernel (`infer` + `def_eq False`) and
    /// render the self-contained Lean module (with the `Char`/`Str`/`Bool`
    /// inductives so an external Lean regenerates their recursors *with* ι).
    fn gate_and_render(&mut self, proof: ExprId) -> Result<String, ReconstructError> {
        let inferred = self
            .kernel
            .infer(proof)
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "word".to_owned(),
                detail: format!("infer failed: {e:?}"),
            })?;
        let false_const = self.kernel.const_(self.sp.logic.false_, vec![]);
        if !self.kernel.def_eq(inferred, false_const) {
            return Err(ReconstructError::KernelRejected {
                rule: "word".to_owned(),
                detail: "word refutation did not infer to False".to_owned(),
            });
        }
        let inductives = [self.sp.char_ind, self.sp.str_ind, self.sp.logic.bool_];
        let false_goal = self.kernel.const_(self.sp.logic.false_, vec![]);
        Ok(self.kernel.render_lean_module_with_inductives(
            WORD_LEAN_THEOREM,
            false_goal,
            proof,
            &inductives,
        ))
    }
}

// ---------------------------------------------------------------------------
// Chain building over the cited premise graph.
// ---------------------------------------------------------------------------

/// Build a proof `Eq Str L(u) L(v)` by a `trans`/`symm` chain along the union-find
/// path from `u` to `v` in the cited-premise graph, declaring one hypothesis axiom
/// per premise edge used. `None` if no path exists (should not happen when `u`, `v`
/// are provably equal).
fn build_chain(
    ctx: &mut WordCtx,
    arena: &TermArena,
    cited: &[(TermId, TermId)],
    adj: &BTreeMap<TermId, Vec<(TermId, usize)>>,
    u: TermId,
    v: TermId,
) -> Result<ExprId, ReconstructError> {
    let path = bfs_path(adj, u, v).ok_or_else(|| ReconstructError::UnsupportedTerm {
        term: "no premise path between the two clashing members".to_owned(),
    })?;
    let str_ty = ctx.sp.str_const(&mut ctx.kernel);
    // Per-premise hypothesis axioms `hᵢ : Eq Str L(lᵢ) L(rᵢ)`, declared once.
    let mut hyps: BTreeMap<usize, ExprId> = BTreeMap::new();
    let start = ctx.translate(arena, u)?;
    // acc : Eq Str L(u) L(cur), cur starts at u.
    let mut acc = ctx.eq_refl(str_ty, start);
    let mut cur = u;
    let mut cur_e = start;
    for &(next, premise_idx) in &path {
        let (l, r) = cited[premise_idx];
        let h = if let Some(&h) = hyps.get(&premise_idx) {
            h
        } else {
            let le = ctx.translate(arena, l)?;
            let re = ctx.translate(arena, r)?;
            let prop = ctx.mk_eq(str_ty, le, re);
            let h = ctx.axiom("h", prop)?;
            hyps.insert(premise_idx, h);
            h
        };
        let next_e = ctx.translate(arena, next)?;
        // Orient the edge to `Eq Str L(cur) L(next)`.
        let edge = if cur == l && next == r {
            h
        } else if cur == r && next == l {
            let le = ctx.translate(arena, l)?;
            let re = ctx.translate(arena, r)?;
            ctx.eq_symm(str_ty, le, re, h)
        } else {
            return Err(ReconstructError::UnsupportedTerm {
                term: "premise edge endpoints did not match the path step".to_owned(),
            });
        };
        acc = ctx.eq_trans(str_ty, start, cur_e, next_e, acc, edge);
        cur = next;
        cur_e = next_e;
    }
    let _ = cur;
    Ok(acc)
}

/// A shortest path from `u` to `v` as a list of `(next_node, premise_index)`
/// steps, via breadth-first search over the premise graph.
fn bfs_path(
    adj: &BTreeMap<TermId, Vec<(TermId, usize)>>,
    u: TermId,
    v: TermId,
) -> Option<Vec<(TermId, usize)>> {
    if u == v {
        return Some(Vec::new());
    }
    let mut prev: BTreeMap<TermId, (TermId, usize)> = BTreeMap::new();
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    let mut queue: VecDeque<TermId> = VecDeque::new();
    seen.insert(u);
    queue.push_back(u);
    while let Some(cur) = queue.pop_front() {
        if let Some(neighbors) = adj.get(&cur) {
            for &(next, idx) in neighbors {
                if seen.insert(next) {
                    prev.insert(next, (cur, idx));
                    if next == v {
                        // Reconstruct the path from v back to u.
                        let mut steps = Vec::new();
                        let mut node = v;
                        while node != u {
                            let (p, i) = prev[&node];
                            steps.push((node, i));
                            node = p;
                        }
                        steps.reverse();
                        return Some(steps);
                    }
                    queue.push_back(next);
                }
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// The two reconstructed classes.
// ---------------------------------------------------------------------------

/// Reconstruct a contradicted disequality `a ≠ b`: chain the premises to
/// `Eq Str L(a) L(b)` and apply the disequality hypothesis to `False`.
fn build_disequality_module(
    arena: &mut TermArena,
    cited: &[(TermId, TermId)],
    adj: &BTreeMap<TermId, Vec<(TermId, usize)>>,
    a: TermId,
    b: TermId,
) -> Result<String, ReconstructError> {
    let codepoints = collect_codepoints(arena, cited, &[(a, b)]);
    let mut ctx = WordCtx::new(&codepoints);
    let chain = build_chain(&mut ctx, arena, cited, adj, a, b)?;
    let str_ty = ctx.sp.str_const(&mut ctx.kernel);
    let ae = ctx.translate(arena, a)?;
    let be = ctx.translate(arena, b)?;
    // h_neq : Not (Eq Str L(a) L(b)) = (Eq Str L(a) L(b) → False).
    let eq_ab = ctx.mk_eq(str_ty, ae, be);
    let false_const = ctx.kernel.const_(ctx.sp.logic.false_, vec![]);
    let anon = ctx.kernel.anon();
    let not_ty = ctx.kernel.pi(anon, eq_ab, false_const, BinderInfo::Default);
    let h_neq = ctx.axiom("hneq", not_ty)?;
    let proof = ctx.kernel.app(h_neq, chain);
    ctx.gate_and_render(proof)
}

/// Reconstruct a concrete constant clash: chain to `Eq Str A B`, then close by
/// `congrArg (is_{cA} ∘ head ∘ tailᵏ)` + the `Bool` discriminator.
fn build_clash_module(
    arena: &mut TermArena,
    cited: &[(TermId, TermId)],
    adj: &BTreeMap<TermId, Vec<(TermId, usize)>>,
    u: TermId,
    v: TermId,
    pos: usize,
) -> Result<String, ReconstructError> {
    let codepoints = collect_codepoints(arena, cited, &[(u, v)]);
    let mut ctx = WordCtx::new(&codepoints);

    // The clash character of `u` at `pos` decides the is-tester.
    let uv = seq_codepoints(arena, u).ok_or_else(|| ReconstructError::UnsupportedTerm {
        term: "clash member is not concrete".to_owned(),
    })?;
    let cp_u = uv[pos];
    let idx_u = *ctx
        .char_index
        .get(&cp_u)
        .expect("clash code point is in the alphabet");

    let chain = build_chain(&mut ctx, arena, cited, adj, u, v)?; // Eq Str A B
    let str_ty = ctx.sp.str_const(&mut ctx.kernel);
    let bool_ty = ctx.kernel.const_(ctx.sp.logic.bool_, vec![]);
    let ue = ctx.translate(arena, u)?;
    let ve = ctx.translate(arena, v)?;

    // g : Str → Bool := λ s, is_{cA} (head (tailᵏ s)).  g A ↝ true, g B ↝ false.
    let g = build_projection_tester(&mut ctx, pos, idx_u);
    let g_v = ctx.kernel.app(g, ve); // ι→ false

    // symm chain : Eq Str B A ; congrArg g : Eq Bool (g B) (g A) = Eq Bool g_v true.
    let symm = ctx.eq_symm(str_ty, ue, ve, chain);
    let congr = ctx.congr_arg(str_ty, bool_ty, g, ve, ue, symm);
    let proof = ctx.bool_true_ne_false(g_v, congr);
    ctx.gate_and_render(proof)
}

/// `g = λ (s : Str), is_{alphabet[idx]} (head (tailᵖᵒˢ s))`.
fn build_projection_tester(ctx: &mut WordCtx, pos: usize, idx: usize) -> ExprId {
    let anon = ctx.kernel.anon();
    let str_ty = ctx.sp.str_const(&mut ctx.kernel);
    let tail = ctx.sp.tail_fn(&mut ctx.kernel);
    let head = ctx.sp.head_fn(&mut ctx.kernel);
    let is_tester = ctx.sp.char_is_tester(&mut ctx.kernel, idx);
    let s = ctx.kernel.bvar(0);
    // tailᵖᵒˢ s.
    let mut cur = s;
    for _ in 0..pos {
        cur = ctx.kernel.app(tail, cur);
    }
    let h = ctx.kernel.app(head, cur);
    let body = ctx.kernel.app(is_tester, h);
    ctx.kernel.lam(anon, str_ty, body, BinderInfo::Default)
}

/// Collect every distinct code point appearing in the concrete literals of the
/// cited premises and the extra target endpoints — the alphabet for the module.
fn collect_codepoints(
    arena: &TermArena,
    cited: &[(TermId, TermId)],
    extra: &[(TermId, TermId)],
) -> BTreeSet<u128> {
    let mut out = BTreeSet::new();
    let mut visit = |t: TermId| {
        collect_term_codepoints(arena, t, &mut out);
    };
    for &(a, b) in cited {
        visit(a);
        visit(b);
    }
    for &(a, b) in extra {
        visit(a);
        visit(b);
    }
    out
}

/// Add every concrete bit-vector code point reachable inside `t` to `out`.
fn collect_term_codepoints(arena: &TermArena, t: TermId, out: &mut BTreeSet<u128>) {
    // A closed sequence contributes all its element code points.
    if let Some(cps) = seq_codepoints(arena, t) {
        out.extend(cps);
        return;
    }
    if let TermNode::App { op, args } = arena.node(t) {
        match op {
            Op::SeqUnit if args.len() == 1 => {
                if let Ok(v) = eval(arena, args[0], &Assignment::new())
                    && let Some(cp) = value_codepoint(&v)
                {
                    out.insert(cp);
                }
            }
            _ => {
                for &a in args {
                    collect_term_codepoints(arena, a, out);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Minimal union-find (value-keyed, deterministic union-by-min-id).
// ---------------------------------------------------------------------------

#[derive(Default)]
struct MiniUf {
    parent: BTreeMap<TermId, TermId>,
}

impl MiniUf {
    fn find(&self, mut t: TermId) -> TermId {
        while let Some(&p) = self.parent.get(&t) {
            if p == t {
                break;
            }
            t = p;
        }
        t
    }

    fn union(&mut self, a: TermId, b: TermId) {
        self.parent.entry(a).or_insert(a);
        self.parent.entry(b).or_insert(b);
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return;
        }
        let (root, child) = if ra < rb { (ra, rb) } else { (rb, ra) };
        self.parent.insert(child, root);
    }
}

#[cfg(test)]
mod tests;
