//! Regex-membership derivative-emptiness refutation → kernel-checked Lean
//! `False` (P3.7 strings fragment, task #44).
//!
//! The in-tree regex-membership sub-solver
//! ([`axeyum_strings::regex::membership`], ADR-0054) reports a single-variable
//! membership problem `unsat` **only** behind a re-checkable **emptiness
//! certificate**: a finite derivative closure `S` of the combined regex that
//! contains the start state `canon(combined)`, is closed under the
//! transition-regex derivative, and holds **no** nullable (ε-accepting) residual
//! ([`recheck_empty`]). When those three hold, `L(combined) = ∅`, so no string is
//! a member and the problem is unsatisfiable.
//!
//! This module reconstructs that emptiness argument to a self-contained,
//! kernel-checked Lean module. It re-establishes the certificate independently
//! (the sole `unsat` gate), then encodes the certificate's derivative automaton
//! as **kernel inductives + ι-computing recursor terms** and proves the emptiness
//! implication *inside the kernel*:
//!
//! - a finite state enum `Q` — one nullary constructor per residual in `S`;
//! - a transition-letter enum `Char` — one nullary constructor per representative
//!   code point that distinguishes the derivative branches (a guard witness);
//! - `delta : Q → Char → Q` — the derivative transition, a closed nested
//!   `Q.rec`/`Char.rec` truth table that ι-folds `delta q_i a_k ↝ q_j` exactly
//!   when residual `s_i` steps to `s_j` on a character in branch `a_k`;
//! - `accept : Q → Bool` — nullability, a `Q.rec` table that ι-folds **every**
//!   state to `Bool.false` (the certificate's nullable-free invariant);
//! - `run : Str → Q → Q` — the automaton fold over `Str = List Char`
//!   (`run nil q ↝ q`, `run (cons c w) q ↝ run w (delta q c)`);
//! - the invariant `∀ (w : Str) (q : Q), accept (run w q) = false`, proved by
//!   **`Str`-induction** (the recursive-datatype recursor's per-tail induction
//!   hypothesis): the `nil` case is `Q.rec` case-analysis (`accept q ↝ false`),
//!   the `cons` step instantiates the hypothesis at `delta q c`.
//!
//! An assumed membership `hmem : accept (run w0 q0) = Bool.true` (for an opaque
//! word `w0` and the start state `q0`) then contradicts the invariant at
//! `(w0, q0)`: `Eq Bool false true` closes to `False` by the `Bool.true ≠
//! Bool.false` discriminator. The assembled term is `infer`-checked and
//! `def_eq`-compared to the prelude `False` before rendering — a wrong term is
//! declined, never a wrong `False`.
//!
//! # Faithfulness — what the kernel checks, and what it rests on
//!
//! The kernel independently re-checks the **combinatorial emptiness implication**
//! ("a closed, nullable-free state set accepts no string") over the certificate's
//! concrete transition/acceptance tables. Its trust rests on exactly what
//! [`recheck_empty`] rests on — the `derivative`/`nullable`/`canon` substrate
//! (anchored by the fundamental-derivative-theorem property test) — from which
//! `delta`/`accept` are read off; it adds no new trust and no kernel axioms. The
//! automaton alphabet is the finite set of branch-guard witnesses (a predicate
//! abstraction of the symbolic derivative automaton), so `w0` ranges over that
//! representative alphabet. A from-nothing faithfulness (a Lean regex-membership
//! *relation* `InRe : Regex → Str → Prop`) is blocked on the kernel's
//! recursive-indexed-inductive support and is the documented follow-up.
//!
//! # Declined (safe `unknown`, never a wrong verdict)
//!
//! A problem that is not certified empty within the reconstruction caps
//! ([`RECON_MAX_STATES`]), whose closure or representative alphabet exceeds the
//! module-size cap, or that is satisfiable, is declined with a
//! [`ReconstructError`]. The sole `unsat` gate is the re-established emptiness
//! certificate; anything short of it declines.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use std::collections::{BTreeMap, BTreeSet};

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, LevelId, NameId, StringPrelude, build_logic_prelude,
    build_string_prelude,
};
use axeyum_strings::Membership;
use axeyum_strings::regex::{Closure, Regex, canon, derivative, derivative_closure, nullable};

use crate::reconstruct::ReconstructError;

/// The rendered theorem name for a regex-emptiness refutation module. Matches the
/// shared `axeyum_refutation` audit name the real-Lean cross-check greps for in
/// `#print axioms` output.
const REGEX_LEAN_THEOREM: &str = "axeyum_refutation";

/// The distinct-canonical-residual cap for the re-established emptiness closure —
/// generous enough to certify the emptiness, then further capped for rendering by
/// [`RECON_STATE_CAP`].
pub const RECON_MAX_STATES: usize = 4_096;

/// The hard cap on the number of automaton states (`Q` constructors) the
/// reconstruction will materialize into a kernel module. A closure larger than
/// this declines to `unknown` (the emitted enum + `n×m` transition table would be
/// unwieldy); the certificate itself is unaffected.
const RECON_STATE_CAP: usize = 96;

/// The hard cap on the representative-alphabet size (`Char` constructors / the
/// transition table's column count). A wider alphabet declines to `unknown`.
const RECON_ALPHABET_CAP: usize = 96;

/// Reconstruct a regex-membership derivative-emptiness refutation of `problem` to
/// a self-contained, kernel-checked Lean module, or a [`ReconstructError`] if this
/// slice declines.
///
/// The emptiness certificate is first re-established independently over
/// `problem.combined_regex()` (the sole `unsat` gate — a complete, nullable-free,
/// re-checked derivative closure); the reconstruction then encodes that
/// certificate's automaton and proves `L(combined) = ∅` inside the kernel (see the
/// module docs). The returned module's `False` proof has already been
/// `infer`-checked and `def_eq False`-compared.
///
/// # Errors
///
/// - [`ReconstructError::UnsupportedTerm`] — no re-checked emptiness certificate
///   (not proven unsatisfiable within the caps), or the closure / representative
///   alphabet exceeds the module-size caps;
/// - [`ReconstructError::KernelRejected`] — an assembled term failed to `infer` to
///   `False` (an emitter bug, declined — never a wrong certificate).
pub fn reconstruct_regex_emptiness_to_lean_module(
    problem: &Membership,
) -> Result<String, ReconstructError> {
    let combined = problem.combined_regex();
    let start = canon(&combined);

    // (1) The sole `unsat` gate: an independently re-established, re-checked
    // emptiness certificate (a complete, nullable-free derivative closure).
    let Closure::Complete(mut states) = derivative_closure(&combined, RECON_MAX_STATES) else {
        return Err(ReconstructError::UnsupportedTerm {
            term: "regex derivative closure is not complete within the reconstruction cap"
                .to_owned(),
        });
    };
    states.sort();
    states.dedup();
    if states.iter().any(nullable) || !recheck_closed(&states) || !states.contains(&start) {
        return Err(ReconstructError::UnsupportedTerm {
            term: "regex membership is not certified empty (no re-checked emptiness certificate)"
                .to_owned(),
        });
    }
    let n = states.len();
    if n > RECON_STATE_CAP {
        return Err(ReconstructError::UnsupportedTerm {
            term: "regex emptiness closure exceeds the reconstruction state cap".to_owned(),
        });
    }

    // (2) Index the states and build the representative transition alphabet + the
    // `n×m` derivative transition table (each cell a target-state index).
    let index: BTreeMap<&Regex, usize> = states.iter().enumerate().map(|(i, s)| (s, i)).collect();
    let start_index = index[&start];

    let mut letters: BTreeSet<u32> = BTreeSet::new();
    for s in &states {
        for (guard, _residual) in derivative(s).branches() {
            if let Some(c) = guard.witness() {
                letters.insert(c);
            }
        }
    }
    let letters: Vec<u32> = letters.into_iter().collect();
    let m = letters.len();
    if m == 0 || m > RECON_ALPHABET_CAP {
        return Err(ReconstructError::UnsupportedTerm {
            term: "regex emptiness alphabet is empty or exceeds the reconstruction cap".to_owned(),
        });
    }

    let mut delta = vec![vec![0usize; m]; n];
    for (i, s) in states.iter().enumerate() {
        let tr = derivative(s);
        for (k, &c) in letters.iter().enumerate() {
            // Every state's guards are disjoint and cover the alphabet, so exactly
            // one branch contains `c`; its residual is in the (closed) state set.
            let residual = tr
                .branches()
                .iter()
                .find(|(g, _)| g.contains(c))
                .map(|(_, r)| r)
                .ok_or_else(|| ReconstructError::UnsupportedTerm {
                    term: "derivative branches do not cover a representative letter".to_owned(),
                })?;
            let j = *index
                .get(residual)
                .ok_or_else(|| ReconstructError::UnsupportedTerm {
                    term: "derivative residual escaped the certified closure".to_owned(),
                })?;
            delta[i][k] = j;
        }
    }

    // (3) Build the kernel automaton and the emptiness proof, gate it, render it.
    let mut ctx = RegexCtx::new(n, m);
    let module = ctx.build_emptiness_module(&delta, start_index)?;
    Ok(module)
}

/// Independently re-check that `states` is closed under the transition-regex
/// derivative (every residual of every member is a member). Nullable-freeness and
/// start-membership are checked by the caller; together they are the emptiness
/// certificate ([`recheck_empty`](axeyum_strings::regex::recheck_empty)) — here
/// re-expressed over the reconstructor's own sorted state vector.
fn recheck_closed(states: &[Regex]) -> bool {
    let set: BTreeSet<&Regex> = states.iter().collect();
    states.iter().all(|s| {
        derivative(s)
            .branches()
            .iter()
            .all(|(_, r)| set.contains(r))
    })
}

// ---------------------------------------------------------------------------
// The reconstruction context: a kernel with the logic + string prelude and a
// freshly-declared state enum `Q`.
// ---------------------------------------------------------------------------

/// A kernel seeded with the logical + string prelude (over the `m`-letter
/// representative alphabet) plus a freshly-declared `n`-state enum `Q`.
struct RegexCtx {
    kernel: Kernel,
    sp: StringPrelude,
    /// `Q : Type` — the automaton state enum.
    q_ind: NameId,
    /// `Q.q<i> : Q` — one nullary constructor per certified residual.
    q_ctors: Vec<NameId>,
    /// `Q.rec` — the state eliminator.
    q_rec: NameId,
    /// The universe level `1`.
    one: LevelId,
    next_id: u64,
}

impl RegexCtx {
    /// A fresh context over an `n`-state / `m`-letter automaton.
    fn new(n: usize, m: usize) -> Self {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel);
        let sp = build_string_prelude(&mut kernel, logic, m);
        let one = {
            let z = kernel.level_zero();
            kernel.level_succ(z)
        };

        // Q : Type, Q.q0 | … | Q.q{n-1} (all nullary), in the reserved namespace.
        let q_ind = {
            let anon = kernel.anon();
            let ns = kernel.name_str(anon, "axeyum.regex");
            kernel.name_str(ns, "Q")
        };
        let q_ctors: Vec<NameId> = (0..n)
            .map(|i| kernel.name_str(q_ind, format!("q{i}")))
            .collect();
        {
            let q_ty = kernel.sort(one);
            let q_const = kernel.const_(q_ind, vec![]);
            let ctor_decls: Vec<(NameId, ExprId)> = q_ctors.iter().map(|&c| (c, q_const)).collect();
            kernel
                .add_inductive(q_ind, &[], 0, q_ty, &ctor_decls)
                .expect("state enum Q should admit");
        }
        let q_rec = kernel.name_str(q_ind, "rec");

        Self {
            kernel,
            sp,
            q_ind,
            q_ctors,
            q_rec,
            one,
            next_id: 0,
        }
    }

    fn n(&self) -> usize {
        self.q_ctors.len()
    }

    fn fresh_name(&mut self, base: &str) -> NameId {
        let anon = self.kernel.anon();
        let ns = self.kernel.name_str(anon, "axeyum.reconstruct.regex");
        let id = self.next_id;
        self.next_id += 1;
        let with_base = self.kernel.name_str(ns, base);
        self.kernel.name_num(with_base, id)
    }

    /// Declare a fresh axiom `_ : ty` and return its `Const` term.
    fn axiom(&mut self, base: &str, ty: ExprId) -> Result<ExprId, ReconstructError> {
        let name = self.fresh_name(base);
        self.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "regex".to_owned(),
                detail: format!("axiom {base} did not admit: {e:?}"),
            })?;
        Ok(self.kernel.const_(name, vec![]))
    }

    // ---- kernel handles ----------------------------------------------------

    fn q_const(&mut self) -> ExprId {
        self.kernel.const_(self.q_ind, vec![])
    }

    fn q_ctor(&mut self, i: usize) -> ExprId {
        self.kernel.const_(self.q_ctors[i], vec![])
    }

    fn bool_const(&mut self) -> ExprId {
        self.kernel.const_(self.sp.logic.bool_, vec![])
    }

    fn bool_true(&mut self) -> ExprId {
        self.kernel.const_(self.sp.logic.bool_true, vec![])
    }

    fn bool_false(&mut self) -> ExprId {
        self.kernel.const_(self.sp.logic.bool_false, vec![])
    }

    // ---- Eq builders over a `Sort 1` carrier (here always `Bool`) ----------

    fn mk_eq(&mut self, ty: ExprId, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.kernel.const_(self.sp.logic.eq, vec![self.one]);
        let e = self.kernel.app(eq, ty);
        let e = self.kernel.app(e, x);
        self.kernel.app(e, y)
    }

    fn eq_refl(&mut self, ty: ExprId, a: ExprId) -> ExprId {
        let refl = self.kernel.const_(self.sp.logic.eq_refl, vec![self.one]);
        let e = self.kernel.app(refl, ty);
        self.kernel.app(e, a)
    }

    /// `Eq.rec` transport over a `Sort 1` carrier into a `Prop` motive:
    /// `@Eq.rec.{0,1} ty p motive refl q h`.
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
        let rec = self.kernel.const_(self.sp.logic.eq_rec, vec![z, self.one]);
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

    /// Given `heq : Eq Bool Bool.true Bool.false`, build `False` via the
    /// `Bool.true ≠ Bool.false` discriminator (`d b := Bool.rec (λ_,Prop) True
    /// False b`; transport `True.intro : d true` along `heq` to `d false = False`).
    fn bool_true_ne_false(&mut self, heq: ExprId) -> ExprId {
        let anon = self.kernel.anon();
        let bool_const = self.bool_const();
        let prop = self.kernel.sort_zero();
        let true_prop = self.kernel.const_(self.sp.logic.true_, vec![]);
        let false_prop = self.kernel.const_(self.sp.logic.false_, vec![]);
        let bool_true = self.bool_true();

        // d : Bool → Prop = λ b, Bool.rec.{1} (λ_,Prop) True False b.
        let discr = {
            let rec = self.kernel.const_(self.sp.logic.bool_rec, vec![self.one]);
            let motive = self.kernel.lam(anon, bool_const, prop, BinderInfo::Default);
            let e = self.kernel.app(rec, motive);
            let e = self.kernel.app(e, true_prop); // minor for Bool.true  ⇒ True
            let e = self.kernel.app(e, false_prop); // minor for Bool.false ⇒ False
            let b = self.kernel.bvar(0);
            let body = self.kernel.app(e, b);
            self.kernel.lam(anon, bool_const, body, BinderInfo::Default)
        };
        // motive N := λ (x:Bool) (_ : Eq Bool true x), d x.
        let transport_motive = {
            let x = self.kernel.bvar(1);
            let discr_x = self.kernel.app(discr, x);
            let x0 = self.kernel.bvar(0);
            let eq_true_x = self.mk_eq(bool_const, bool_true, x0);
            let inner = self
                .kernel
                .lam(anon, eq_true_x, discr_x, BinderInfo::Default);
            self.kernel
                .lam(anon, bool_const, inner, BinderInfo::Default)
        };
        // refl_case : d true = True ⇒ True.intro.
        let refl_case = self.kernel.const_(self.sp.logic.true_intro, vec![]);
        let bool_false = self.bool_false();
        self.eq_rec(
            bool_const,
            bool_true,
            transport_motive,
            refl_case,
            bool_false,
            heq,
        )
    }

    // ---- the automaton terms ----------------------------------------------

    /// `delta : Q → Char → Q`, the closed nested `Q.rec`/`Char.rec` truth table:
    /// `delta q_i a_k ↝ q_{table[i][k]}`.
    fn build_delta(&mut self, table: &[Vec<usize>]) -> ExprId {
        let anon = self.kernel.anon();
        let q_const = self.q_const();
        let char_const = self.sp.char_const(&mut self.kernel);
        let char_to_q = self
            .kernel
            .pi(anon, char_const, q_const, BinderInfo::Default);
        let outer_motive = self
            .kernel
            .lam(anon, q_const, char_to_q, BinderInfo::Default);
        let outer_rec = self.kernel.const_(self.q_rec, vec![self.one]);
        let mut outer = self.kernel.app(outer_rec, outer_motive);
        for row in table {
            // row_i : Char → Q = λ (c:Char), Char.rec.{1} (λ_,Q) [q…] c.
            let inner_motive = self
                .kernel
                .lam(anon, char_const, q_const, BinderInfo::Default);
            let inner_rec = self.kernel.const_(self.sp.char_rec, vec![self.one]);
            let mut inner = self.kernel.app(inner_rec, inner_motive);
            for &j in row {
                let qj = self.q_ctor(j);
                inner = self.kernel.app(inner, qj);
            }
            let c = self.kernel.bvar(0);
            let inner_body = self.kernel.app(inner, c);
            let row_lam = self
                .kernel
                .lam(anon, char_const, inner_body, BinderInfo::Default);
            outer = self.kernel.app(outer, row_lam);
        }
        let q = self.kernel.bvar(0);
        let outer_body = self.kernel.app(outer, q);
        self.kernel
            .lam(anon, q_const, outer_body, BinderInfo::Default)
    }

    /// `accept : Q → Bool`, the `Q.rec` table folding **every** state to
    /// `Bool.false` (the certificate's nullable-free invariant).
    fn build_accept(&mut self) -> ExprId {
        let anon = self.kernel.anon();
        let q_const = self.q_const();
        let bool_const = self.bool_const();
        let motive = self
            .kernel
            .lam(anon, q_const, bool_const, BinderInfo::Default);
        let rec = self.kernel.const_(self.q_rec, vec![self.one]);
        let mut e = self.kernel.app(rec, motive);
        let false_c = self.bool_false();
        for _ in 0..self.n() {
            e = self.kernel.app(e, false_c);
        }
        let q = self.kernel.bvar(0);
        let body = self.kernel.app(e, q);
        self.kernel.lam(anon, q_const, body, BinderInfo::Default)
    }

    /// `run : Str → Q → Q`, the automaton fold via `Str.rec`:
    /// `run nil q ↝ q`, `run (cons c w) q ↝ run w (delta q c)`.
    fn build_run(&mut self, delta: ExprId) -> ExprId {
        let anon = self.kernel.anon();
        let q_const = self.q_const();
        let str_const = self.sp.str_const(&mut self.kernel);
        let char_const = self.sp.char_const(&mut self.kernel);
        let q_to_q = self.kernel.pi(anon, q_const, q_const, BinderInfo::Default);
        let motive = self
            .kernel
            .lam(anon, str_const, q_to_q, BinderInfo::Default);
        let rec = self.kernel.const_(self.sp.str_rec, vec![self.one]);
        // nil minor : Q → Q = λ q, q.
        let nil_minor = {
            let q = self.kernel.bvar(0);
            self.kernel.lam(anon, q_const, q, BinderInfo::Default)
        };
        // cons minor : Π (h:Char)(t:Str)(ih:Q→Q), (Q→Q) = λ h t ih, λ q, ih (delta q h).
        let cons_minor = {
            let q = self.kernel.bvar(0); // q
            let ih = self.kernel.bvar(1); // ih : Q → Q
            let h = self.kernel.bvar(3); // h : Char
            let dqh = {
                let e = self.kernel.app(delta, q);
                self.kernel.app(e, h)
            };
            let body = self.kernel.app(ih, dqh);
            let lq = self.kernel.lam(anon, q_const, body, BinderInfo::Default); // λ q
            let lih = self.kernel.lam(anon, q_to_q, lq, BinderInfo::Default); // λ ih
            let lt = self.kernel.lam(anon, str_const, lih, BinderInfo::Default); // λ t
            self.kernel.lam(anon, char_const, lt, BinderInfo::Default) // λ h
        };
        let e = self.kernel.app(rec, motive);
        let e = self.kernel.app(e, nil_minor);
        let e = self.kernel.app(e, cons_minor);
        let w = self.kernel.bvar(0);
        let body = self.kernel.app(e, w);
        self.kernel.lam(anon, str_const, body, BinderInfo::Default)
    }

    /// `emptiness : Π (w:Str) (q:Q), Eq Bool (accept (run w q)) Bool.false`, proved
    /// by `Str`-induction over the certificate's nullable-free closed automaton.
    fn build_emptiness(&mut self, accept: ExprId, run: ExprId, delta: ExprId) -> ExprId {
        let anon = self.kernel.anon();
        let q_const = self.q_const();
        let str_const = self.sp.str_const(&mut self.kernel);
        let char_const = self.sp.char_const(&mut self.kernel);
        let bool_const = self.bool_const();
        let false_c = self.bool_false();

        // motive M := λ (w:Str), Π (q:Q), Eq Bool (accept (run w q)) false.
        let motive = {
            // body under `λ w` then `Π q`: q = bvar 0, w = bvar 1.
            let w = self.kernel.bvar(1);
            let q = self.kernel.bvar(0);
            let run_wq = {
                let e = self.kernel.app(run, w);
                self.kernel.app(e, q)
            };
            let acc = self.kernel.app(accept, run_wq);
            let eqf = self.mk_eq(bool_const, acc, false_c);
            let pi_q = self.kernel.pi(anon, q_const, eqf, BinderInfo::Default);
            self.kernel.lam(anon, str_const, pi_q, BinderInfo::Default)
        };

        // nil minor : M nil ≡ Π (q:Q), Eq Bool (accept q) false.
        //   = λ q, Q.rec.{0} (λ q', Eq Bool (accept q') false) [refl…] q.
        let nil_minor = {
            let inner_motive = {
                let qp = self.kernel.bvar(0);
                let acc = self.kernel.app(accept, qp);
                let eqf = self.mk_eq(bool_const, acc, false_c);
                self.kernel.lam(anon, q_const, eqf, BinderInfo::Default)
            };
            let z = self.kernel.level_zero();
            let rec = self.kernel.const_(self.q_rec, vec![z]);
            let mut e = self.kernel.app(rec, inner_motive);
            let refl_false = self.eq_refl(bool_const, false_c);
            for _ in 0..self.n() {
                e = self.kernel.app(e, refl_false);
            }
            let q = self.kernel.bvar(0);
            let body = self.kernel.app(e, q);
            self.kernel.lam(anon, q_const, body, BinderInfo::Default)
        };

        // cons minor : Π (h:Char)(t:Str)(ih : M t), M (cons h t)
        //   = λ h t ih, λ q, ih (delta q h).
        let cons_minor = {
            let q = self.kernel.bvar(0); // q
            let ih = self.kernel.bvar(1); // ih : M t
            let h = self.kernel.bvar(3); // h : Char
            let dqh = {
                let e = self.kernel.app(delta, q);
                self.kernel.app(e, h)
            };
            let body = self.kernel.app(ih, dqh);
            let lq = self.kernel.lam(anon, q_const, body, BinderInfo::Default); // λ q
            // ih : M t, where t is the bvar bound by the enclosing `λ t`.
            let m_t = {
                let t = self.kernel.bvar(0);
                self.kernel.app(motive, t)
            };
            let lih = self.kernel.lam(anon, m_t, lq, BinderInfo::Default); // λ ih : M t
            let lt = self.kernel.lam(anon, str_const, lih, BinderInfo::Default); // λ t
            self.kernel.lam(anon, char_const, lt, BinderInfo::Default) // λ h
        };

        let z = self.kernel.level_zero();
        let rec = self.kernel.const_(self.sp.str_rec, vec![z]);
        let e = self.kernel.app(rec, motive);
        let e = self.kernel.app(e, nil_minor);
        self.kernel.app(e, cons_minor)
        // Result: `Str.rec.{0} M nil_minor cons_minor : Π (w:Str), M w`.
    }

    /// Assemble the full `False` proof, gate it through the kernel, and render the
    /// self-contained Lean module (emitting `Char`, `Q`, `Str`, `Bool` inductives
    /// so an external Lean regenerates their recursors *with* ι).
    fn build_emptiness_module(
        &mut self,
        delta_table: &[Vec<usize>],
        start_index: usize,
    ) -> Result<String, ReconstructError> {
        let bool_const = self.bool_const();
        let false_c = self.bool_false();
        let true_c = self.bool_true();
        let str_const = self.sp.str_const(&mut self.kernel);

        let delta = self.build_delta(delta_table);
        let accept = self.build_accept();
        let run = self.build_run(delta);
        let emptiness = self.build_emptiness(accept, run, delta);

        // The opaque candidate word `w0 : Str` and the automaton's start state.
        let w0 = self.axiom("w", str_const)?;
        let q0 = self.q_ctor(start_index);

        // e1 : Eq Bool (accept (run w0 q0)) false.
        let empt_w0 = self.kernel.app(emptiness, w0);
        let e1 = self.kernel.app(empt_w0, q0);

        // acc := accept (run w0 q0).
        let acc = {
            let e = self.kernel.app(run, w0);
            let run_w0_q0 = self.kernel.app(e, q0);
            self.kernel.app(accept, run_w0_q0)
        };

        // hmem : Eq Bool acc true  — the assumed membership (`w0 ∈ L(combined)`).
        let hmem_ty = self.mk_eq(bool_const, acc, true_c);
        let hmem = self.axiom("hmem", hmem_ty)?;

        // heq : Eq Bool true false = trans (symm hmem) e1.
        let sym = self.eq_symm(bool_const, acc, true_c, hmem);
        let heq = self.eq_trans(bool_const, true_c, acc, false_c, sym, e1);
        let proof = self.bool_true_ne_false(heq);

        self.gate_and_render(proof)
    }

    /// Gate the assembled proof (`infer` + `def_eq False`) and render the module.
    fn gate_and_render(&mut self, proof: ExprId) -> Result<String, ReconstructError> {
        let inferred = self
            .kernel
            .infer(proof)
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "regex".to_owned(),
                detail: format!("infer failed: {e:?}"),
            })?;
        let false_const = self.kernel.const_(self.sp.logic.false_, vec![]);
        if !self.kernel.def_eq(inferred, false_const) {
            return Err(ReconstructError::KernelRejected {
                rule: "regex".to_owned(),
                detail: "regex emptiness refutation did not infer to False".to_owned(),
            });
        }
        let inductives = [
            self.sp.char_ind,
            self.q_ind,
            self.sp.str_ind,
            self.sp.logic.bool_,
        ];
        let false_goal = self.kernel.const_(self.sp.logic.false_, vec![]);
        Ok(self.kernel.render_lean_module_with_inductives(
            REGEX_LEAN_THEOREM,
            false_goal,
            proof,
            &inductives,
        ))
    }
}

#[cfg(test)]
mod tests;
