//! Machine-checked natural-number arithmetic for the Rado shell construction.
//!
//! This is the first *mathematical* development checked by axeyum's own Lean
//! kernel (as opposed to a reconstructed SMT certificate). Everything here is
//! built out of the kernel's public trusted gates:
//!
//! - [`Kernel::add_inductive`] via [`build_logic_prelude`] supplies `Nat`
//!   (`Nat.zero | Nat.succ`) with its generated, ι-computing `Nat.rec`, and the
//!   indexed `Eq` with `Eq.rec`;
//! - [`Kernel::add_declaration`] admits `Definition`s (`add`/`mul`/`pow`/`geo`/
//!   the shell recurrence) and `Theorem`s, each of which is admitted **only if
//!   the kernel itself type-checks the proof term against the stated
//!   proposition**.
//!
//! **No axioms are declared.** The `arith_prelude` route (an axiomatized linear
//! ordered field, 30 axioms) is deliberately *not* used: over the prelude's
//! inductive `Nat` the same statements are provable outright, and the Rado
//! equation lives over the naturals anyway. `tests::the_development_declares_no_axioms`
//! enforces that claim mechanically.
//!
//! What is proved (all statements universally quantified over ℕ, i.e. infinite
//! families, not enumerated points):
//!
//! - `defect_identity` — `a * (a*b*b + 1) = a*1 + b*(a*a*b)`. In ℕ the Rado
//!   equation `a(x − y) = b z` is `a*x = a*y + b*z`; with `y = 1`,
//!   `x = a*b² + 1`, `z = a²*b` this says the closed-form defect family of the
//!   shell construction really is a solution of `E(a,b)` for **every** `a, b`.
//! - `geo_closed_form` — `a * G(a,k) + 1 = G(a,k) + a^k` for `G(a,k) = Σ_{i<k} a^i`
//!   (the geometric-sum identity, by induction on `k`).
//! - `shell_closed_form` — the shell's level-capacity recurrence
//!   `T(a,0) = a`, `T(a,m+1) = a*T(a,m) + 2a` satisfies
//!   `T(a,m) = a^(m+1) + 2*(a*G(a,m))`, i.e. the construction's
//!   `N = b*(a^(k-1) + 2*(a^(k-2) + … + a))` (by induction on `m`, using the
//!   geometric identity in the step).
//! - `nshell_closed_form` — the same with the `b` factor: `N = b*T(a,m)`.

// Proof scripts are long, straight-line term constructions with short
// mathematical names; splitting them would obscure the derivation they mirror.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::type_complexity
)]

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, KernelError, LogicPrelude, NameId, ReducibilityHint,
    build_logic_prelude,
};

// ---------------------------------------------------------------------------
// Development scaffolding
// ---------------------------------------------------------------------------

/// A kernel plus the interned names of this development.
struct Dev {
    k: Kernel,
    logic: LogicPrelude,
    anon: NameId,
    root: NameId,
    nat_ty: ExprId,
    next_fvar: u64,
}

impl Dev {
    fn new() -> Self {
        let mut k = Kernel::new();
        let logic = build_logic_prelude(&mut k);
        let anon = k.anon();
        let root = k.name_str(anon, "rado");
        let nat_ty = k.const_(logic.nat, vec![]);
        Self {
            k,
            logic,
            anon,
            root,
            nat_ty,
            // Start well above anything the kernel's own inference allocates
            // for the closed terms we hand it.
            next_fvar: 1_000,
        }
    }

    fn name(&mut self, s: &str) -> NameId {
        let root = self.root;
        self.k.name_str(root, s)
    }

    fn fresh(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }

    fn level_one(&mut self) -> axeyum_lean_kernel::LevelId {
        let z = self.k.level_zero();
        self.k.level_succ(z)
    }

    // --- Nat terms ---------------------------------------------------------

    fn zero(&mut self) -> ExprId {
        self.k.const_(self.logic.nat_zero, vec![])
    }

    fn succ(&mut self, x: ExprId) -> ExprId {
        let s = self.k.const_(self.logic.nat_succ, vec![]);
        self.k.app(s, x)
    }

    /// The unary numeral `succ^n zero`.
    fn num(&mut self, n: u32) -> ExprId {
        let mut e = self.zero();
        for _ in 0..n {
            e = self.succ(e);
        }
        e
    }

    fn apply(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        let mut e = head;
        for &a in args {
            e = self.k.app(e, a);
        }
        e
    }

    /// `f x y` for a declared binary constant of this development.
    fn bin(&mut self, f: &str, x: ExprId, y: ExprId) -> ExprId {
        let n = self.name(f);
        let c = self.k.const_(n, vec![]);
        self.apply(c, &[x, y])
    }

    fn add(&mut self, x: ExprId, y: ExprId) -> ExprId {
        self.bin("add", x, y)
    }

    fn mul(&mut self, x: ExprId, y: ExprId) -> ExprId {
        self.bin("mul", x, y)
    }

    fn pow(&mut self, x: ExprId, y: ExprId) -> ExprId {
        self.bin("pow", x, y)
    }

    fn geo(&mut self, x: ExprId, y: ExprId) -> ExprId {
        self.bin("geo", x, y)
    }

    fn geo1(&mut self, x: ExprId, y: ExprId) -> ExprId {
        self.bin("geo1", x, y)
    }

    fn shell(&mut self, x: ExprId, y: ExprId) -> ExprId {
        self.bin("shellT", x, y)
    }

    fn nshell(&mut self, a: ExprId, b: ExprId, m: ExprId) -> ExprId {
        let n = self.name("nshell");
        let c = self.k.const_(n, vec![]);
        self.apply(c, &[a, b, m])
    }

    // --- binders -----------------------------------------------------------

    fn lam_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.k.abstract_fvars(body, &[fv]);
        let anon = self.anon;
        self.k.lam(anon, ty, b, BinderInfo::Default)
    }

    fn pi_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.k.abstract_fvars(body, &[fv]);
        let anon = self.anon;
        self.k.pi(anon, ty, b, BinderInfo::Default)
    }

    // --- Eq terms ----------------------------------------------------------

    /// `Eq.{1} Nat x y`.
    fn eq(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let one = self.level_one();
        let eq = self.k.const_(self.logic.eq, vec![one]);
        let nat = self.nat_ty;
        self.apply(eq, &[nat, x, y])
    }

    /// `Eq.refl.{1} Nat a : Eq Nat a a`.
    fn refl(&mut self, a: ExprId) -> ExprId {
        let one = self.level_one();
        let refl = self.k.const_(self.logic.eq_refl, vec![one]);
        let nat = self.nat_ty;
        self.apply(refl, &[nat, a])
    }

    /// `Eq.rec.{0,1} Nat p motive refl_case q h : motive q h`.
    fn transport(
        &mut self,
        p: ExprId,
        motive: ExprId,
        refl_case: ExprId,
        q: ExprId,
        h: ExprId,
    ) -> ExprId {
        let z = self.k.level_zero();
        let one = self.level_one();
        let rec = self.k.const_(self.logic.eq_rec, vec![z, one]);
        let nat = self.nat_ty;
        self.apply(rec, &[nat, p, motive, refl_case, q, h])
    }

    /// Build the `Eq.rec` motive `fun (x : Nat) (_ : Eq Nat a x) => body(x)`.
    fn eq_motive(&mut self, a: ExprId, body: &dyn Fn(&mut Dev, ExprId) -> ExprId) -> ExprId {
        let x_fv = self.fresh();
        let x = self.k.fvar(x_fv);
        let concl = body(self, x);
        let hyp = self.eq(a, x);
        let anon = self.anon;
        let inner = self.k.lam(anon, hyp, concl, BinderInfo::Default);
        let nat = self.nat_ty;
        self.lam_fv(x_fv, nat, inner)
    }

    /// `h : Eq Nat a b  ⊢  Eq Nat b a`.
    fn symm(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let motive = self.eq_motive(a, &|d, x| d.eq(x, a));
        let refl_case = self.refl(a);
        self.transport(a, motive, refl_case, b, h)
    }

    /// `h1 : Eq Nat a b`, `h2 : Eq Nat b c  ⊢  Eq Nat a c`.
    fn trans(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        let motive = self.eq_motive(b, &|d, x| d.eq(a, x));
        self.transport(b, motive, h1, c, h2)
    }

    /// Chain `a = x1 = x2 = … = z` from `(rhs, proof)` steps.
    fn chain(&mut self, start: ExprId, steps: &[(ExprId, ExprId)]) -> (ExprId, ExprId) {
        let mut current = start;
        let mut proof = self.refl(start);
        for &(next, step) in steps {
            proof = self.trans(start, current, next, proof, step);
            current = next;
        }
        (current, proof)
    }

    /// Congruence in an arbitrary one-hole context: `h : Eq Nat a b` gives
    /// `Eq Nat (f a) (f b)`.
    fn congr(
        &mut self,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        f: &dyn Fn(&mut Dev, ExprId) -> ExprId,
    ) -> ExprId {
        let fa = f(self, a);
        let motive = self.eq_motive(a, &|d, x| {
            let fx = f(d, x);
            d.eq(fa, fx)
        });
        let refl_case = self.refl(fa);
        self.transport(a, motive, refl_case, b, h)
    }

    // --- induction ---------------------------------------------------------

    /// `Nat.rec.{0} (fun x => p x) base (fun j ih => step j ih) target`, a proof
    /// of `p target` for a `Prop`-valued motive.
    fn induct(
        &mut self,
        p: &dyn Fn(&mut Dev, ExprId) -> ExprId,
        base: &dyn Fn(&mut Dev) -> ExprId,
        step: &dyn Fn(&mut Dev, ExprId, ExprId) -> ExprId,
        target: ExprId,
    ) -> ExprId {
        let nat = self.nat_ty;
        let motive = {
            let x_fv = self.fresh();
            let x = self.k.fvar(x_fv);
            let body = p(self, x);
            self.lam_fv(x_fv, nat, body)
        };
        let base_term = base(self);
        let step_term = {
            let j_fv = self.fresh();
            let j = self.k.fvar(j_fv);
            let ih_fv = self.fresh();
            let ih = self.k.fvar(ih_fv);
            let hyp_ty = p(self, j);
            let body = step(self, j, ih);
            let inner = self.lam_fv(ih_fv, hyp_ty, body);
            self.lam_fv(j_fv, nat, inner)
        };
        let z = self.k.level_zero();
        let rec = self.k.const_(self.logic.nat_rec, vec![z]);
        self.apply(rec, &[motive, base_term, step_term, target])
    }

    // --- declarations ------------------------------------------------------

    /// `def name : Nat → Nat → Nat := fun x y => Nat.rec (fun _ => Nat) (base x) (fun j ih => step x j ih) y`
    ///
    /// i.e. structural recursion on the **second** argument, so
    /// `name x zero ≡ base x` and `name x (succ j) ≡ step x j (name x j)` hold
    /// definitionally (β/δ/ι), with no equation lemmas needed.
    fn define_binary(
        &mut self,
        name: &str,
        height: u16,
        base: &dyn Fn(&mut Dev, ExprId) -> ExprId,
        step: &dyn Fn(&mut Dev, ExprId, ExprId, ExprId) -> ExprId,
    ) -> NameId {
        let nat = self.nat_ty;
        let anon = self.anon;
        let x_fv = self.fresh();
        let x = self.k.fvar(x_fv);
        let motive = self.k.lam(anon, nat, nat, BinderInfo::Default);
        let minor_zero = base(self, x);
        let minor_succ = {
            let j_fv = self.fresh();
            let j = self.k.fvar(j_fv);
            let ih_fv = self.fresh();
            let ih = self.k.fvar(ih_fv);
            let body = step(self, x, j, ih);
            let inner = self.lam_fv(ih_fv, nat, body);
            self.lam_fv(j_fv, nat, inner)
        };
        let y_fv = self.fresh();
        let y = self.k.fvar(y_fv);
        let one = self.level_one();
        let rec = self.k.const_(self.logic.nat_rec, vec![one]);
        let body = self.apply(rec, &[motive, minor_zero, minor_succ, y]);
        let value = {
            let inner = self.lam_fv(y_fv, nat, body);
            self.lam_fv(x_fv, nat, inner)
        };
        let ty = {
            let inner = self.k.pi(anon, nat, nat, BinderInfo::Default);
            self.k.pi(anon, nat, inner, BinderInfo::Default)
        };
        let nm = self.name(name);
        self.k
            .add_declaration(Declaration::Definition {
                name: nm,
                uparams: vec![],
                ty,
                value,
                hint: ReducibilityHint::Regular(height),
            })
            .unwrap_or_else(|e| panic!("definition {name} should admit: {e:?}"));
        nm
    }

    /// Declare `theorem name : ∀ (x_0 … x_{arity-1} : Nat), stmt := fun … => proof`.
    ///
    /// The kernel re-checks `proof` against `stmt` inside
    /// [`Kernel::add_declaration`]; an `Err` here means the kernel **rejected**
    /// the proof.
    fn try_theorem(
        &mut self,
        name: &str,
        arity: usize,
        build: &dyn Fn(&mut Dev, &[ExprId]) -> (ExprId, ExprId),
    ) -> Result<ExprId, KernelError> {
        let nat = self.nat_ty;
        let fvs: Vec<u64> = (0..arity).map(|_| self.fresh()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&f| self.k.fvar(f)).collect();
        let (stmt, proof) = build(self, &vars);
        let mut ty = stmt;
        let mut value = proof;
        for &fv in fvs.iter().rev() {
            ty = self.pi_fv(fv, nat, ty);
            value = self.lam_fv(fv, nat, value);
        }
        let nm = self.name(name);
        self.k.add_declaration(Declaration::Theorem {
            name: nm,
            uparams: vec![],
            ty,
            value,
        })?;
        Ok(ty)
    }

    fn theorem(
        &mut self,
        name: &str,
        arity: usize,
        build: &dyn Fn(&mut Dev, &[ExprId]) -> (ExprId, ExprId),
    ) -> ExprId {
        match self.try_theorem(name, arity, build) {
            Ok(ty) => ty,
            Err(e) => panic!(
                "theorem {name} was rejected by the kernel: {}",
                self.explain(&e)
            ),
        }
    }

    /// A readable rendering of a kernel rejection (the payloads are `ExprId`s).
    fn explain(&self, e: &KernelError) -> String {
        match e {
            KernelError::DeclarationValueMismatch { declared, inferred } => format!(
                "DeclarationValueMismatch\n    declared : {}\n    inferred : {}",
                self.k.render_lean(*declared),
                self.k.render_lean(*inferred)
            ),
            KernelError::TypeMismatch { expected, got } => format!(
                "TypeMismatch\n    expected : {}\n    got      : {}",
                self.k.render_lean(*expected),
                self.k.render_lean(*got)
            ),
            other => format!("{other:?}"),
        }
    }

    /// Apply a previously proved lemma of this development to arguments.
    fn lem(&mut self, name: &str, args: &[ExprId]) -> ExprId {
        let n = self.name(name);
        let c = self.k.const_(n, vec![]);
        self.apply(c, args)
    }
}

// ---------------------------------------------------------------------------
// The development itself
// ---------------------------------------------------------------------------

/// Declare `add`, `mul`, `pow`, `geo` (the geometric sum), `shellT` (the shell's
/// level-capacity recurrence) and `nshell = b * shellT`.
fn definitions(d: &mut Dev) {
    // add x y : recursion on y.  add x zero ≡ x ; add x (succ j) ≡ succ (add x j)
    d.define_binary("add", 1, &|_d, x| x, &|d, _x, _j, ih| d.succ(ih));
    // mul x y : recursion on y.  mul x zero ≡ zero ; mul x (succ j) ≡ add (mul x j) x
    d.define_binary("mul", 2, &|d, _x| d.zero(), &|d, x, _j, ih| d.add(ih, x));
    // pow x y : recursion on y.  pow x zero ≡ 1 ; pow x (succ j) ≡ mul (pow x j) x
    d.define_binary("pow", 3, &|d, _x| d.num(1), &|d, x, _j, ih| d.mul(ih, x));
    // geo x y = Σ_{i<y} x^i.  geo x zero ≡ zero ; geo x (succ j) ≡ add (geo x j) (pow x j)
    d.define_binary("geo", 4, &|d, _x| d.zero(), &|d, x, j, ih| {
        let p = d.pow(x, j);
        d.add(ih, p)
    });
    // geo1 x y = Σ_{i=1..y} x^i — the bracket `a^(k-2) + … + a` as the shell
    // construction writes it.  geo1 x zero ≡ zero ; geo1 x (succ j) ≡ add (geo1 x j) (pow x (succ j))
    d.define_binary("geo1", 4, &|d, _x| d.zero(), &|d, x, j, ih| {
        let sj = d.succ(j);
        let p = d.pow(x, sj);
        d.add(ih, p)
    });
    // shellT a m : the level-capacity recurrence of the shell construction,
    // T(a,0) = a, T(a,m+1) = a*T(a,m) + 2a  (T(a, k-2) is the bracket of
    // N = b*(a^(k-1) + 2*(a^(k-2) + … + a))).
    d.define_binary("shellT", 5, &|_d, a| a, &|d, a, _j, ih| {
        let left = d.mul(a, ih);
        let two = d.num(2);
        let right = d.mul(two, a);
        d.add(left, right)
    });
    // nshell a b m = b * shellT a m — the construction's N.
    {
        let nat = d.nat_ty;
        let anon = d.anon;
        let a_fv = d.fresh();
        let b_fv = d.fresh();
        let m_fv = d.fresh();
        let a = d.k.fvar(a_fv);
        let b = d.k.fvar(b_fv);
        let m = d.k.fvar(m_fv);
        let t = d.shell(a, m);
        let body = d.mul(b, t);
        let value = {
            let v = d.lam_fv(m_fv, nat, body);
            let v = d.lam_fv(b_fv, nat, v);
            d.lam_fv(a_fv, nat, v)
        };
        let ty = {
            let t1 = d.k.pi(anon, nat, nat, BinderInfo::Default);
            let t2 = d.k.pi(anon, nat, t1, BinderInfo::Default);
            d.k.pi(anon, nat, t2, BinderInfo::Default)
        };
        let nm = d.name("nshell");
        d.k.add_declaration(Declaration::Definition {
            name: nm,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })
        .expect("nshell should admit");
    }
}

/// The additive and multiplicative lemmas, each proved by `Nat.rec` induction
/// (or by chaining earlier lemmas). Every one goes through `add_declaration`,
/// so every one is kernel-checked.
fn lemmas(d: &mut Dev) {
    // zero_add : ∀ n, add zero n = n   (induction on n)
    d.theorem("zero_add", 1, &|d, v| {
        let n = v[0];
        let p = |d: &mut Dev, x: ExprId| {
            let z = d.zero();
            let lhs = d.add(z, x);
            d.eq(lhs, x)
        };
        let stmt = p(d, n);
        let proof = d.induct(
            &p,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            &|d, j, ih| {
                let z = d.zero();
                let lhs = d.add(z, j);
                d.congr(lhs, j, ih, &|d, x| d.succ(x))
            },
            n,
        );
        (stmt, proof)
    });

    // succ_add : ∀ n m, add (succ n) m = succ (add n m)   (induction on m)
    d.theorem("succ_add", 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let p = |d: &mut Dev, x: ExprId| {
            let sn = d.succ(n);
            let lhs = d.add(sn, x);
            let inner = d.add(n, x);
            let rhs = d.succ(inner);
            d.eq(lhs, rhs)
        };
        let stmt = p(d, m);
        let proof = d.induct(
            &p,
            &|d| {
                let sn = d.succ(n);
                d.refl(sn)
            },
            &|d, j, ih| {
                let sn = d.succ(n);
                let lhs = d.add(sn, j);
                let inner = d.add(n, j);
                let rhs = d.succ(inner);
                d.congr(lhs, rhs, ih, &|d, x| d.succ(x))
            },
            m,
        );
        (stmt, proof)
    });

    // add_comm : ∀ n m, add n m = add m n   (induction on m)
    d.theorem("add_comm", 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let p = |d: &mut Dev, x: ExprId| {
            let lhs = d.add(n, x);
            let rhs = d.add(x, n);
            d.eq(lhs, rhs)
        };
        let stmt = p(d, m);
        let proof = d.induct(
            &p,
            &|d| {
                let z = d.zero();
                let za = d.add(z, n);
                let h = d.lem("zero_add", &[n]);
                d.symm(za, n, h)
            },
            &|d, j, ih| {
                let lhs = d.add(n, j);
                let rhs = d.add(j, n);
                let h1 = d.congr(lhs, rhs, ih, &|d, x| d.succ(x));
                let s_lhs = d.succ(lhs);
                let s_rhs = d.succ(rhs);
                let sj = d.succ(j);
                let sj_n = d.add(sj, n);
                let h_sa = d.lem("succ_add", &[j, n]);
                let h2 = d.symm(sj_n, s_rhs, h_sa);
                d.trans(s_lhs, s_rhs, sj_n, h1, h2)
            },
            m,
        );
        (stmt, proof)
    });

    // add_assoc : ∀ a b c, add (add a b) c = add a (add b c)   (induction on c)
    d.theorem("add_assoc", 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let p = |d: &mut Dev, x: ExprId| {
            let ab = d.add(a, b);
            let lhs = d.add(ab, x);
            let bx = d.add(b, x);
            let rhs = d.add(a, bx);
            d.eq(lhs, rhs)
        };
        let stmt = p(d, c);
        let proof = d.induct(
            &p,
            &|d| {
                let ab = d.add(a, b);
                d.refl(ab)
            },
            &|d, j, ih| {
                let ab = d.add(a, b);
                let lhs = d.add(ab, j);
                let bj = d.add(b, j);
                let rhs = d.add(a, bj);
                d.congr(lhs, rhs, ih, &|d, x| d.succ(x))
            },
            c,
        );
        (stmt, proof)
    });

    // add_right_comm : ∀ x y z, add (add x y) z = add (add x z) y   (no induction)
    d.theorem("add_right_comm", 3, &|d, v| {
        let (x, y, z) = (v[0], v[1], v[2]);
        let xy = d.add(x, y);
        let start = d.add(xy, z);
        let yz = d.add(y, z);
        let s1 = d.add(x, yz);
        let h1 = d.lem("add_assoc", &[x, y, z]);
        let zy = d.add(z, y);
        let s2 = d.add(x, zy);
        let h_comm = d.lem("add_comm", &[y, z]);
        let h2 = d.congr(yz, zy, h_comm, &|d, t| d.add(x, t));
        let xz = d.add(x, z);
        let s3 = d.add(xz, y);
        let h_assoc2 = d.lem("add_assoc", &[x, z, y]);
        let h3 = d.symm(s3, s2, h_assoc2);
        let (end, proof) = d.chain(start, &[(s1, h1), (s2, h2), (s3, h3)]);
        let stmt = d.eq(start, end);
        (stmt, proof)
    });

    // zero_mul : ∀ n, mul zero n = zero   (induction on n)
    d.theorem("zero_mul", 1, &|d, v| {
        let n = v[0];
        let p = |d: &mut Dev, x: ExprId| {
            let z = d.zero();
            let lhs = d.mul(z, x);
            d.eq(lhs, z)
        };
        let stmt = p(d, n);
        let proof = d.induct(
            &p,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            // mul zero (succ j) ≡ add (mul zero j) zero ≡ mul zero j, so the
            // induction hypothesis *is* the step, up to definitional equality.
            &|_d, _j, ih| ih,
            n,
        );
        (stmt, proof)
    });

    // succ_mul : ∀ n m, mul (succ n) m = add (mul n m) m   (induction on m)
    d.theorem("succ_mul", 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let p = |d: &mut Dev, x: ExprId| {
            let sn = d.succ(n);
            let lhs = d.mul(sn, x);
            let nm = d.mul(n, x);
            let rhs = d.add(nm, x);
            d.eq(lhs, rhs)
        };
        let stmt = p(d, m);
        let proof = d.induct(
            &p,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            &|d, j, ih| {
                // goal ≡ succ (add (mul (succ n) j) n) = succ (add (add (mul n j) n) j)
                let sn = d.succ(n);
                let snj = d.mul(sn, j);
                let start = d.add(snj, n);
                let nj = d.mul(n, j);
                let nj_j = d.add(nj, j);
                let s1 = d.add(nj_j, n);
                let h1 = d.congr(snj, nj_j, ih, &|d, t| d.add(t, n));
                let nj_n = d.add(nj, n);
                let s2 = d.add(nj_n, j);
                let h2 = d.lem("add_right_comm", &[nj, j, n]);
                let (end, inner) = d.chain(start, &[(s1, h1), (s2, h2)]);
                d.congr(start, end, inner, &|d, t| d.succ(t))
            },
            m,
        );
        (stmt, proof)
    });

    // mul_comm : ∀ n m, mul n m = mul m n   (induction on m)
    d.theorem("mul_comm", 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let p = |d: &mut Dev, x: ExprId| {
            let lhs = d.mul(n, x);
            let rhs = d.mul(x, n);
            d.eq(lhs, rhs)
        };
        let stmt = p(d, m);
        let proof = d.induct(
            &p,
            &|d| {
                let z = d.zero();
                let zn = d.mul(z, n);
                let h = d.lem("zero_mul", &[n]);
                d.symm(zn, z, h)
            },
            &|d, j, ih| {
                // goal ≡ add (mul n j) n = mul (succ j) n
                let nj = d.mul(n, j);
                let start = d.add(nj, n);
                let jn = d.mul(j, n);
                let s1 = d.add(jn, n);
                let h1 = d.congr(nj, jn, ih, &|d, t| d.add(t, n));
                let sj = d.succ(j);
                let s2 = d.mul(sj, n);
                let h_sm = d.lem("succ_mul", &[j, n]);
                let h2 = d.symm(s2, s1, h_sm);
                let (_end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
                proof
            },
            m,
        );
        (stmt, proof)
    });

    // mul_one : ∀ a, mul a 1 = a
    // mul a (succ zero) ≡ add (mul a zero) a ≡ add zero a, so `zero_add a`
    // already has this type up to definitional equality.
    d.theorem("mul_one", 1, &|d, v| {
        let a = v[0];
        let one = d.num(1);
        let lhs = d.mul(a, one);
        let stmt = d.eq(lhs, a);
        let proof = d.lem("zero_add", &[a]);
        (stmt, proof)
    });

    // one_mul : ∀ a, mul 1 a = a
    d.theorem("one_mul", 1, &|d, v| {
        let a = v[0];
        let one = d.num(1);
        let z = d.zero();
        let start = d.mul(one, a);
        let za = d.mul(z, a);
        let s1 = d.add(za, a);
        let h1 = d.lem("succ_mul", &[z, a]);
        let s2 = d.add(z, a);
        let h_zm = d.lem("zero_mul", &[a]);
        let h2 = d.congr(za, z, h_zm, &|d, t| d.add(t, a));
        let h3 = d.lem("zero_add", &[a]);
        let (end, proof) = d.chain(start, &[(s1, h1), (s2, h2), (a, h3)]);
        let stmt = d.eq(start, end);
        (stmt, proof)
    });

    // left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)  (ind. on c)
    d.theorem("left_distrib", 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let p = |d: &mut Dev, x: ExprId| {
            let bx = d.add(b, x);
            let lhs = d.mul(a, bx);
            let ab = d.mul(a, b);
            let ax = d.mul(a, x);
            let rhs = d.add(ab, ax);
            d.eq(lhs, rhs)
        };
        let stmt = p(d, c);
        let proof = d.induct(
            &p,
            &|d| {
                let ab = d.mul(a, b);
                d.refl(ab)
            },
            &|d, j, ih| {
                // goal ≡ add (mul a (add b j)) a = add (mul a b) (add (mul a j) a)
                let bj = d.add(b, j);
                let a_bj = d.mul(a, bj);
                let start = d.add(a_bj, a);
                let ab = d.mul(a, b);
                let aj = d.mul(a, j);
                let ab_aj = d.add(ab, aj);
                let s1 = d.add(ab_aj, a);
                let h1 = d.congr(a_bj, ab_aj, ih, &|d, t| d.add(t, a));
                let aj_a = d.add(aj, a);
                let s2 = d.add(ab, aj_a);
                let h2 = d.lem("add_assoc", &[ab, aj, a]);
                let (_end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
                proof
            },
            c,
        );
        (stmt, proof)
    });

    // mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)   (induction on c)
    d.theorem("mul_assoc", 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let p = |d: &mut Dev, x: ExprId| {
            let ab = d.mul(a, b);
            let lhs = d.mul(ab, x);
            let bx = d.mul(b, x);
            let rhs = d.mul(a, bx);
            d.eq(lhs, rhs)
        };
        let stmt = p(d, c);
        let proof = d.induct(
            &p,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            &|d, j, ih| {
                // goal ≡ add (mul (mul a b) j) (mul a b) = mul a (add (mul b j) b)
                let ab = d.mul(a, b);
                let abj = d.mul(ab, j);
                let start = d.add(abj, ab);
                let bj = d.mul(b, j);
                let a_bj = d.mul(a, bj);
                let s1 = d.add(a_bj, ab);
                let h1 = d.congr(abj, a_bj, ih, &|d, t| d.add(t, ab));
                let bj_b = d.add(bj, b);
                let s2 = d.mul(a, bj_b);
                let h_ld = d.lem("left_distrib", &[a, bj, b]);
                let h2 = d.symm(s2, s1, h_ld);
                let (_end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
                proof
            },
            c,
        );
        (stmt, proof)
    });
}

/// `geo_shift : ∀ a m, a * G(a,m) = Σ_{i=1..m} a^i` — the bridge between the
/// geometric sum `G(a,m) = Σ_{i<m} a^i` used in the induction and the bracket
/// `a^(k-2) + … + a` the shell construction is written with. By induction on `m`.
fn lemma_geo_shift(d: &mut Dev) -> ExprId {
    d.theorem("geo_shift", 2, &|d, v| {
        let (a, m) = (v[0], v[1]);
        let p = |d: &mut Dev, x: ExprId| {
            let g = d.geo(a, x);
            let lhs = d.mul(a, g);
            let rhs = d.geo1(a, x);
            d.eq(lhs, rhs)
        };
        let stmt = p(d, m);
        let proof = d.induct(
            &p,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            &|d, j, ih| {
                // goal ≡ mul a (add G P') = add (geo1 a j) (mul P' a)
                let g = d.geo(a, j);
                let pw = d.pow(a, j);
                let gp = d.add(g, pw);
                let start = d.mul(a, gp);
                let ag = d.mul(a, g);
                let ap = d.mul(a, pw);
                let s1 = d.add(ag, ap);
                let h1 = d.lem("left_distrib", &[a, g, pw]);
                let g1 = d.geo1(a, j);
                let s2 = d.add(g1, ap);
                let h2 = d.congr(ag, g1, ih, &|d, t| d.add(t, ap));
                let pa = d.mul(pw, a);
                let s3 = d.add(g1, pa);
                let h_mc = d.lem("mul_comm", &[a, pw]);
                let h3 = d.congr(ap, pa, h_mc, &|d, t| d.add(g1, t));
                let (_e, proof) = d.chain(start, &[(s1, h1), (s2, h2), (s3, h3)]);
                proof
            },
            m,
        );
        (stmt, proof)
    })
}

/// THEOREM D — the shell size in the construction's own notation:
/// `N = b * (a^(k-1) + 2 * (a^(k-2) + … + a))` with `m = k - 2`.
fn theorem_nshell_paper_form(d: &mut Dev) -> ExprId {
    d.theorem("nshell_paper_form", 3, &|d, v| {
        let (a, b, m) = (v[0], v[1], v[2]);
        let two = d.num(2);
        let sm = d.succ(m);
        let pw = d.pow(a, sm);
        let g = d.geo(a, m);
        let ag = d.mul(a, g);
        let g1 = d.geo1(a, m);
        let closed_g = {
            let t = d.mul(two, ag);
            d.add(pw, t)
        };
        let closed_g1 = {
            let t = d.mul(two, g1);
            d.add(pw, t)
        };
        let lhs = d.nshell(a, b, m);
        let rhs = d.mul(b, closed_g1);
        let stmt = d.eq(lhs, rhs);

        let sh = d.shell(a, m);
        let h1 = d.lem("shell_closed_form", &[a, m]);
        let h_shift = d.lem("geo_shift", &[a, m]);
        let h2 = d.congr(ag, g1, h_shift, &|d, t| {
            let inner = d.mul(two, t);
            d.add(pw, inner)
        });
        let (_e, inner) = d.chain(sh, &[(closed_g, h1), (closed_g1, h2)]);
        let proof = d.congr(sh, closed_g1, inner, &|d, t| d.mul(b, t));
        (stmt, proof)
    })
}

/// THEOREM E — the *sufficiency* half of the solution-form lemma for
/// `E(a,b) : a(x − y) = b z`: every triple of the form `x = y + b*t`, `z = a*t`
/// is a solution, for all `a, b, y, t`. (The converse needs `gcd(a,b) = 1` and
/// is out of reach here — see the report.)
fn theorem_solution_family(d: &mut Dev) -> ExprId {
    d.theorem("solution_family", 4, &|d, v| {
        let (a, b, y, t) = (v[0], v[1], v[2], v[3]);
        let bt = d.mul(b, t);
        let x = d.add(y, bt);
        let start = d.mul(a, x);
        let ay = d.mul(a, y);
        let at = d.mul(a, t);
        let bat = d.mul(b, at);
        let goal_rhs = d.add(ay, bat);

        let abt = d.mul(a, bt);
        let s1 = d.add(ay, abt);
        let h1 = d.lem("left_distrib", &[a, y, bt]);
        let h_inner = {
            let ab = d.mul(a, b);
            let ab_t = d.mul(ab, t);
            let h_ma = d.lem("mul_assoc", &[a, b, t]);
            let u1 = d.symm(ab_t, abt, h_ma);
            let ba = d.mul(b, a);
            let ba_t = d.mul(ba, t);
            let h_mc = d.lem("mul_comm", &[a, b]);
            let u2 = d.congr(ab, ba, h_mc, &|d, s| d.mul(s, t));
            let h_ma2 = d.lem("mul_assoc", &[b, a, t]);
            let (_e, pf) = d.chain(abt, &[(ab_t, u1), (ba_t, u2), (bat, h_ma2)]);
            pf
        };
        let s2 = d.add(ay, bat);
        let h2 = d.congr(abt, bat, h_inner, &|d, s| d.add(ay, s));
        let (end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
        assert_eq!(end, goal_rhs, "chain must land exactly on the claimed RHS");
        let stmt = d.eq(start, goal_rhs);
        (stmt, proof)
    })
}

/// THEOREM A — the closed-form defect family solves `E(a,b)` for all `a,b`.
fn theorem_defect_identity(d: &mut Dev) -> ExprId {
    d.theorem("defect_identity", 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let one = d.num(1);
        // x = a*b*b + 1, y = 1, z = a*a*b ; claim a*x = a*y + b*z.
        let bb = d.mul(b, b);
        let x_core = d.mul(a, bb); // a*(b*b)
        let x = d.add(x_core, one);
        let start = d.mul(a, x);
        let aa = d.mul(a, a);
        let aab = d.mul(aa, b);
        let z = d.mul(b, aab); // b*((a*a)*b)
        let a_one = d.mul(a, one);
        let goal_rhs = d.add(a_one, z);

        // a*(a*b² + 1) = a*(a*b²) + a*1
        let ax = d.mul(a, x_core);
        let s1 = d.add(ax, a_one);
        let h1 = d.lem("left_distrib", &[a, x_core, one]);
        // ... = a*(a*b²) + a
        let s2 = d.add(ax, a);
        let h_mo = d.lem("mul_one", &[a]);
        let h2 = d.congr(a_one, a, h_mo, &|d, t| d.add(ax, t));
        // ... = a + a*(a*b²)
        let s3 = d.add(a, ax);
        let h3 = d.lem("add_comm", &[ax, a]);
        // ... = a*1 + a*(a*b²)
        let s4 = d.add(a_one, ax);
        let h_mo2 = d.lem("mul_one", &[a]);
        let h_mo2 = d.symm(a_one, a, h_mo2);
        let h4 = d.congr(a, a_one, h_mo2, &|d, t| d.add(t, ax));
        // a*(a*b²) = b*(a²*b)
        let h_xz = {
            let u_start = ax; // a*(a*(b*b))
            let aa_bb = d.mul(aa, bb);
            let h_ma = d.lem("mul_assoc", &[a, a, bb]);
            let u1 = d.symm(aa_bb, ax, h_ma);
            let aab_b = d.mul(aab, b);
            let h_ma2 = d.lem("mul_assoc", &[aa, b, b]);
            let u2 = d.symm(aab_b, aa_bb, h_ma2);
            let h_mc = d.lem("mul_comm", &[aab, b]);
            let (_e, p) = d.chain(u_start, &[(aa_bb, u1), (aab_b, u2), (z, h_mc)]);
            p
        };
        let s5 = d.add(a_one, z);
        let h5 = d.congr(ax, z, h_xz, &|d, t| d.add(a_one, t));

        let (end, proof) = d.chain(start, &[(s1, h1), (s2, h2), (s3, h3), (s4, h4), (s5, h5)]);
        assert_eq!(end, goal_rhs, "chain must land exactly on the claimed RHS");
        let stmt = d.eq(start, goal_rhs);
        (stmt, proof)
    })
}

/// THEOREM B — the geometric-sum closed form, by induction on `k`.
fn theorem_geo_closed_form(d: &mut Dev) -> ExprId {
    d.theorem("geo_closed_form", 2, &|d, v| {
        let (a, k) = (v[0], v[1]);
        let p = |d: &mut Dev, x: ExprId| {
            let g = d.geo(a, x);
            let ag = d.mul(a, g);
            let one = d.num(1);
            let lhs = d.add(ag, one);
            let pw = d.pow(a, x);
            let rhs = d.add(g, pw);
            d.eq(lhs, rhs)
        };
        let stmt = p(d, k);
        let proof = d.induct(
            &p,
            // base: geo a 0 ≡ 0, pow a 0 ≡ 1, so both sides ≡ 1.
            &|d| {
                let one = d.num(1);
                d.refl(one)
            },
            &|d, j, ih| {
                let one = d.num(1);
                let g = d.geo(a, j);
                let pw = d.pow(a, j);
                // geo a (succ j) ≡ add g pw ; pow a (succ j) ≡ mul pw a
                let gp = d.add(g, pw);
                let a_gp = d.mul(a, gp);
                let start = d.add(a_gp, one);
                let ag = d.mul(a, g);
                let ap = d.mul(a, pw);
                let ag_ap = d.add(ag, ap);
                let s1 = d.add(ag_ap, one);
                let h_ld = d.lem("left_distrib", &[a, g, pw]);
                let h1 = d.congr(a_gp, ag_ap, h_ld, &|d, t| d.add(t, one));
                let ag_one = d.add(ag, one);
                let s2 = d.add(ag_one, ap);
                let h2 = d.lem("add_right_comm", &[ag, ap, one]);
                let s3 = d.add(gp, ap);
                let h3 = d.congr(ag_one, gp, ih, &|d, t| d.add(t, ap));
                let pa = d.mul(pw, a);
                let s4 = d.add(gp, pa);
                let h_mc = d.lem("mul_comm", &[a, pw]);
                let h4 = d.congr(ap, pa, h_mc, &|d, t| d.add(gp, t));
                let (_e, proof) = d.chain(start, &[(s1, h1), (s2, h2), (s3, h3), (s4, h4)]);
                proof
            },
            k,
        );
        (stmt, proof)
    })
}

/// THEOREM C — the shell level-capacity recurrence equals the construction's
/// closed form `a^(m+1) + 2*(a*G(a,m))`, by induction on `m`, using THEOREM B.
fn theorem_shell_closed_form(d: &mut Dev) -> ExprId {
    d.theorem("shell_closed_form", 2, &|d, v| {
        let (a, m) = (v[0], v[1]);
        let p = |d: &mut Dev, x: ExprId| {
            let lhs = d.shell(a, x);
            let sx = d.succ(x);
            let pw = d.pow(a, sx);
            let g = d.geo(a, x);
            let ag = d.mul(a, g);
            let two = d.num(2);
            let tag = d.mul(two, ag);
            let rhs = d.add(pw, tag);
            d.eq(lhs, rhs)
        };
        let stmt = p(d, m);
        let proof = d.induct(
            &p,
            // base: shellT a 0 ≡ a ; RHS ≡ add (mul 1 a) 0 ≡ mul 1 a.
            &|d| {
                let one = d.num(1);
                let one_a = d.mul(one, a);
                let h = d.lem("one_mul", &[a]);
                d.symm(one_a, a, h)
            },
            &|d, j, ih| {
                let one = d.num(1);
                let two = d.num(2);
                let sj = d.succ(j);
                let big_p = d.pow(a, sj); // P  = a^(j+1)
                let small_p = d.pow(a, j); // P' = a^j
                let g = d.geo(a, j); // G
                let ag = d.mul(a, g); // a*G
                let two_ag = d.mul(two, ag); // 2*(a*G)
                let cf = d.add(big_p, two_ag); // the closed form at j
                let two_a = d.mul(two, a);

                // LHS ≡ add (mul a (shellT a j)) (2*a)
                let sh = d.shell(a, j);
                let a_sh = d.mul(a, sh);
                let start = d.add(a_sh, two_a);

                // (1) rewrite by the induction hypothesis under `a * _`
                let a_cf = d.mul(a, cf);
                let s1 = d.add(a_cf, two_a);
                let h_ih = d.congr(sh, cf, ih, &|d, t| d.mul(a, t));
                let h1 = d.congr(a_sh, a_cf, h_ih, &|d, t| d.add(t, two_a));

                // (2) distribute a over the closed form
                let a_bigp = d.mul(a, big_p);
                let a_twoag = d.mul(a, two_ag);
                let sum = d.add(a_bigp, a_twoag);
                let s2 = d.add(sum, two_a);
                let h_ld = d.lem("left_distrib", &[a, big_p, two_ag]);
                let h2 = d.congr(a_cf, sum, h_ld, &|d, t| d.add(t, two_a));

                // (3) a*(2*(a*G)) = 2*(a*(a*G))
                let sq = d.mul(a, ag); // S = a*(a*G)
                let two_sq = d.mul(two, sq);
                let h3_inner = {
                    let a_two = d.mul(a, two);
                    let at_ag = d.mul(a_two, ag);
                    let h_ma = d.lem("mul_assoc", &[a, two, ag]);
                    let u1 = d.symm(at_ag, a_twoag, h_ma);
                    let ta_ag = d.mul(two_a, ag);
                    let h_mc = d.lem("mul_comm", &[a, two]);
                    let u2 = d.congr(a_two, two_a, h_mc, &|d, t| d.mul(t, ag));
                    let h_ma2 = d.lem("mul_assoc", &[two, a, ag]);
                    let (_e, pf) = d.chain(a_twoag, &[(at_ag, u1), (ta_ag, u2), (two_sq, h_ma2)]);
                    pf
                };
                let sum2 = d.add(a_bigp, two_sq);
                let s3 = d.add(sum2, two_a);
                let h3 = d.congr(a_twoag, two_sq, h3_inner, &|d, t| {
                    let inner = d.add(a_bigp, t);
                    d.add(inner, two_a)
                });

                // (4) reassociate: (a*P + 2*S) + 2*a = a*P + (2*S + 2*a)
                let tail = d.add(two_sq, two_a);
                let s4 = d.add(a_bigp, tail);
                let h4 = d.lem("add_assoc", &[a_bigp, two_sq, two_a]);

                // (5) 2*S + 2*a = 2*(S + a)
                let sq_a = d.add(sq, a);
                let two_sqa = d.mul(two, sq_a);
                let h_ld2 = d.lem("left_distrib", &[two, sq, a]);
                let h5_inner = d.symm(two_sqa, tail, h_ld2);
                let s5 = d.add(a_bigp, two_sqa);
                let h5 = d.congr(tail, two_sqa, h5_inner, &|d, t| d.add(a_bigp, t));

                // (6) S + a = a*(a*G + 1) = a*(G + P')   <- THEOREM B enters here
                let ag_one = d.add(ag, one);
                let a_agone = d.mul(a, ag_one);
                let h6_inner = {
                    // a*(a*G + 1) = a*(a*G) + a*1 = S + a
                    let a_one = d.mul(a, one);
                    let sum_a1 = d.add(sq, a_one);
                    let h_ld3 = d.lem("left_distrib", &[a, ag, one]);
                    let h_mo = d.lem("mul_one", &[a]);
                    let u2 = d.congr(a_one, a, h_mo, &|d, t| d.add(sq, t));
                    let (_e, fwd) = d.chain(a_agone, &[(sum_a1, h_ld3), (sq_a, u2)]);
                    // reverse it: S + a = a*(a*G + 1)
                    let back = d.symm(a_agone, sq_a, fwd);
                    // then rewrite by THEOREM B under `a * _`
                    let g_p = d.add(g, small_p);
                    let a_gp = d.mul(a, g_p);
                    let h_geo = d.lem("geo_closed_form", &[a, j]);
                    let u3 = d.congr(ag_one, g_p, h_geo, &|d, t| d.mul(a, t));
                    let (_e2, pf) = d.chain(sq_a, &[(a_agone, back), (a_gp, u3)]);
                    pf
                };
                let g_p = d.add(g, small_p);
                let a_gp = d.mul(a, g_p);
                let two_agp = d.mul(two, a_gp);
                let s6 = d.add(a_bigp, two_agp);
                let h6 = d.congr(sq_a, a_gp, h6_inner, &|d, t| {
                    let inner = d.mul(two, t);
                    d.add(a_bigp, inner)
                });

                // (7) a*P = P*a  (so the head is definitionally a^(j+2))
                let pa = d.mul(big_p, a);
                let s7 = d.add(pa, two_agp);
                let h_mc2 = d.lem("mul_comm", &[a, big_p]);
                let h7 = d.congr(a_bigp, pa, h_mc2, &|d, t| d.add(t, two_agp));

                let (_e, proof) = d.chain(
                    start,
                    &[
                        (s1, h1),
                        (s2, h2),
                        (s3, h3),
                        (s4, h4),
                        (s5, h5),
                        (s6, h6),
                        (s7, h7),
                    ],
                );
                proof
            },
            m,
        );
        (stmt, proof)
    })
}

/// THEOREM C' — the same with the `b` factor: the construction's
/// `N = b*(a^(k-1) + 2*(a^(k-2) + … + a))`.
fn theorem_nshell_closed_form(d: &mut Dev) -> ExprId {
    d.theorem("nshell_closed_form", 3, &|d, v| {
        let (a, b, m) = (v[0], v[1], v[2]);
        let lhs = d.nshell(a, b, m);
        let sh = d.shell(a, m);
        let sm = d.succ(m);
        let pw = d.pow(a, sm);
        let g = d.geo(a, m);
        let ag = d.mul(a, g);
        let two = d.num(2);
        let tag = d.mul(two, ag);
        let cf = d.add(pw, tag);
        let rhs = d.mul(b, cf);
        let stmt = d.eq(lhs, rhs);
        let h = d.lem("shell_closed_form", &[a, m]);
        let proof = d.congr(sh, cf, h, &|d, t| d.mul(b, t));
        (stmt, proof)
    })
}

/// The complete development: definitions, lemmas, and the theorems.
fn full_development() -> Dev {
    let mut d = Dev::new();
    definitions(&mut d);
    lemmas(&mut d);
    theorem_solution_family(&mut d);
    theorem_defect_identity(&mut d);
    theorem_geo_closed_form(&mut d);
    theorem_shell_closed_form(&mut d);
    theorem_nshell_closed_form(&mut d);
    lemma_geo_shift(&mut d);
    theorem_nshell_paper_form(&mut d);
    d
}

/// Every theorem statement this development admits, rendered.
const THEOREM_NAMES: [&str; 6] = [
    "solution_family",
    "defect_identity",
    "geo_closed_form",
    "shell_closed_form",
    "nshell_closed_form",
    "nshell_paper_form",
];

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// The definitions compute the values the orchestrator's brief measured by
/// enumeration: `N_shell(3,2,3) = 30` (so `R_3 > 30`, `N+1 = 31`) and
/// `N_shell(4,3,3) = 72` (`N+1 = 73`). Checked by the kernel's own `def_eq`
/// (δ/β/ι reduction), not by a Rust-side evaluator.
#[test]
fn definitions_compute_the_measured_shell_values() {
    let mut d = Dev::new();
    definitions(&mut d);

    // pow 3 3 = 27, geo 3 3 = 1 + 3 + 9 = 13
    let three = d.num(3);
    let p = d.pow(three, three);
    let twenty_seven = d.num(27);
    assert!(d.k.def_eq(p, twenty_seven), "pow 3 3 must reduce to 27");
    let g = d.geo(three, three);
    let thirteen = d.num(13);
    assert!(d.k.def_eq(g, thirteen), "geo 3 3 must reduce to 13");

    // shellT 3 1 = 3*3 + 2*3 = 15   (this is T(k=3) for a=3)
    let one = d.num(1);
    let t = d.shell(three, one);
    let fifteen = d.num(15);
    assert!(d.k.def_eq(t, fifteen), "shellT 3 1 must reduce to 15");

    // N_shell(a=3,b=2,k=3) = 2 * 15 = 30  → the brief's row (3,2,3): N+1 = 31
    let two = d.num(2);
    let n = d.nshell(three, two, one);
    let thirty = d.num(30);
    assert!(d.k.def_eq(n, thirty), "nshell 3 2 1 must reduce to 30");

    // N_shell(a=4,b=3,k=3) = 3 * (4*4 + 2*4) = 72 → the brief's row (4,3,3): 73
    let four = d.num(4);
    let n2 = d.nshell(four, three, one);
    let seventy_two = d.num(72);
    assert!(
        d.k.def_eq(n2, seventy_two),
        "nshell 4 3 1 must reduce to 72"
    );

    // And the closed form agrees numerically at the same point:
    // a^(m+1) + 2*(a*G(a,m)) at a=3, m=1 is 9 + 2*(3*1) = 15.
    let two_m = d.num(2);
    let pw = d.pow(three, two_m);
    let gg = d.geo(three, one);
    let agg = d.mul(three, gg);
    let t2 = d.mul(two, agg);
    let closed = d.add(pw, t2);
    assert!(
        d.k.def_eq(closed, fifteen),
        "closed form at (3,1) must be 15"
    );

    // N_shell(3,2,4) = 2 * (3*15 + 6) = 102 → the brief's row (3,2,4): N+1 = 103.
    let n3 = d.nshell(three, two, two_m);
    let one_hundred_two = d.num(102);
    assert!(
        d.k.def_eq(n3, one_hundred_two),
        "nshell 3 2 2 must reduce to 102"
    );

    // NEGATIVE reduction control: def_eq is not vacuously true.
    let one_hundred_three = d.num(103);
    assert!(
        !d.k.def_eq(n3, one_hundred_three),
        "nshell 3 2 2 must NOT be def-eq to 103"
    );
    let twenty_six = d.num(26);
    assert!(
        !d.k.def_eq(p, twenty_six),
        "pow 3 3 must NOT be def-eq to 26"
    );

    // N_shell(4,3,4) = 3 * (4*24 + 8) = 312 → the brief's row (4,3,4): N+1 = 313.
    let n4 = d.nshell(four, three, two_m);
    let three_twelve = d.num(312);
    assert!(
        d.k.def_eq(n4, three_twelve),
        "nshell 4 3 2 must reduce to 312"
    );

    // geo1 3 3 = 3 + 9 + 27 = 39, and it agrees with a * geo 3 3 = 3 * 13.
    let g1 = d.geo1(three, three);
    let thirty_nine = d.num(39);
    assert!(d.k.def_eq(g1, thirty_nine), "geo1 3 3 must reduce to 39");
    let a_geo = d.mul(three, g);
    assert!(d.k.def_eq(a_geo, g1), "3 * geo 3 3 must equal geo1 3 3");
}

/// THEOREM A: the closed-form defect family solves `E(a,b)` for **all** `a,b`.
#[test]
fn kernel_checks_the_defect_family_identity() {
    let mut d = Dev::new();
    definitions(&mut d);
    lemmas(&mut d);
    let ty = theorem_defect_identity(&mut d);
    println!("defect_identity : {}", d.k.render_lean(ty));
    let name = d.name("defect_identity");
    assert!(d.k.environment().contains(name));
}

/// THEOREM B: the geometric-sum closed form, by `Nat.rec` induction.
#[test]
fn kernel_checks_the_geometric_sum_closed_form() {
    let mut d = Dev::new();
    definitions(&mut d);
    lemmas(&mut d);
    let ty = theorem_geo_closed_form(&mut d);
    println!("geo_closed_form : {}", d.k.render_lean(ty));
    let name = d.name("geo_closed_form");
    assert!(d.k.environment().contains(name));
}

/// THEOREM C / C' / D: the shell size closed form, by induction, using THEOREM B;
/// and every statement the development admits, rendered for the record.
#[test]
fn kernel_checks_the_shell_size_closed_form() {
    let mut d = full_development();
    for name in THEOREM_NAMES {
        let n = d.name(name);
        let ty =
            d.k.environment()
                .get(n)
                .unwrap_or_else(|| panic!("{name} must be admitted"))
                .ty();
        println!("{name} : {}", d.k.render_lean(ty));
    }
}

/// The honesty control: this development declares **no axioms**. Its trusted
/// base is the kernel plus the inductive declarations of the logic prelude.
#[test]
fn the_development_declares_no_axioms() {
    let mut d = full_development();
    let axioms: Vec<String> =
        d.k.environment()
            .iter()
            .filter_map(|(_, decl)| match decl {
                Declaration::Axiom { name, .. } => Some(d.k.display_name(*name).to_string()),
                _ => None,
            })
            .collect();
    println!("axiom population: {axioms:?}");
    assert!(
        axioms.is_empty(),
        "the development must rest on zero axioms, found: {axioms:?}"
    );

    // ... and the theorems really are in the environment as checked Theorems.
    for name in THEOREM_NAMES {
        let n = d.name(name);
        assert!(
            matches!(d.k.environment().get(n), Some(Declaration::Theorem { .. })),
            "{name} must be a checked Theorem"
        );
    }
}

/// CAPABILITY PROBE — the infrastructure a full correctness proof would need.
///
/// The shell construction's *solution-freeness* argument needs an order (`≤`),
/// divisibility, and `a`-adic valuations. None of that exists in this kernel's
/// preludes. The question this probe answers is whether that is a **kernel**
/// limit or a **library** limit: can a user declare an indexed `Prop`-valued
/// inductive relation through the trusted gate and eliminate with its generated
/// recursor?
///
/// It declares `Le : Nat → Nat → Prop` (one parameter, one index, two
/// constructors), proves `∀ n, Le zero n` by `Nat.rec` induction, and proves
/// `∀ n m, Le n m → Le (succ n) (succ m)` by induction on the **derivation**
/// with the generated `Le.rec`.
#[test]
fn capability_probe_indexed_prop_relation_and_its_recursor() {
    let mut d = Dev::new();
    definitions(&mut d);
    let nat = d.nat_ty;
    let anon = d.anon;
    let prop = d.k.sort_zero();

    // Le : Nat → Nat → Prop, with `n` a parameter and `m` an index.
    let le = d.name("Le");
    let le_refl = d.k.name_str(le, "refl");
    let le_step = d.k.name_str(le, "step");
    let le_ty = {
        let inner = d.k.pi(anon, nat, prop, BinderInfo::Default);
        d.k.pi(anon, nat, inner, BinderInfo::Default)
    };
    // Le.refl : Π (n : Nat), Le n n
    let refl_ty = {
        let n_fv = d.fresh();
        let n = d.k.fvar(n_fv);
        let c = d.k.const_(le, vec![]);
        let body = d.apply(c, &[n, n]);
        d.pi_fv(n_fv, nat, body)
    };
    // Le.step : Π (n : Nat) (m : Nat), Le n m → Le n (succ m)
    let step_ty = {
        let n_fv = d.fresh();
        let n = d.k.fvar(n_fv);
        let m_fv = d.fresh();
        let m = d.k.fvar(m_fv);
        let c = d.k.const_(le, vec![]);
        let hyp = d.apply(c, &[n, m]);
        let sm = d.succ(m);
        let c2 = d.k.const_(le, vec![]);
        let concl = d.apply(c2, &[n, sm]);
        let arrow = d.k.pi(anon, hyp, concl, BinderInfo::Default);
        let over_m = d.pi_fv(m_fv, nat, arrow);
        d.pi_fv(n_fv, nat, over_m)
    };
    d.k.add_inductive(le, &[], 1, le_ty, &[(le_refl, refl_ty), (le_step, step_ty)])
        .expect("an indexed Prop relation must admit through the trusted gate");
    let le_rec = d.k.name_str(le, "rec");
    println!(
        "Le.rec : {}",
        d.k.render_lean(
            d.k.environment()
                .get(le_rec)
                .expect("Le.rec generated")
                .ty()
        )
    );

    let mk_le = |d: &mut Dev, a: ExprId, b: ExprId| {
        let c = d.k.const_(le, vec![]);
        d.apply(c, &[a, b])
    };

    // zero_le : ∀ n, Le zero n   (induction on n, using only the constructors)
    {
        let n_fv = d.fresh();
        let n = d.k.fvar(n_fv);
        let p = |d: &mut Dev, x: ExprId| {
            let z = d.zero();
            mk_le(d, z, x)
        };
        let stmt = p(&mut d, n);
        let proof = d.induct(
            &p,
            &|d| {
                let z = d.zero();
                let c = d.k.const_(le_refl, vec![]);
                d.k.app(c, z)
            },
            &|d, j, ih| {
                let z = d.zero();
                let c = d.k.const_(le_step, vec![]);
                d.apply(c, &[z, j, ih])
            },
            n,
        );
        let ty = d.pi_fv(n_fv, nat, stmt);
        let value = d.lam_fv(n_fv, nat, proof);
        let name = d.name("zero_le");
        d.k.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|e| panic!("zero_le rejected: {}", d.explain(&e)));
        println!("zero_le : {}", d.k.render_lean(ty));
    }

    // le_succ_succ : ∀ n m, Le n m → Le (succ n) (succ m)
    // — induction on the DERIVATION, i.e. elimination with the generated Le.rec.
    {
        let n_fv = d.fresh();
        let n = d.k.fvar(n_fv);
        let m_fv = d.fresh();
        let m = d.k.fvar(m_fv);
        let h_fv = d.fresh();
        let h = d.k.fvar(h_fv);
        let hyp = mk_le(&mut d, n, m);
        let sn = d.succ(n);
        let sm = d.succ(m);
        let concl = mk_le(&mut d, sn, sm);

        // motive := fun (x : Nat) (_ : Le n x) => Le (succ n) (succ x)
        let motive = {
            let x_fv = d.fresh();
            let x = d.k.fvar(x_fv);
            let sx = d.succ(x);
            let body = mk_le(&mut d, sn, sx);
            let dom = mk_le(&mut d, n, x);
            let inner = d.k.lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        // minor for Le.refl : motive n (Le.refl n) = Le (succ n) (succ n)
        let minor_refl = {
            let c = d.k.const_(le_refl, vec![]);
            d.k.app(c, sn)
        };
        // minor for Le.step : Π (x : Nat) (hx : Le n x), motive x hx → motive (succ x) …
        let minor_step = {
            let x_fv = d.fresh();
            let x = d.k.fvar(x_fv);
            let hx_fv = d.fresh();
            let hx_ty = mk_le(&mut d, n, x);
            let ih_fv = d.fresh();
            let ih = d.k.fvar(ih_fv);
            let sx = d.succ(x);
            let ih_ty = mk_le(&mut d, sn, sx);
            let c = d.k.const_(le_step, vec![]);
            let body = d.apply(c, &[sn, sx, ih]);
            let l_ih = d.lam_fv(ih_fv, ih_ty, body);
            let l_hx = d.lam_fv(hx_fv, hx_ty, l_ih);
            d.lam_fv(x_fv, nat, l_hx)
        };
        let rec = d.k.const_(le_rec, vec![]);
        let applied = d.apply(rec, &[n, motive, minor_refl, minor_step, m, h]);

        let ty = {
            let arrow = d.k.pi(anon, hyp, concl, BinderInfo::Default);
            let over_m = d.pi_fv(m_fv, nat, arrow);
            d.pi_fv(n_fv, nat, over_m)
        };
        let value = {
            let l_h = d.lam_fv(h_fv, hyp, applied);
            let l_m = d.lam_fv(m_fv, nat, l_h);
            d.lam_fv(n_fv, nat, l_m)
        };
        let name = d.name("le_succ_succ");
        d.k.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|e| panic!("le_succ_succ rejected: {}", d.explain(&e)));
        println!("le_succ_succ : {}", d.k.render_lean(ty));
    }

    // Negative control for the probe: `Le (succ n) n` must NOT be derivable by
    // the same shape of term (the constructor produces `Le n (succ m)`).
    {
        let n_fv = d.fresh();
        let n = d.k.fvar(n_fv);
        let sn = d.succ(n);
        let bad_stmt = mk_le(&mut d, sn, n);
        let c = d.k.const_(le_refl, vec![]);
        let bogus = d.k.app(c, n);
        let ty = d.pi_fv(n_fv, nat, bad_stmt);
        let value = d.lam_fv(n_fv, nat, bogus);
        let name = d.name("nc6_succ_le_self");
        let err =
            d.k.add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            })
            .expect_err("NC6: `Le (succ n) n` must be rejected");
        println!("NC6 (bogus order fact) rejected:\n  {}", d.explain(&err));
    }
}

/// CAPABILITY PROBE 2 — existential machinery, i.e. the first step of the
/// divisibility/valuation layer the shell construction's colouring is defined by
/// (`χ(j) = min(v(j), k)` for `a | j`).
///
/// Defines `dvd a n := ∃ q, n = a * q` with the prelude's `Exists`, then proves
/// `a ∣ a*q` (existential **introduction**) and
/// `a ∣ m → a ∣ n → a ∣ (m + n)` (existential **elimination** through
/// `Exists.rec`, twice, plus `left_distrib`).
#[test]
fn capability_probe_existential_divisibility() {
    let mut d = Dev::new();
    definitions(&mut d);
    lemmas(&mut d);
    let nat = d.nat_ty;
    let anon = d.anon;
    let prop = d.k.sort_zero();
    let one_lvl = d.level_one();
    let exists_name = d.logic.exists_;
    let intro_name = d.logic.exists_intro;
    let rec_name = d.logic.exists_rec;

    // dvd : Nat → Nat → Prop := fun a n => Exists Nat (fun q => Eq Nat n (a*q))
    let dvd = d.name("dvd");
    {
        let a_fv = d.fresh();
        let a = d.k.fvar(a_fv);
        let n_fv = d.fresh();
        let n = d.k.fvar(n_fv);
        let pred = {
            let q_fv = d.fresh();
            let q = d.k.fvar(q_fv);
            let aq = d.mul(a, q);
            let body = d.eq(n, aq);
            d.lam_fv(q_fv, nat, body)
        };
        let ex = d.k.const_(exists_name, vec![one_lvl]);
        let body = d.apply(ex, &[nat, pred]);
        let value = {
            let v = d.lam_fv(n_fv, nat, body);
            d.lam_fv(a_fv, nat, v)
        };
        let ty = {
            let i = d.k.pi(anon, nat, prop, BinderInfo::Default);
            d.k.pi(anon, nat, i, BinderInfo::Default)
        };
        d.k.add_declaration(Declaration::Definition {
            name: dvd,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(7),
        })
        .expect("dvd should admit");
    }
    let mk_dvd = |d: &mut Dev, a: ExprId, n: ExprId| {
        let c = d.k.const_(dvd, vec![]);
        d.apply(c, &[a, n])
    };
    // `fun q => Eq Nat target (a * q)` — the predicate `dvd a target` unfolds to.
    let mk_pred = |d: &mut Dev, a: ExprId, target: ExprId| {
        let q_fv = d.fresh();
        let q = d.k.fvar(q_fv);
        let aq = d.mul(a, q);
        let body = d.eq(target, aq);
        let nat = d.nat_ty;
        d.lam_fv(q_fv, nat, body)
    };

    // dvd_mul : ∀ a q, dvd a (a * q)   — existential introduction.
    {
        let a_fv = d.fresh();
        let a = d.k.fvar(a_fv);
        let q_fv = d.fresh();
        let q = d.k.fvar(q_fv);
        let aq = d.mul(a, q);
        let stmt = mk_dvd(&mut d, a, aq);
        let pred = mk_pred(&mut d, a, aq);
        let witness_proof = d.refl(aq);
        let intro = d.k.const_(intro_name, vec![one_lvl]);
        let proof = d.apply(intro, &[nat, pred, q, witness_proof]);
        let ty = {
            let i = d.pi_fv(q_fv, nat, stmt);
            d.pi_fv(a_fv, nat, i)
        };
        let value = {
            let v = d.lam_fv(q_fv, nat, proof);
            d.lam_fv(a_fv, nat, v)
        };
        let name = d.name("dvd_mul");
        d.k.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|e| panic!("dvd_mul rejected: {}", d.explain(&e)));
        println!("dvd_mul : {}", d.k.render_lean(ty));
    }

    // dvd_add : ∀ a m n, dvd a m → dvd a n → dvd a (m + n)
    // — double existential elimination through `Exists.rec`.
    let build_dvd_add = |d: &mut Dev, conclusion_target: ExprId, a, m, n, h1, h2| {
        let goal = mk_dvd(d, a, conclusion_target);
        let mn = d.add(m, n);
        let p1 = mk_pred(d, a, m);
        let p2 = mk_pred(d, a, n);
        // motive := fun (_ : Exists Nat p_i) => goal
        let motive_for = |d: &mut Dev, pred: ExprId| {
            let ex = d.k.const_(exists_name, vec![one_lvl]);
            let nat = d.nat_ty;
            let dom = d.apply(ex, &[nat, pred]);
            let anon = d.anon;
            d.k.lam(anon, dom, goal, BinderInfo::Default)
        };
        let minor1 = {
            let q1_fv = d.fresh();
            let q1 = d.k.fvar(q1_fv);
            let aq1 = d.mul(a, q1);
            let e1_fv = d.fresh();
            let e1_ty = d.eq(m, aq1);
            let e1 = d.k.fvar(e1_fv);
            let minor2 = {
                let q2_fv = d.fresh();
                let q2 = d.k.fvar(q2_fv);
                let aq2 = d.mul(a, q2);
                let e2_fv = d.fresh();
                let e2_ty = d.eq(n, aq2);
                let e2 = d.k.fvar(e2_fv);
                // (m + n) = (a*q1) + n = (a*q1) + (a*q2) = a*(q1 + q2)
                let s1 = d.add(aq1, n);
                let c1 = d.congr(m, aq1, e1, &|d, t| d.add(t, n));
                let s2 = d.add(aq1, aq2);
                let c2 = d.congr(n, aq2, e2, &|d, t| d.add(aq1, t));
                let q12 = d.add(q1, q2);
                let a_q12 = d.mul(a, q12);
                let h_ld = d.lem("left_distrib", &[a, q1, q2]);
                let c3 = d.symm(a_q12, s2, h_ld);
                let (_e, witness_proof) = d.chain(mn, &[(s1, c1), (s2, c2), (a_q12, c3)]);
                let pred3 = mk_pred(d, a, conclusion_target);
                let intro = d.k.const_(intro_name, vec![one_lvl]);
                let nat = d.nat_ty;
                let body = d.apply(intro, &[nat, pred3, q12, witness_proof]);
                let l_e2 = d.lam_fv(e2_fv, e2_ty, body);
                let nat = d.nat_ty;
                d.lam_fv(q2_fv, nat, l_e2)
            };
            let motive2 = motive_for(d, p2);
            let rec = d.k.const_(rec_name, vec![one_lvl]);
            let nat = d.nat_ty;
            let inner = d.apply(rec, &[nat, p2, motive2, minor2, h2]);
            let l_e1 = d.lam_fv(e1_fv, e1_ty, inner);
            d.lam_fv(q1_fv, nat, l_e1)
        };
        let motive1 = motive_for(d, p1);
        let rec = d.k.const_(rec_name, vec![one_lvl]);
        let nat = d.nat_ty;
        d.apply(rec, &[nat, p1, motive1, minor1, h1])
    };

    {
        let a_fv = d.fresh();
        let a = d.k.fvar(a_fv);
        let m_fv = d.fresh();
        let m = d.k.fvar(m_fv);
        let n_fv = d.fresh();
        let n = d.k.fvar(n_fv);
        let h1_fv = d.fresh();
        let h1 = d.k.fvar(h1_fv);
        let h2_fv = d.fresh();
        let h2 = d.k.fvar(h2_fv);
        let h1_ty = mk_dvd(&mut d, a, m);
        let h2_ty = mk_dvd(&mut d, a, n);
        let mn = d.add(m, n);
        let concl = mk_dvd(&mut d, a, mn);
        let proof = build_dvd_add(&mut d, mn, a, m, n, h1, h2);
        let ty = {
            let t = d.k.pi(anon, h2_ty, concl, BinderInfo::Default);
            let t = d.pi_fv(h1_fv, h1_ty, t);
            let t = d.pi_fv(n_fv, nat, t);
            let t = d.pi_fv(m_fv, nat, t);
            d.pi_fv(a_fv, nat, t)
        };
        let value = {
            let v = d.lam_fv(h2_fv, h2_ty, proof);
            let v = d.lam_fv(h1_fv, h1_ty, v);
            let v = d.lam_fv(n_fv, nat, v);
            let v = d.lam_fv(m_fv, nat, v);
            d.lam_fv(a_fv, nat, v)
        };
        let name = d.name("dvd_add");
        d.k.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .unwrap_or_else(|e| panic!("dvd_add rejected: {}", d.explain(&e)));
        println!("dvd_add : {}", d.k.render_lean(ty));
    }

    // NC7 — the same proof term against the FALSE conclusion `a ∣ m*n` (false:
    // a=2, m=n=1 gives 2∣1). Must be rejected.
    {
        let a_fv = d.fresh();
        let a = d.k.fvar(a_fv);
        let m_fv = d.fresh();
        let m = d.k.fvar(m_fv);
        let n_fv = d.fresh();
        let n = d.k.fvar(n_fv);
        let h1_fv = d.fresh();
        let h1 = d.k.fvar(h1_fv);
        let h2_fv = d.fresh();
        let h2 = d.k.fvar(h2_fv);
        let h1_ty = mk_dvd(&mut d, a, m);
        let h2_ty = mk_dvd(&mut d, a, n);
        let mn = d.add(m, n);
        let bad = d.mul(m, n);
        let concl = mk_dvd(&mut d, a, bad);
        let proof = build_dvd_add(&mut d, mn, a, m, n, h1, h2);
        let ty = {
            let t = d.k.pi(anon, h2_ty, concl, BinderInfo::Default);
            let t = d.pi_fv(h1_fv, h1_ty, t);
            let t = d.pi_fv(n_fv, nat, t);
            let t = d.pi_fv(m_fv, nat, t);
            d.pi_fv(a_fv, nat, t)
        };
        let value = {
            let v = d.lam_fv(h2_fv, h2_ty, proof);
            let v = d.lam_fv(h1_fv, h1_ty, v);
            let v = d.lam_fv(n_fv, nat, v);
            let v = d.lam_fv(m_fv, nat, v);
            d.lam_fv(a_fv, nat, v)
        };
        let name = d.name("nc7_dvd_mul_false");
        let err =
            d.k.add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            })
            .expect_err("NC7: `a ∣ m*n` must be rejected");
        println!("NC7 (false divisibility conclusion) rejected: {}", {
            match &err {
                KernelError::DeclarationValueMismatch { .. } => "DeclarationValueMismatch",
                KernelError::TypeMismatch { .. } => "TypeMismatch",
                _ => "other",
            }
        });
    }
}

/// NEGATIVE CONTROLS. A checker that accepts everything proves nothing: each of
/// these feeds the kernel a deliberately broken proof and requires a rejection.
#[test]
fn kernel_rejects_broken_proof_terms() {
    let mut rejections = 0usize;

    // NC1 — a correct proof against a FALSE statement (drop a factor of `b`
    // from `z`): `a*(a*b² + 1) = a*1 + b*(a*a)` is false (a=b=2: 18 ≠ 10).
    {
        let mut d = Dev::new();
        definitions(&mut d);
        lemmas(&mut d);
        let err = d
            .try_theorem("nc1_wrong_statement", 2, &|d, v| {
                let (a, b) = (v[0], v[1]);
                let one = d.num(1);
                let bb = d.mul(b, b);
                let x_core = d.mul(a, bb);
                let x = d.add(x_core, one);
                let start = d.mul(a, x);
                let aa = d.mul(a, a);
                let bad_z = d.mul(b, aa); // b*(a*a) — the `*b` is missing
                let a_one = d.mul(a, one);
                let bad_rhs = d.add(a_one, bad_z);
                // The proof term is the *correct* derivation from THEOREM A.
                let aab = d.mul(aa, b);
                let z = d.mul(b, aab);
                let ax = d.mul(a, x_core);
                let s1 = d.add(ax, a_one);
                let h1 = d.lem("left_distrib", &[a, x_core, one]);
                let s2 = d.add(ax, a);
                let h_mo = d.lem("mul_one", &[a]);
                let h2 = d.congr(a_one, a, h_mo, &|d, t| d.add(ax, t));
                let s3 = d.add(a, ax);
                let h3 = d.lem("add_comm", &[ax, a]);
                let s4 = d.add(a_one, ax);
                let h_mo2 = d.lem("mul_one", &[a]);
                let h_mo2 = d.symm(a_one, a, h_mo2);
                let h4 = d.congr(a, a_one, h_mo2, &|d, t| d.add(t, ax));
                let h_xz = {
                    let aa_bb = d.mul(aa, bb);
                    let h_ma = d.lem("mul_assoc", &[a, a, bb]);
                    let u1 = d.symm(aa_bb, ax, h_ma);
                    let aab_b = d.mul(aab, b);
                    let h_ma2 = d.lem("mul_assoc", &[aa, b, b]);
                    let u2 = d.symm(aab_b, aa_bb, h_ma2);
                    let h_mc = d.lem("mul_comm", &[aab, b]);
                    let (_e, p) = d.chain(ax, &[(aa_bb, u1), (aab_b, u2), (z, h_mc)]);
                    p
                };
                let s5 = d.add(a_one, z);
                let h5 = d.congr(ax, z, h_xz, &|d, t| d.add(a_one, t));
                let (_e, proof) =
                    d.chain(start, &[(s1, h1), (s2, h2), (s3, h3), (s4, h4), (s5, h5)]);
                let stmt = d.eq(start, bad_rhs);
                (stmt, proof)
            })
            .expect_err("NC1: a false statement must be rejected");
        println!(
            "NC1 (false statement, correct proof) rejected:\n  {}",
            d.explain(&err)
        );
        assert!(matches!(err, KernelError::DeclarationValueMismatch { .. }));
        let rejected_name = d.name("nc1_wrong_statement");
        assert!(
            !d.k.environment().contains(rejected_name),
            "a rejected declaration must never reach the environment"
        );
        rejections += 1;
    }

    // NC2 — swap two arguments of a lemma inside an otherwise-correct chain:
    // `mul_assoc b a a` where `mul_assoc a a (b*b)` is required.
    {
        let mut d = Dev::new();
        definitions(&mut d);
        lemmas(&mut d);
        let err = d
            .try_theorem("nc2_swapped_lemma_arguments", 2, &|d, v| {
                let (a, b) = (v[0], v[1]);
                let bb = d.mul(b, b);
                let ax = d.mul(a, bb);
                let a_ax = d.mul(a, ax);
                let aa = d.mul(a, a);
                let aa_bb = d.mul(aa, bb);
                // WRONG: mul_assoc b a a : (b*a)*a = b*(a*a), not what is needed.
                let h_bad = d.lem("mul_assoc", &[b, a, a]);
                let proof = d.symm(aa_bb, a_ax, h_bad);
                let stmt = d.eq(a_ax, aa_bb);
                (stmt, proof)
            })
            .expect_err("NC2: swapped lemma arguments must be rejected");
        println!(
            "NC2 (swapped lemma arguments) rejected:\n  {}",
            d.explain(&err)
        );
        rejections += 1;
    }

    // NC3 — a broken induction: use the induction hypothesis itself as the
    // successor step for `zero_add`, which proves `P j`, not `P (succ j)`.
    {
        let mut d = Dev::new();
        definitions(&mut d);
        let err = d
            .try_theorem("nc3_broken_induction", 1, &|d, v| {
                let n = v[0];
                let p = |d: &mut Dev, x: ExprId| {
                    let z = d.zero();
                    let lhs = d.add(z, x);
                    d.eq(lhs, x)
                };
                let stmt = p(d, n);
                let proof = d.induct(
                    &p,
                    &|d| {
                        let z = d.zero();
                        d.refl(z)
                    },
                    &|_d, _j, ih| ih, // missing the `congr succ` transport
                    n,
                );
                (stmt, proof)
            })
            .expect_err("NC3: a broken induction step must be rejected");
        println!(
            "NC3 (induction step omitted) rejected:\n  {}",
            d.explain(&err)
        );
        rejections += 1;
    }

    // NC4 — a false theorem with a superficially plausible proof.
    {
        let mut d = Dev::new();
        definitions(&mut d);
        let err = d
            .try_theorem("nc4_mul_is_add", 2, &|d, v| {
                let (a, b) = (v[0], v[1]);
                let lhs = d.mul(a, b);
                let rhs = d.add(a, b);
                let stmt = d.eq(lhs, rhs);
                let proof = d.refl(lhs);
                (stmt, proof)
            })
            .expect_err("NC4: `mul = add` must be rejected");
        println!(
            "NC4 (false identity, refl proof) rejected:\n  {}",
            d.explain(&err)
        );
        rejections += 1;
    }

    // NC5 — the geometric closed form with the two sides of one summand
    // swapped, proved with the unmodified THEOREM B proof term.
    {
        let mut d = Dev::new();
        definitions(&mut d);
        lemmas(&mut d);
        theorem_geo_closed_form(&mut d);
        let err = d
            .try_theorem("nc5_transposed_conclusion", 2, &|d, v| {
                let (a, k) = (v[0], v[1]);
                let g = d.geo(a, k);
                let ag = d.mul(a, g);
                let one = d.num(1);
                let lhs = d.add(ag, one);
                let pw = d.pow(a, k);
                // transposed: `pow + geo` instead of `geo + pow`
                let rhs = d.add(pw, g);
                let stmt = d.eq(lhs, rhs);
                let proof = d.lem("geo_closed_form", &[a, k]);
                (stmt, proof)
            })
            .expect_err("NC5: a transposed conclusion must be rejected");
        println!(
            "NC5 (transposed conclusion) rejected:\n  {}",
            d.explain(&err)
        );
        rejections += 1;
    }

    assert_eq!(rejections, 5, "every negative control must be rejected");
}

/// EXPORT PROBE — can the checked development be emitted as a self-contained
/// real Lean module (the north-star claim: "a proof a Lean-grade kernel
/// accepts")? This renders `shell_closed_form` with its transitive dependencies
/// and `AxNat`/`Eq` emitted as real Lean `inductive`s.
///
/// It does **not** run Lean: no toolchain is installed on this machine
/// (`command -v lean` is empty), so this asserts only that the exporter
/// produces a plausible module. Running it through real Lean is the next
/// validation step.
#[test]
fn export_probe_renders_a_real_lean_module() {
    let mut d = full_development();
    let name = d.name("shell_closed_form");
    let (goal, proof) = match d.k.environment().get(name) {
        Some(Declaration::Theorem { ty, value, .. }) => (*ty, *value),
        _ => panic!("shell_closed_form must be a checked Theorem"),
    };
    let nat = d.logic.nat;
    let eq = d.logic.eq;
    let module = d.k.render_lean_module_compact_with_inductives(
        "shell_closed_form",
        goal,
        proof,
        &[nat, eq],
    );
    println!("lean module bytes: {}", module.len());
    for line in module.lines().take(12) {
        println!("| {line}");
    }
    assert!(module.contains("theorem shell_closed_form"));
    assert!(module.contains("inductive AxNat"));
    assert!(!module.contains("sorry"));
    assert!(
        !module.contains("axiom "),
        "the module must declare no axioms"
    );

    // Opt-in: drop the module somewhere a real Lean can be pointed at it.
    if let Ok(dir) = std::env::var("AXEYUM_LEAN_EXPORT_DIR") {
        let path = std::path::Path::new(&dir).join("shell_closed_form.lean");
        std::fs::write(&path, &module).expect("export directory must be writable");
        println!("wrote {}", path.display());
    }
}
