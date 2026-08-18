//! The **ordered-ring signature**: the 30 declarations LRA/SOS reconstruction
//! reasons over, named as a *parameter* rather than as the `Real` package.
//!
//! ## Why this type exists
//!
//! [`LraReconstructCtx`](super::LraReconstructCtx) used to hold an
//! [`ArithPrelude`] — the value only
//! [`build_arith_prelude`](axeyum_lean_kernel::build_arith_prelude) can produce
//! — and its constructor built that package into a fresh kernel and panicked if
//! the build failed. That welded the whole reconstruction route to the
//! axiomatized carrier `Real`, which is the entire remaining trusted surface of
//! this repository (`real: axiom=30`, and 30 of 30 of the recorded axiom ledger).
//!
//! Nothing in the reconstruction actually needs *that* carrier. Measured across
//! [`arithmetic`](super), [`ordered_ring`](super::ordered_ring) and
//! [`setoid`](super::ordered_ring::setoid): 158 field reads, touching all 30
//! declarations and the embedded [`LogicPrelude`], and every one of them is a
//! [`NameId`] handed to `Kernel::const_`. The route is already parametric; only
//! the *type* said otherwise.
//!
//! [`RingSignature`] is that type, decoupled from `build_arith_prelude`. It has
//! the same field names as [`ArithPrelude`] (so the 158 reads are unchanged) plus
//! [`RingSignature::equality`], which says *which relation plays the role of
//! equality* — `Eq` at the carrier for the `Real` package, and a defined
//! relation for a constructed carrier. `CReal`'s equality is `CReal.Equiv`, a
//! definition rather than the kernel's `Eq`, and that difference is exactly what
//! keeps its trusted surface at zero (ADR-0468 phase R3), so it has to be part of
//! the signature rather than an assumption baked into the code.
//!
//! ## What is checked
//!
//! A signature is a claim about a kernel environment, so
//! [`RingSignature::validate_in`] checks it against one rather than trusting the
//! caller. Five independent guards, each of which a wrong signature trips on its
//! own:
//!
//! 1. **presence** — all 30 declarations are in the environment;
//! 2. **carrier** — the carrier's type is a `Sort`, and its level is measured
//!    and reported (it is not assumed to be `Sort 1`);
//! 3. **symbols** — `add`/`mul : R → R → R`, `neg : R → R`, `zero`/`one : R`,
//!    `le`/`lt : R → R → Prop`, compared by `def_eq` against types built from the
//!    signature's own carrier;
//! 4. **laws are propositions** — each of the 22 laws has a type inhabiting
//!    `Prop`;
//! 5. **laws are in the ring language** — every `Const` occurring in a law's
//!    statement is one of the eight symbols, one of the propositional
//!    connectives, or the signature's declared equality. A law that mentions
//!    anything else is not a law *of this interface*, and a signature claiming
//!    a defined equality while its laws still mention the kernel's `Eq` is
//!    refused rather than silently generalized over the wrong relation.
//!
//! Guard 5 is what makes [`RingSignature::equality`] load-bearing rather than
//! decorative: flip it to [`RingEquality::Defined`] on the `Real` package and the
//! nine `Eq`-stated laws become stray constants.

use axeyum_lean_kernel::{
    ArithPrelude, BinderInfo, CRealPrelude, Declaration, ExprId, ExprNode, IntPrelude, Kernel,
    LogicPrelude, NameId,
};

use super::ReconstructError;

/// Which relation plays the role of equality in a [`RingSignature`]'s laws.
///
/// The nine `Eq`-shaped ordered-ring laws (`add_comm`, `add_assoc`, `add_zero`,
/// `add_neg`, `mul_comm`, `mul_assoc`, `mul_one`, `mul_zero`, `left_distrib`)
/// have to be stated with *some* equality. The axiomatized `Real` package uses
/// the kernel's `Eq` at the carrier; a constructed carrier generally cannot,
/// because its elements are equal as *values of a setoid* and not as terms —
/// `CReal.Equiv` is a definition over regular rational sequences, and stating
/// `add_comm` with `Eq CReal` would be false.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RingEquality {
    /// The kernel's `Eq`, applied at the carrier. What
    /// [`build_arith_prelude`](axeyum_lean_kernel::build_arith_prelude)
    /// produces, and the default.
    KernelEq,
    /// A declared relation `R → R → Prop`, e.g. `CReal.Equiv`.
    ///
    /// Under this choice the kernel's `Eq` is *not* an admissible constant in a
    /// law statement: a signature that claims a defined equality but whose laws
    /// still mention `Eq` has not actually moved off the kernel's equality, and
    /// [`RingSignature::validate_in`] says so.
    Defined(NameId),
}

/// The ordered-commutative-ring-with-`1` interface, as 30 names in some kernel
/// environment, plus the propositional prelude the laws are stated over and the
/// relation playing the role of equality.
///
/// Field names mirror [`ArithPrelude`] exactly; [`From<ArithPrelude>`] is the
/// `Real`-package instance and is what [`LraReconstructCtx::new`] uses, so the
/// default route is bit-for-bit what it was.
///
/// Handles belong to the kernel they were interned in; do not mix them across
/// kernels. [`RingSignature::validate_in`] is the check that they belong to the
/// kernel you are about to reconstruct in.
///
/// [`LraReconstructCtx::new`]: super::LraReconstructCtx::new
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RingSignature {
    /// The propositional prelude (`False`, `Not`, `Eq`, …) the laws and the
    /// reconstructed refutation are stated over.
    pub logic: LogicPrelude,
    /// Which relation the nine `Eq`-shaped laws are stated with.
    pub equality: RingEquality,

    // --- carrier + operations (8) --------------------------------------------
    /// The carrier, a constant whose type is a `Sort`.
    pub r: NameId,
    /// `add : R → R → R`.
    pub add: NameId,
    /// `mul : R → R → R`.
    pub mul: NameId,
    /// `neg : R → R`.
    pub neg: NameId,
    /// `zero : R`.
    pub zero: NameId,
    /// `one : R`.
    pub one: NameId,
    /// `le : R → R → Prop`.
    pub le: NameId,
    /// `lt : R → R → Prop`.
    pub lt: NameId,

    // --- the 22 laws ---------------------------------------------------------
    /// `le_refl : ∀ a, le a a`.
    pub le_refl: NameId,
    /// `le_trans : ∀ a b c, le a b → le b c → le a c`.
    pub le_trans: NameId,
    /// `lt_irrefl : ∀ a, Not (lt a a)`.
    pub lt_irrefl: NameId,
    /// `lt_trans : ∀ a b c, lt a b → lt b c → lt a c`.
    pub lt_trans: NameId,
    /// `lt_of_lt_of_le : ∀ a b c, lt a b → le b c → lt a c`.
    pub lt_of_lt_of_le: NameId,
    /// `lt_of_le_of_lt : ∀ a b c, le a b → lt b c → lt a c`.
    pub lt_of_le_of_lt: NameId,
    /// `le_of_lt : ∀ a b, lt a b → le a b`.
    pub le_of_lt: NameId,
    /// `add_le_add : ∀ a b c d, le a b → le c d → le (add a c) (add b d)`.
    pub add_le_add: NameId,
    /// `add_comm`, stated with [`Self::equality`].
    pub add_comm: NameId,
    /// `add_assoc`, stated with [`Self::equality`].
    pub add_assoc: NameId,
    /// `add_zero`, stated with [`Self::equality`].
    pub add_zero: NameId,
    /// `add_neg`, stated with [`Self::equality`].
    pub add_neg: NameId,
    /// `mul_le_mul_of_nonneg_left`.
    pub mul_le_mul_of_nonneg_left: NameId,
    /// `zero_lt_one : lt zero one`.
    pub zero_lt_one: NameId,
    /// `add_lt_add_of_le_of_lt`.
    pub add_lt_add_of_le_of_lt: NameId,
    /// `mul_comm`, stated with [`Self::equality`].
    pub mul_comm: NameId,
    /// `mul_assoc`, stated with [`Self::equality`].
    pub mul_assoc: NameId,
    /// `mul_one`, stated with [`Self::equality`].
    pub mul_one: NameId,
    /// `mul_zero`, stated with [`Self::equality`].
    pub mul_zero: NameId,
    /// `left_distrib`, stated with [`Self::equality`].
    pub left_distrib: NameId,
    /// `mul_nonneg : ∀ a b, le zero a → le zero b → le zero (mul a b)`.
    pub mul_nonneg: NameId,
    /// `sq_nonneg : ∀ a, le zero (mul a a)`.
    pub sq_nonneg: NameId,
}

impl From<ArithPrelude> for RingSignature {
    /// The `Real` package as a signature: the same 30 names, with equality the
    /// kernel's `Eq`.
    fn from(a: ArithPrelude) -> Self {
        Self {
            logic: a.logic,
            equality: RingEquality::KernelEq,
            r: a.r,
            add: a.add,
            mul: a.mul,
            neg: a.neg,
            zero: a.zero,
            one: a.one,
            le: a.le,
            lt: a.lt,
            le_refl: a.le_refl,
            le_trans: a.le_trans,
            lt_irrefl: a.lt_irrefl,
            lt_trans: a.lt_trans,
            lt_of_lt_of_le: a.lt_of_lt_of_le,
            lt_of_le_of_lt: a.lt_of_le_of_lt,
            le_of_lt: a.le_of_lt,
            add_le_add: a.add_le_add,
            add_comm: a.add_comm,
            add_assoc: a.add_assoc,
            add_zero: a.add_zero,
            add_neg: a.add_neg,
            mul_le_mul_of_nonneg_left: a.mul_le_mul_of_nonneg_left,
            zero_lt_one: a.zero_lt_one,
            add_lt_add_of_le_of_lt: a.add_lt_add_of_le_of_lt,
            mul_comm: a.mul_comm,
            mul_assoc: a.mul_assoc,
            mul_one: a.mul_one,
            mul_zero: a.mul_zero,
            left_distrib: a.left_distrib,
            mul_nonneg: a.mul_nonneg,
            sq_nonneg: a.sq_nonneg,
        }
    }
}

impl From<CRealPrelude> for RingSignature {
    /// The **constructed** reals as a signature: the same 30 field names, read
    /// off `CRealPrelude`, with equality the *defined* relation `CReal.Equiv`.
    ///
    /// This is the instance that costs nothing. `build_arith_prelude` admits its
    /// 30 declarations as **axioms**; `build_creal_prelude` proves all 22 laws
    /// from the constructed ℚ, so a refutation abstracted over this signature
    /// and instantiated back at `CReal` rests on no carrier assumption at all.
    ///
    /// `CRealPrelude` has no `logic` field of its own — the propositional
    /// prelude is three hops down its rational/integer tower, and it is the same
    /// `LogicPrelude` value either way.
    fn from(c: CRealPrelude) -> Self {
        Self {
            logic: c.rat.int.logic,
            // NOT `KernelEq`: `Eq CReal` is equality of *representatives*, not
            // of real numbers, and stating `add_comm` with it would be false.
            equality: RingEquality::Defined(c.equiv),
            r: c.creal,
            add: c.add,
            mul: c.mul,
            neg: c.neg,
            zero: c.zero,
            one: c.one,
            le: c.le,
            lt: c.lt,
            le_refl: c.le_refl,
            le_trans: c.le_trans,
            lt_irrefl: c.lt_irrefl,
            lt_trans: c.lt_trans,
            lt_of_lt_of_le: c.lt_of_lt_of_le,
            lt_of_le_of_lt: c.lt_of_le_of_lt,
            le_of_lt: c.le_of_lt,
            add_le_add: c.add_le_add,
            add_comm: c.add_comm,
            add_assoc: c.add_assoc,
            add_zero: c.add_zero,
            add_neg: c.add_neg,
            mul_le_mul_of_nonneg_left: c.mul_le_mul_of_nonneg_left,
            zero_lt_one: c.zero_lt_one,
            add_lt_add_of_le_of_lt: c.add_lt_add_of_le_of_lt,
            mul_comm: c.mul_comm,
            mul_assoc: c.mul_assoc,
            mul_one: c.mul_one,
            mul_zero: c.mul_zero,
            left_distrib: c.left_distrib,
            mul_nonneg: c.mul_nonneg,
            sq_nonneg: c.sq_nonneg,
        }
    }
}

impl From<IntPrelude> for RingSignature {
    /// The **constructed** integers as a signature: the same 30 field names,
    /// read off `IntPrelude`, with equality the kernel's own `Eq`.
    ///
    /// This is the third instance, and it fills the one slot the other two
    /// cannot both occupy. `build_arith_prelude` gives kernel equality at the
    /// cost of 30 **axioms**; `build_creal_prelude` costs nothing but its
    /// equality is the *defined* relation `CReal.Equiv`, because `Eq CReal` is
    /// equality of representatives (ADR-0468). `ℤ` is the case where both hold
    /// at once: `build_int_prelude` proves all 22 laws — `build_int_model_of_arith`
    /// admits each `Real` axiom's interpretation with `Int.<law>` as its proof and
    /// records `identical: true` for all 22, so the statements agree symbol for
    /// symbol after renaming — and its equality really is the kernel's `Eq`,
    /// since `Int` is a one-constructor inductive with no setoid over it.
    ///
    /// So a route that only needs *an* axiom-free ordered commutative ring with
    /// `Eq` — which is every consumer of the `Real` package that is not
    /// specifically about ℝ — can take this and reach no axiom at all. It is
    /// also cheap: the `Int` development is a small fraction of `CReal`'s
    /// construction cost.
    ///
    /// What it is **not** is a carrier for ℝ. `ℤ` is not ℝ (ADR-0456), and a
    /// theorem instantiated here is a theorem about the integers; the
    /// constructed reals are [`From<CRealPrelude>`].
    ///
    /// `IntPrelude` carries far more than the interface (division, `nat_abs`,
    /// the rational quotient, …); this reads exactly the 30 the signature names
    /// and nothing else.
    fn from(i: IntPrelude) -> Self {
        Self {
            logic: i.logic,
            equality: RingEquality::KernelEq,
            r: i.z,
            add: i.add,
            mul: i.mul,
            neg: i.neg,
            zero: i.zero,
            one: i.one,
            le: i.le,
            lt: i.lt,
            le_refl: i.le_refl,
            le_trans: i.le_trans,
            lt_irrefl: i.lt_irrefl,
            lt_trans: i.lt_trans,
            lt_of_lt_of_le: i.lt_of_lt_of_le,
            lt_of_le_of_lt: i.lt_of_le_of_lt,
            le_of_lt: i.le_of_lt,
            add_le_add: i.add_le_add,
            add_comm: i.add_comm,
            add_assoc: i.add_assoc,
            add_zero: i.add_zero,
            add_neg: i.add_neg,
            mul_le_mul_of_nonneg_left: i.mul_le_mul_of_nonneg_left,
            zero_lt_one: i.zero_lt_one,
            add_lt_add_of_le_of_lt: i.add_lt_add_of_le_of_lt,
            mul_comm: i.mul_comm,
            mul_assoc: i.mul_assoc,
            mul_one: i.mul_one,
            mul_zero: i.mul_zero,
            left_distrib: i.left_distrib,
            mul_nonneg: i.mul_nonneg,
            sq_nonneg: i.sq_nonneg,
        }
    }
}

/// How many of the 30 signature entries are the carrier and its operations.
pub const SIGNATURE_SYMBOLS: usize = 8;

/// How many of the 30 signature entries are laws.
pub const SIGNATURE_LAWS: usize = 22;

impl RingSignature {
    /// The carrier and the seven operations/relations, in declaration order.
    #[must_use]
    pub fn symbols(&self) -> [NameId; SIGNATURE_SYMBOLS] {
        [
            self.r, self.add, self.mul, self.neg, self.zero, self.one, self.le, self.lt,
        ]
    }

    /// The 22 laws, in declaration order — the order
    /// [`ArithPrelude::ordered_ring_laws`] and
    /// [`CRealPrelude::ordered_ring_laws`](axeyum_lean_kernel::CRealPrelude::ordered_ring_laws)
    /// share, so the three lists zip entry by entry.
    #[must_use]
    pub fn laws(&self) -> [NameId; SIGNATURE_LAWS] {
        [
            self.le_refl,
            self.le_trans,
            self.lt_irrefl,
            self.lt_trans,
            self.lt_of_lt_of_le,
            self.lt_of_le_of_lt,
            self.le_of_lt,
            self.add_le_add,
            self.add_comm,
            self.add_assoc,
            self.add_zero,
            self.add_neg,
            self.mul_le_mul_of_nonneg_left,
            self.zero_lt_one,
            self.add_lt_add_of_le_of_lt,
            self.mul_comm,
            self.mul_assoc,
            self.mul_one,
            self.mul_zero,
            self.left_distrib,
            self.mul_nonneg,
            self.sq_nonneg,
        ]
    }

    /// All 30 entries, symbols first — the abstraction telescope's ring prefix.
    #[must_use]
    pub fn declarations(&self) -> [NameId; SIGNATURE_SYMBOLS + SIGNATURE_LAWS] {
        let mut out = [self.r; SIGNATURE_SYMBOLS + SIGNATURE_LAWS];
        out[..SIGNATURE_SYMBOLS].copy_from_slice(&self.symbols());
        out[SIGNATURE_SYMBOLS..].copy_from_slice(&self.laws());
        out
    }

    /// Check this signature against `kernel`'s environment and report what was
    /// measured.
    ///
    /// Five guards, one function each, run in order; see this module's docs.
    /// Each has its own dedicated negative test, and deleting any one of them
    /// kills that test and no other (`signature_tests`).
    ///
    /// # Errors
    ///
    /// [`ReconstructError::KernelRejected`] naming the guard that failed and the
    /// declarations that failed it. The message is the finding; it is never a
    /// bare "invalid signature".
    pub fn validate_in(
        &self,
        kernel: &mut Kernel,
    ) -> Result<RingSignatureReport, ReconstructError> {
        self.guard_presence(kernel)?;
        let carrier_level = self.guard_carrier_is_a_type(kernel)?;
        self.guard_symbol_shapes(kernel)?;
        self.guard_laws_are_propositions(kernel)?;
        let equality_laws = self.guard_laws_speak_the_ring_language(kernel)?;
        Ok(RingSignatureReport {
            carrier_level,
            equality_laws,
        })
    }

    /// Guard 1: every one of the 30 entries is declared in this environment.
    ///
    /// Runs first because every later guard reads declared types by name.
    fn guard_presence(&self, kernel: &Kernel) -> Result<(), ReconstructError> {
        let missing: Vec<String> = self
            .declarations()
            .into_iter()
            .filter(|&n| kernel.environment().get(n).is_none())
            .map(|n| kernel.display_name(n).to_string())
            .collect();
        if !missing.is_empty() {
            return Err(defect(format!(
                "{} of {} signature declaration(s) are not in this kernel's environment: {}",
                missing.len(),
                SIGNATURE_SYMBOLS + SIGNATURE_LAWS,
                missing.join(", ")
            )));
        }
        Ok(())
    }

    /// Guard 2: the carrier is a type, and its universe is *measured* rather
    /// than assumed to be `1`.
    fn guard_carrier_is_a_type(&self, kernel: &mut Kernel) -> Result<usize, ReconstructError> {
        let carrier_decl = declared_ty(kernel, self.r);
        let carrier_whnf = kernel.whnf(carrier_decl);
        let ExprNode::Sort(level) = *kernel.expr_node(carrier_whnf) else {
            return Err(defect(format!(
                "the carrier `{}` is not a type: its declared type is not a `Sort`",
                kernel.display_name(self.r)
            )));
        };
        let zero_level = kernel.level_zero();
        let (base, succs) = kernel.level_succs(level);
        if base == zero_level {
            Ok(succs)
        } else {
            Err(defect(format!(
                "the carrier `{}` lives in a universe that is not a numeral, so the `Eq` \
                 universe argument this route builds cannot be computed from it",
                kernel.display_name(self.r)
            )))
        }
    }

    /// Guard 3: the seven operations and relations have the shapes the
    /// reconstruction applies them at, compared by `def_eq` against types built
    /// from this signature's own carrier.
    fn guard_symbol_shapes(&self, kernel: &mut Kernel) -> Result<(), ReconstructError> {
        let r_ty = kernel.const_(self.r, vec![]);
        let prop = {
            let z = kernel.level_zero();
            kernel.sort(z)
        };
        let unary = arrow(kernel, r_ty, r_ty);
        let binary = arrow(kernel, r_ty, unary);
        let relation = {
            let inner = arrow(kernel, r_ty, prop);
            arrow(kernel, r_ty, inner)
        };
        let expected: [(NameId, ExprId, &str); 7] = [
            (self.add, binary, "R -> R -> R"),
            (self.mul, binary, "R -> R -> R"),
            (self.neg, unary, "R -> R"),
            (self.zero, r_ty, "R"),
            (self.one, r_ty, "R"),
            (self.le, relation, "R -> R -> Prop"),
            (self.lt, relation, "R -> R -> Prop"),
        ];
        for (name, want, rendered) in expected {
            let have = declared_ty(kernel, name);
            if !kernel.def_eq(have, want) {
                return Err(defect(format!(
                    "the signature symbol `{}` does not have the shape `{rendered}` over the \
                     carrier `{}`",
                    kernel.display_name(name),
                    kernel.display_name(self.r)
                )));
            }
        }
        Ok(())
    }

    /// Guard 4: every law states a proposition.
    fn guard_laws_are_propositions(&self, kernel: &mut Kernel) -> Result<(), ReconstructError> {
        let mut not_prop: Vec<String> = Vec::new();
        for law in self.laws() {
            let ty = declared_ty(kernel, law);
            let inhabits = kernel.infer(ty).map_err(|e| {
                defect(format!(
                    "the law `{}` has a statement the kernel cannot type: {e:?}",
                    kernel.display_name(law)
                ))
            })?;
            let whnf = kernel.whnf(inhabits);
            let is_prop = match *kernel.expr_node(whnf) {
                ExprNode::Sort(l) => {
                    let z = kernel.level_zero();
                    l == z
                }
                _ => false,
            };
            if !is_prop {
                not_prop.push(kernel.display_name(law).to_string());
            }
        }
        if !not_prop.is_empty() {
            return Err(defect(format!(
                "{} signature law(s) do not state a proposition: {}",
                not_prop.len(),
                not_prop.join(", ")
            )));
        }
        Ok(())
    }

    /// Guard 5: every constant in a law statement is one of the eight symbols, a
    /// propositional connective, or this signature's declared equality.
    ///
    /// Returns the laws that mention the equality — nine, for the `Real`
    /// package.
    fn guard_laws_speak_the_ring_language(
        &self,
        kernel: &Kernel,
    ) -> Result<Vec<String>, ReconstructError> {
        let mut allowed: std::collections::BTreeSet<NameId> = self.symbols().into_iter().collect();
        allowed.extend([
            self.logic.not,
            self.logic.false_,
            self.logic.true_,
            self.logic.and,
            self.logic.or,
            self.logic.iff,
            self.logic.exists_,
        ]);
        let equality_name = match self.equality {
            RingEquality::KernelEq => self.logic.eq,
            RingEquality::Defined(rel) => rel,
        };
        allowed.insert(equality_name);

        let mut equality_laws: Vec<String> = Vec::new();
        let mut foreign: Vec<String> = Vec::new();
        for law in self.laws() {
            let ty = declared_ty(kernel, law);
            let mentioned = constants_in(kernel, ty);
            if mentioned.contains(&equality_name) {
                equality_laws.push(kernel.display_name(law).to_string());
            }
            for name in mentioned {
                if !allowed.contains(&name) {
                    foreign.push(format!(
                        "{} (in `{}`)",
                        kernel.display_name(name),
                        kernel.display_name(law)
                    ));
                }
            }
        }
        if !foreign.is_empty() {
            foreign.sort_unstable();
            foreign.dedup();
            return Err(defect(format!(
                "{} constant(s) outside the ordered-ring language occur in the signature's law \
                 statements, so the laws are not statements about this interface alone: {}",
                foreign.len(),
                foreign.join(", ")
            )));
        }
        Ok(equality_laws)
    }
}

/// What [`RingSignature::validate_in`] measured. Every field is read out of the
/// kernel, not asserted by the caller.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RingSignatureReport {
    /// The carrier's universe: `n` for `Sort n`. `1` for the `Real` package's
    /// `Real : Type`.
    ///
    /// Reported rather than assumed because the reconstruction builds `Eq` and
    /// `Eq.rec` at a *fixed* universe 1; a carrier at any other level is a
    /// finding, not a configuration.
    pub carrier_level: usize,
    /// The laws whose statement mentions [`RingSignature::equality`], rendered
    /// and in declaration order. Nine for the `Real` package — the nine ADR-0468
    /// Measurement 2 counted, and the nine
    /// [`enable_setoid_equality`](super::LraReconstructCtx::enable_setoid_equality)
    /// restates through the equality slot.
    pub equality_laws: Vec<String>,
}

fn defect(detail: String) -> ReconstructError {
    ReconstructError::KernelRejected {
        rule: "ring_signature".to_owned(),
        detail,
    }
}

/// The declared type of a name that guard (1) has already shown to be present.
fn declared_ty(kernel: &Kernel, name: NameId) -> ExprId {
    kernel
        .environment()
        .get(name)
        .map(Declaration::ty)
        .expect("presence is checked before any other guard runs")
}

fn arrow(kernel: &mut Kernel, dom: ExprId, cod: ExprId) -> ExprId {
    let anon = kernel.anon();
    kernel.pi(anon, dom, cod, BinderInfo::Default)
}

/// Every `Const` name occurring anywhere in `expr`.
fn constants_in(kernel: &Kernel, expr: ExprId) -> std::collections::BTreeSet<NameId> {
    let mut found = std::collections::BTreeSet::new();
    let mut seen: std::collections::BTreeSet<ExprId> = std::collections::BTreeSet::new();
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if !seen.insert(node) {
            continue;
        }
        match *kernel.expr_node(node) {
            ExprNode::Const(name, _) => {
                found.insert(name);
            }
            ExprNode::App(a, b) => {
                stack.push(a);
                stack.push(b);
            }
            ExprNode::Proj(_, _, inner) => stack.push(inner),
            ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprNode::Let(_, ty, value, body) => {
                stack.push(ty);
                stack.push(value);
                stack.push(body);
            }
            ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => {}
        }
    }
    found
}

#[cfg(test)]
mod signature_tests;
