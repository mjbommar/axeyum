//! **The `by axeyum` bridge** — decode a Lean goal, prove it, print a Lean term.
//!
//! This is the Rust half of `lean/axeyum-tactic` (ADR-1666). It is the second
//! adapter in this crate and it is deliberately shaped like the first: C3's
//! [`crate::thin_adapter`] carries a *protocol* and a *grading* step and adds
//! no new translation logic, because C2 had already built and checked one.
//! Here there is genuinely new translation logic, so the rule that keeps it
//! honest is different and stated once:
//!
//! > **Nothing in this file is trusted.** A wrong translation, a wrong name
//! > mapping, a wrong printer — each one produces a term Lean's own elaborator
//! > and kernel then refuse, and `by axeyum` fails. The only thing that closes
//! > a Lean goal is a term Lean checked.
//!
//! # Three steps
//!
//! 1. [`LeanExpr`] decodes the already-elaborated goal the tactic serialized.
//!    No Lean *source* crosses the boundary, so this is not a Lean parser and
//!    does not become one — the missing native parser is a separate, larger
//!    piece of work (`docs/math-department/14-lean-lang.md` item 9).
//! 2. [`Translator`] turns that into a term over this kernel's `NatPrelude`,
//!    or declines. Every recognized head is listed in one table and every
//!    unrecognized one declines `unsupported`; the type arguments of Lean's
//!    heterogeneous operators (`HAdd.hAdd`, `LE.le`, `OfNat.ofNat`) are
//!    *checked* to be `Nat` rather than assumed.
//! 3. [`print_lean`] walks the emitted kernel term and prints Lean source,
//!    mapping every constant through [`NAME_MAP`]. A constant that is not in
//!    the map declines `unsupported` — that is the correspondence gate, and
//!    the reason it is a gate rather than a best effort is that a missing
//!    entry would otherwise print a name Lean does not have and surface as a
//!    parse error at the far end, where it says nothing about which lemma was
//!    missing.
//!
//! # The name map, and why a rename is not enough
//!
//! Measured with `examples/axeyum_tactic_probe.rs` (2026-09-05): the `ring`
//! and `linarith` ℕ producers reference twenty kernel constants across an
//! eleven-goal battery. Eight are structural (`AxNat`, `Eq`, `Eq.rec`, …) and
//! map to Lean core by name. Twelve are lemmas, and *the emitted term applies
//! every one of them with all arguments explicit, in axeyum's argument order*
//! — where Lean core takes most of them implicitly and, in five cases, in a
//! different order. So the lemmas map to `Axeyum.Shim.*`: one Lean theorem
//! each, stated with axeyum's exact signature and **proved from Lean core**
//! in `lean/axeyum-tactic/Axeyum/Shim.lean`. The shim adds no axiom, and
//! Lean checks it before any tactic runs.

use std::collections::BTreeMap;

use axeyum_lean_kernel::{
    ExprId, ExprNode, Kernel, LevelNode, NatOps, NatPrelude, NatState, build_nat_prelude, linarith,
    ring,
};
use serde_json::Value;

/// Why the bridge produced no Lean term.
///
/// The three variants map exactly onto the sidecar's three decline reasons,
/// which are exactly `axeyum_lean_import::thin_adapter::KNOWN_DECLINE_REASONS`
/// and `Axeyum.Protocol.knownDeclineReasons`. There is deliberately no fourth:
/// a bridge that could invent a category the Lean side does not know would
/// make the Lean side's `malformed-response` path unreachable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decline {
    /// The goal, or a constant in the emitted term, is outside the fragment
    /// this bridge covers. Carries a human-readable detail for the log.
    Unsupported(String),
    /// The fragment covers the goal and the producers found no term. Never a
    /// claim that the goal is false.
    Unknown(String),
}

impl Decline {
    /// The wire reason string.
    #[must_use]
    pub const fn reason(&self) -> &'static str {
        match self {
            Self::Unsupported(_) => "unsupported",
            Self::Unknown(_) => "unknown",
        }
    }

    /// The human-readable detail.
    #[must_use]
    pub fn detail(&self) -> &str {
        match self {
            Self::Unsupported(d) | Self::Unknown(d) => d,
        }
    }
}

// ---------------------------------------------------------------------------
// 1. The wire form of an already-elaborated Lean `Expr`
// ---------------------------------------------------------------------------

/// The subset of Lean's `Expr` the tactic serializes. Everything else is
/// refused on the Lean side before a request is sent (`Axeyum.encodeExpr`),
/// so a node kind reaching here that is not one of these is a protocol
/// violation, not a mathematical limitation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeanExpr {
    /// A de Bruijn index. Present only inside binders, which this fragment
    /// does not accept; kept so the decoder is total over the encoder.
    BVar(u32),
    /// A local hypothesis or variable, by its user-facing Lean name.
    FVar(String),
    /// A constant, by its full Lean name. Universe arguments are deliberately
    /// not carried: the fragment is ℕ, where every relevant constant is either
    /// universe-monomorphic or applied at levels the *printer* re-derives.
    Const(String),
    /// Application.
    App(Box<LeanExpr>, Box<LeanExpr>),
    /// A raw `Nat` literal.
    Nat(u64),
}

/// Decode one node.
///
/// # Errors
///
/// A description of the first malformed node. The sidecar turns this into a
/// `malformed-response`-shaped decline (`unsupported`), never a panic.
pub fn decode(value: &Value) -> Result<LeanExpr, String> {
    let object = value
        .as_object()
        .ok_or("expression node is not an object")?;
    let kind = object
        .get("k")
        .and_then(Value::as_str)
        .ok_or("expression node has no string \"k\"")?;
    match kind {
        "bvar" => {
            let idx = object
                .get("idx")
                .and_then(Value::as_u64)
                .ok_or("bvar without \"idx\"")?;
            Ok(LeanExpr::BVar(
                u32::try_from(idx).map_err(|_| "bvar index out of range".to_owned())?,
            ))
        }
        "fvar" => Ok(LeanExpr::FVar(
            object
                .get("name")
                .and_then(Value::as_str)
                .ok_or("fvar without \"name\"")?
                .to_owned(),
        )),
        "const" => Ok(LeanExpr::Const(
            object
                .get("name")
                .and_then(Value::as_str)
                .ok_or("const without \"name\"")?
                .to_owned(),
        )),
        "app" => {
            let f = object.get("fn").ok_or("app without \"fn\"")?;
            let a = object.get("arg").ok_or("app without \"arg\"")?;
            Ok(LeanExpr::App(Box::new(decode(f)?), Box::new(decode(a)?)))
        }
        "nat" => Ok(LeanExpr::Nat(
            object
                .get("value")
                .and_then(Value::as_u64)
                .ok_or("nat without \"value\"")?,
        )),
        other => Err(format!("unrecognized expression node kind {other:?}")),
    }
}

impl LeanExpr {
    /// The head and its arguments, left to right.
    #[must_use]
    pub fn spine(&self) -> (&Self, Vec<&Self>) {
        let mut args = Vec::new();
        let mut head = self;
        while let Self::App(f, a) = head {
            args.push(a.as_ref());
            head = f.as_ref();
        }
        args.reverse();
        (head, args)
    }

    /// Whether this node is exactly the constant `name`.
    #[must_use]
    pub fn is_const(&self, name: &str) -> bool {
        matches!(self, Self::Const(n) if n == name)
    }
}

// ---------------------------------------------------------------------------
// 2. Translation into this kernel's ℕ
// ---------------------------------------------------------------------------

/// The kernel-side development the bridge proves in.
pub struct Dev {
    kernel: Kernel,
    state: NatState,
    prelude: NatPrelude,
}

impl NatOps for Dev {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.kernel
    }
    fn nat_state(&mut self) -> &mut NatState {
        &mut self.state
    }
}

impl Dev {
    /// Build the ℕ prelude and the development over it.
    ///
    /// # Errors
    ///
    /// The kernel's own error if the prelude does not build, which would mean
    /// this crate is broken rather than that the request was.
    pub fn new() -> Result<Self, axeyum_lean_kernel::KernelError> {
        let mut kernel = Kernel::new();
        let prelude = build_nat_prelude(&mut kernel)?;
        let state = NatState::new(&mut kernel, prelude);
        Ok(Self {
            kernel,
            state,
            prelude,
        })
    }

    /// The prelude handle, for the producers.
    #[must_use]
    pub const fn prelude(&self) -> NatPrelude {
        self.prelude
    }

    /// The kernel, for printing.
    #[must_use]
    pub const fn kernel_ref(&self) -> &Kernel {
        &self.kernel
    }
}

/// Lean's ℕ addition instance chain, as names. A `HAdd.hAdd` whose instance
/// argument mentions anything outside this set is not ℕ's `+` and is refused
/// rather than translated — the instance is what decides *which* operation the
/// notation denotes.
const NAT_ADD_INSTANCE_NAMES: &[&str] = &["instHAdd", "instAddNat", "Nat", "Add.mk", "instAdd"];
/// Lean's ℕ multiplication instance chain. Same rule.
const NAT_MUL_INSTANCE_NAMES: &[&str] = &["instHMul", "instMulNat", "Nat", "Mul.mk", "instMul"];
/// Lean's ℕ `≤` instance chain. Same rule.
const NAT_LE_INSTANCE_NAMES: &[&str] = &["instLENat", "Nat", "LE.mk"];
/// Lean's ℕ `<` instance chain. Same rule.
const NAT_LT_INSTANCE_NAMES: &[&str] = &["instLTNat", "Nat", "LT.mk"];

/// Whether every constant in `e` is in `allowed` and `e` mentions no local.
fn instance_is(e: &LeanExpr, allowed: &[&str]) -> bool {
    match e {
        LeanExpr::Const(n) => allowed.contains(&n.as_str()),
        LeanExpr::App(f, a) => instance_is(f, allowed) && instance_is(a, allowed),
        LeanExpr::Nat(_) => true,
        LeanExpr::BVar(_) | LeanExpr::FVar(_) => false,
    }
}

/// Translates a decoded Lean goal into this kernel's ℕ.
pub struct Translator {
    /// Lean local name -> (kernel free-variable id, its `ExprId`), in
    /// first-seen order. The raw id is kept because closing the emitted term
    /// for this kernel's own re-check needs `NatOps::lam_fv`, which abstracts
    /// by id and not by expression.
    fvars: BTreeMap<String, (u64, ExprId)>,
}

impl Default for Translator {
    fn default() -> Self {
        Self::new()
    }
}

impl Translator {
    /// A fresh translator with no locals bound.
    #[must_use]
    pub fn new() -> Self {
        Self {
            fvars: BTreeMap::new(),
        }
    }

    /// The Lean local names bound so far, and their kernel free variables.
    #[must_use]
    pub const fn fvars(&self) -> &BTreeMap<String, (u64, ExprId)> {
        &self.fvars
    }

    /// The kernel free variable for a Lean local, allocating on first use.
    fn local(&mut self, dev: &mut Dev, name: &str) -> ExprId {
        if let Some(&(_, id)) = self.fvars.get(name) {
            return id;
        }
        let fv = dev.fresh_fvar();
        let id = dev.kernel.fvar(fv);
        self.fvars.insert(name.to_owned(), (fv, id));
        id
    }

    /// Translate a ℕ-valued Lean term.
    ///
    /// # Errors
    ///
    /// [`Decline::Unsupported`] naming the first head outside the fragment.
    pub fn term(&mut self, dev: &mut Dev, e: &LeanExpr) -> Result<ExprId, Decline> {
        let (head, args) = e.spine();
        match head {
            LeanExpr::FVar(name) if args.is_empty() => Ok(self.local(dev, name)),
            LeanExpr::Nat(n) if args.is_empty() => Self::numeral(dev, *n),
            LeanExpr::Const(name) => self.const_term(dev, name, &args),
            LeanExpr::BVar(_) => Err(Decline::Unsupported(
                "a de Bruijn variable reached the translator; the goal has a binder".to_owned(),
            )),
            LeanExpr::App(..) => unreachable!("spine() never returns an application as the head"),
            LeanExpr::FVar(name) => Err(Decline::Unsupported(format!(
                "the local `{name}` is applied to {} argument(s); ℕ locals are not functions",
                args.len()
            ))),
            LeanExpr::Nat(n) => Err(Decline::Unsupported(format!(
                "the literal {n} is applied to {} argument(s)",
                args.len()
            ))),
        }
    }

    /// A ℕ numeral, spelled as `succ`s over `zero` because every numeral in
    /// this kernel is unary. Bounded because a large numeral is a large term:
    /// the producers' own coefficient bound is 4 and the goals this fragment
    /// serves are small.
    fn numeral(dev: &mut Dev, n: u64) -> Result<ExprId, Decline> {
        const MAX_NUMERAL: u64 = 64;
        if n > MAX_NUMERAL {
            return Err(Decline::Unsupported(format!(
                "the numeral {n} exceeds the bridge's bound of {MAX_NUMERAL}; \
                 every numeral in this kernel is unary, so the term would be {n} `succ`s"
            )));
        }
        let value = u32::try_from(n)
            .map_err(|_| Decline::Unsupported(format!("the numeral {n} does not fit in a u32")))?;
        Ok(dev.num(value))
    }

    /// A constant-headed ℕ term. **This match is the fragment.**
    fn const_term(
        &mut self,
        dev: &mut Dev,
        name: &str,
        args: &[&LeanExpr],
    ) -> Result<ExprId, Decline> {
        match (name, args.len()) {
            // `a + b` at ℕ: `@HAdd.hAdd Nat Nat Nat inst a b`.
            ("HAdd.hAdd", 6) => {
                Self::require_nat_triple(args, "HAdd.hAdd")?;
                if !instance_is(args[3], NAT_ADD_INSTANCE_NAMES) {
                    return Err(Decline::Unsupported(
                        "`+` is used at ℕ with an instance that is not ℕ's own `instAddNat`"
                            .to_owned(),
                    ));
                }
                let l = self.term(dev, args[4])?;
                let r = self.term(dev, args[5])?;
                Ok(dev.add(l, r))
            }
            ("Nat.add", 2) => {
                let l = self.term(dev, args[0])?;
                let r = self.term(dev, args[1])?;
                Ok(dev.add(l, r))
            }
            // `a * b` at ℕ.
            ("HMul.hMul", 6) => {
                Self::require_nat_triple(args, "HMul.hMul")?;
                if !instance_is(args[3], NAT_MUL_INSTANCE_NAMES) {
                    return Err(Decline::Unsupported(
                        "`*` is used at ℕ with an instance that is not ℕ's own `instMulNat`"
                            .to_owned(),
                    ));
                }
                let l = self.term(dev, args[4])?;
                let r = self.term(dev, args[5])?;
                Ok(dev.mul(l, r))
            }
            ("Nat.mul", 2) => {
                let l = self.term(dev, args[0])?;
                let r = self.term(dev, args[1])?;
                Ok(dev.mul(l, r))
            }
            ("Nat.succ", 1) => {
                let inner = self.term(dev, args[0])?;
                Ok(dev.succ(inner))
            }
            ("Nat.zero", 0) => Ok(dev.zero()),
            // A numeral: `@OfNat.ofNat Nat n inst`.
            ("OfNat.ofNat", 3) => {
                if !args[0].is_const("Nat") {
                    return Err(Decline::Unsupported(
                        "a numeral literal is not at type ℕ".to_owned(),
                    ));
                }
                match args[1] {
                    LeanExpr::Nat(n) => Self::numeral(dev, *n),
                    _ => Err(Decline::Unsupported(
                        "a numeral literal's value is not a raw `Nat` literal".to_owned(),
                    )),
                }
            }
            (other, arity) => Err(Decline::Unsupported(format!(
                "`{other}` applied to {arity} argument(s) is not in the ℕ term fragment"
            ))),
        }
    }

    /// The first three arguments of a heterogeneous operator must all be `Nat`.
    fn require_nat_triple(args: &[&LeanExpr], what: &str) -> Result<(), Decline> {
        if args[0].is_const("Nat") && args[1].is_const("Nat") && args[2].is_const("Nat") {
            Ok(())
        } else {
            Err(Decline::Unsupported(format!(
                "`{what}` is not used at ℕ × ℕ → ℕ"
            )))
        }
    }

    /// Translate a Lean proposition into this kernel's ℕ.
    ///
    /// # Errors
    ///
    /// [`Decline::Unsupported`] naming the head that is not a ℕ relation.
    pub fn prop(&mut self, dev: &mut Dev, e: &LeanExpr) -> Result<ExprId, Decline> {
        let (head, args) = e.spine();
        let LeanExpr::Const(name) = head else {
            return Err(Decline::Unsupported(
                "the proposition's head is not a constant".to_owned(),
            ));
        };
        match (name.as_str(), args.len()) {
            ("Eq", 3) => {
                if !args[0].is_const("Nat") {
                    return Err(Decline::Unsupported(
                        "the equation is not at type ℕ".to_owned(),
                    ));
                }
                let l = self.term(dev, args[1])?;
                let r = self.term(dev, args[2])?;
                Ok(dev.eq(l, r))
            }
            ("LE.le", 4) => {
                if !args[0].is_const("Nat") {
                    return Err(Decline::Unsupported("`≤` is not at type ℕ".to_owned()));
                }
                if !instance_is(args[1], NAT_LE_INSTANCE_NAMES) {
                    return Err(Decline::Unsupported(
                        "`≤` is used at ℕ with an instance that is not ℕ's own `instLENat`"
                            .to_owned(),
                    ));
                }
                let l = self.term(dev, args[2])?;
                let r = self.term(dev, args[3])?;
                Ok(dev.le(l, r))
            }
            ("Nat.le", 2) => {
                let l = self.term(dev, args[0])?;
                let r = self.term(dev, args[1])?;
                Ok(dev.le(l, r))
            }
            ("LT.lt", 4) => {
                if !args[0].is_const("Nat") {
                    return Err(Decline::Unsupported("`<` is not at type ℕ".to_owned()));
                }
                if !instance_is(args[1], NAT_LT_INSTANCE_NAMES) {
                    return Err(Decline::Unsupported(
                        "`<` is used at ℕ with an instance that is not ℕ's own `instLTNat`"
                            .to_owned(),
                    ));
                }
                let l = self.term(dev, args[2])?;
                let r = self.term(dev, args[3])?;
                Ok(dev.lt(l, r))
            }
            ("Nat.lt", 2) => {
                let l = self.term(dev, args[0])?;
                let r = self.term(dev, args[1])?;
                Ok(dev.lt(l, r))
            }
            (other, arity) => Err(Decline::Unsupported(format!(
                "`{other}` applied to {arity} argument(s) is not a ℕ relation this bridge reads"
            ))),
        }
    }
}

// ---------------------------------------------------------------------------
// 3. Printing a kernel term as Lean source
// ---------------------------------------------------------------------------

/// The name-correspondence table: this kernel's spelling -> the Lean constant
/// the printer emits, and how many universe arguments that Lean constant takes.
///
/// Every row is checked by Lean, twice over. `Axeyum.Shim.*` rows are theorems
/// Lean proved from core in `lean/axeyum-tactic/Axeyum/Shim.lean`; core rows
/// are checked every time a term mentioning them elaborates. A constant the
/// producers emit that is *not* here declines `unsupported`, which is why this
/// table is a gate and not documentation.
///
/// Populated from `examples/axeyum_tactic_probe.rs`'s measured inventory.
pub const NAME_MAP: &[(&str, &str, usize)] = &[
    // Structural: Lean core has these under the same spelling.
    ("AxNat", "Nat", 0),
    ("AxNat.zero", "Nat.zero", 0),
    ("AxNat.succ", "Nat.succ", 0),
    ("AxNat.add", "Nat.add", 0),
    ("AxNat.mul", "Nat.mul", 0),
    ("AxNat.le", "Nat.le", 0),
    ("Eq", "Eq", 1),
    ("Eq.refl", "Eq.refl", 1),
    ("Eq.rec", "Eq.rec", 2),
    // Lemmas: axeyum's argument order and explicitness, proved from core.
    ("AxNat.le.refl", "Axeyum.Shim.natLeRefl", 0),
    ("AxNat.le_trans", "Axeyum.Shim.natLeTrans", 0),
    ("AxNat.le_add_right", "Axeyum.Shim.natLeAddRight", 0),
    ("AxNat.add_le_add_left", "Axeyum.Shim.natAddLeAddLeft", 0),
    ("AxNat.add_le_add_right", "Axeyum.Shim.natAddLeAddRight", 0),
    (
        "AxNat.le_of_add_le_add_right",
        "Axeyum.Shim.natLeOfAddLeAddRight",
        0,
    ),
    ("AxNat.add_comm", "Axeyum.Shim.natAddComm", 0),
    ("AxNat.add_assoc", "Axeyum.Shim.natAddAssoc", 0),
    ("AxNat.add_right_comm", "Axeyum.Shim.natAddRightComm", 0),
    ("AxNat.mul_comm", "Axeyum.Shim.natMulComm", 0),
    ("AxNat.mul_assoc", "Axeyum.Shim.natMulAssoc", 0),
    ("AxNat.left_distrib", "Axeyum.Shim.natLeftDistrib", 0),
    ("AxNat.right_distrib", "Axeyum.Shim.natRightDistrib", 0),
];

/// The Lean constant for a kernel name, and its universe arity.
fn mapped(name: &str) -> Option<(&'static str, usize)> {
    NAME_MAP
        .iter()
        .find(|(ours, _, _)| *ours == name)
        .map(|(_, theirs, arity)| (*theirs, *arity))
}

/// Print a level as a Lean universe argument. Only numeric levels are
/// supported; a parameter or a `max` declines, because this fragment's terms
/// only ever carry `Sort 0` and `Sort 1`.
fn print_level(kernel: &Kernel, mut level: axeyum_lean_kernel::LevelId) -> Result<String, Decline> {
    let mut n = 0_u32;
    loop {
        match kernel.level_node(level) {
            LevelNode::Zero => return Ok(n.to_string()),
            LevelNode::Succ(inner) => {
                n += 1;
                level = *inner;
            }
            LevelNode::Max(..) | LevelNode::IMax(..) | LevelNode::Param(_) => {
                return Err(Decline::Unsupported(
                    "the emitted term carries a non-numeric universe level".to_owned(),
                ));
            }
        }
    }
}

/// Print a kernel term as Lean 4 source, in the local context named by
/// `fvar_names` (kernel free variable -> the Lean local it stands for).
///
/// Every constant is emitted `@`-applied, because this kernel's terms are
/// fully explicit and Lean's counterparts are not.
///
/// # Errors
///
/// [`Decline::Unsupported`] on a constant outside [`NAME_MAP`], a non-numeric
/// universe, a structure projection, or a `let`.
pub fn print_lean(
    kernel: &Kernel,
    expr: ExprId,
    fvar_names: &BTreeMap<ExprId, String>,
) -> Result<String, Decline> {
    let mut binders: Vec<String> = Vec::new();
    print_node(kernel, expr, fvar_names, &mut binders)
}

fn print_node(
    kernel: &Kernel,
    expr: ExprId,
    fvar_names: &BTreeMap<ExprId, String>,
    binders: &mut Vec<String>,
) -> Result<String, Decline> {
    match kernel.expr_node(expr) {
        ExprNode::BVar(index) => {
            let depth = binders.len();
            let position = depth
                .checked_sub(*index as usize + 1)
                .ok_or_else(|| Decline::Unsupported("unbound de Bruijn index".to_owned()))?;
            Ok(binders[position].clone())
        }
        ExprNode::FVar(_) => fvar_names.get(&expr).cloned().ok_or_else(|| {
            Decline::Unsupported(
                "the emitted term mentions a free variable with no Lean name".to_owned(),
            )
        }),
        ExprNode::Sort(level) => Ok(format!("Sort {}", print_level(kernel, *level)?)),
        ExprNode::Const(name, levels) => {
            let spelled = kernel.lean_name(*name);
            let (lean, universe_arity) = mapped(&spelled).ok_or_else(|| {
                Decline::Unsupported(format!(
                    "the emitted term references `{spelled}`, which has no entry in the \
                     name-correspondence table; add a proved row to Axeyum.Shim first"
                ))
            })?;
            if universe_arity == 0 {
                Ok(format!("@{lean}"))
            } else {
                if levels.len() != universe_arity {
                    return Err(Decline::Unsupported(format!(
                        "`{spelled}` was emitted with {} universe argument(s); \
                         `{lean}` takes {universe_arity}",
                        levels.len()
                    )));
                }
                let mut parts = Vec::with_capacity(levels.len());
                for &level in levels {
                    parts.push(print_level(kernel, level)?);
                }
                Ok(format!("@{lean}.{{{}}}", parts.join(", ")))
            }
        }
        ExprNode::App(..) => {
            // FLAT, not binary. `@f` makes the implicit arguments of the
            // application it heads explicit -- it does not turn `f` into an
            // all-explicit function. So `((@Eq.rec Nat) x)` re-inserts
            // `Eq.rec`'s implicits around the parenthesized partial
            // application and every later argument lands one slot late. That
            // is a real defect this printer had, found by Lean on the first
            // run of `Tests/NatLinear.lean` (2026-09-05): the emitted motive
            // arrived where the `refl` case was expected. One spine, one
            // application node.
            let mut args = Vec::new();
            let mut head = expr;
            while let ExprNode::App(f, a) = kernel.expr_node(head) {
                args.push(*a);
                head = *f;
            }
            args.reverse();
            let mut rendered = String::from("(");
            rendered.push_str(&print_node(kernel, head, fvar_names, binders)?);
            for arg in args {
                rendered.push(' ');
                rendered.push_str(&print_node(kernel, arg, fvar_names, binders)?);
            }
            rendered.push(')');
            Ok(rendered)
        }
        ExprNode::Lam(_, ty, body, _) => {
            let domain = print_node(kernel, *ty, fvar_names, binders)?;
            let name = format!("axb{}", binders.len());
            binders.push(name.clone());
            let inner = print_node(kernel, *body, fvar_names, binders);
            binders.pop();
            Ok(format!("(fun ({name} : {domain}) => {})", inner?))
        }
        ExprNode::Pi(_, ty, body, _) => {
            let domain = print_node(kernel, *ty, fvar_names, binders)?;
            let name = format!("axb{}", binders.len());
            binders.push(name.clone());
            let inner = print_node(kernel, *body, fvar_names, binders);
            binders.pop();
            Ok(format!("(({name} : {domain}) -> {})", inner?))
        }
        ExprNode::Lit(_) => Err(Decline::Unsupported(
            "the emitted term carries a literal; this kernel's ℕ is unary and should not"
                .to_owned(),
        )),
        ExprNode::Let(..) => Err(Decline::Unsupported(
            "the emitted term carries a `let`".to_owned(),
        )),
        ExprNode::Proj(..) => Err(Decline::Unsupported(
            "the emitted term carries a structure projection".to_owned(),
        )),
    }
}

// ---------------------------------------------------------------------------
// The whole route
// ---------------------------------------------------------------------------

/// One hypothesis from the Lean local context.
#[derive(Debug, Clone)]
pub struct Hypothesis {
    /// The Lean local's user-facing name; the emitted term refers to it.
    pub name: String,
    /// Its type, as the tactic serialized it.
    pub ty: LeanExpr,
}

/// Prove `goal` from `hypotheses` and return a Lean term, or decline.
///
/// The producers are tried in order — `ring` first because its normal-form
/// computation is deterministic and cheap, then `linarith`, whose bounded
/// Farkas search is the more expensive of the two. Neither is trusted: the
/// term each emits goes through this kernel's own `Kernel::infer` before it is
/// printed, and then through Lean's elaborator and kernel after.
///
/// # Errors
///
/// [`Decline`], with the reason string the wire carries.
pub fn prove_to_lean_term(
    dev: &mut Dev,
    hypotheses: &[Hypothesis],
    goal: &LeanExpr,
) -> Result<String, Decline> {
    let mut translator = Translator::new();
    let prelude = dev.prelude();

    // Hypotheses first, so a local that appears only in a hypothesis is still
    // bound to the same kernel free variable the goal would give it.
    let mut assumptions: Vec<(ExprId, ExprId)> = Vec::new();
    let mut hypothesis_names: Vec<String> = Vec::new();
    for hypothesis in hypotheses {
        // A hypothesis outside the fragment is skipped, not fatal: it is a
        // fact the producers simply will not use.
        if let Ok(ty) = translator.prop(dev, &hypothesis.ty) {
            let proof = translator.local(dev, &hypothesis.name);
            assumptions.push((ty, proof));
            hypothesis_names.push(hypothesis.name.clone());
        }
    }
    let goal_expr = translator.prop(dev, goal)?;

    let term = match ring::nat::prove(dev, &prelude, goal_expr) {
        Ok(term) => term,
        Err(ring_decline) => match linarith::nat::prove(dev, &prelude, &assumptions, goal_expr) {
            Ok(term) => term,
            Err(linarith_decline) => {
                return Err(Decline::Unknown(format!(
                    "ring declined ({ring_decline:?}) and linarith declined ({linarith_decline:?})"
                )));
            }
        },
    };

    recheck_in_this_kernel(dev, &translator, &hypothesis_names, &assumptions, term)?;

    let mut fvar_names: BTreeMap<ExprId, String> = BTreeMap::new();
    for (name, &(_, id)) in translator.fvars() {
        fvar_names.insert(id, name.clone());
    }
    print_lean(&dev.kernel, term, &fvar_names)
}

/// Re-check the emitted term with **this** kernel before Lean is asked to.
///
/// The producers hand back an *open* term over the goal's free variables, and
/// `Kernel::infer` refuses a free variable (`UnboundFVar`) rather than
/// inventing a context for it. So the term is closed first — ℕ variables
/// outermost, hypothesis proofs innermost, because a hypothesis's type mentions
/// the variables — and the closed term is what gets inferred.
///
/// This is a *convenience* check, not the soundness boundary: a producer bug
/// that slipped past it would still be caught by Lean. What it buys is that a
/// producer bug is reported as a producer bug here, instead of surfacing at the
/// far end as a Lean type error against a term nobody can read.
fn recheck_in_this_kernel(
    dev: &mut Dev,
    translator: &Translator,
    hypothesis_names: &[String],
    assumptions: &[(ExprId, ExprId)],
    term: ExprId,
) -> Result<(), Decline> {
    let nat = dev.nat_ty();
    let mut closed = term;
    // Innermost first: the hypotheses, each at its translated type.
    for (name, (ty, _)) in hypothesis_names.iter().zip(assumptions.iter()) {
        let Some(&(fv, _)) = translator.fvars().get(name) else {
            continue;
        };
        closed = dev.lam_fv(fv, *ty, closed);
    }
    // Then the ℕ variables, which is everything else.
    for (name, &(fv, _)) in translator.fvars() {
        if hypothesis_names.iter().any(|h| h == name) {
            continue;
        }
        closed = dev.lam_fv(fv, nat, closed);
    }
    if let Err(error) = dev.kernel.infer(closed) {
        let detail = dev.explain(&error);
        return Err(Decline::Unknown(format!(
            "a producer emitted a term this kernel refused: {detail}"
        )));
    }
    Ok(())
}

#[cfg(test)]
mod tests;
