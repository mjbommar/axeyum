//! The restricted-Rust runtime AST the proc-macro lowers a `#[verify]` function
//! into.
//!
//! This is intentionally small and `Clone`-able so the macro can emit it as a
//! plain Rust value and the runtime can interpret it symbolically. It is the
//! "small Rust-surface AST" that replaces the toy ISA of the symbolic-execution
//! template. Anything the front-end can't express in this AST is rejected at
//! macro time (a clean compile error), never silently mis-modeled.

/// A scalar type of a parameter or local: an `N`-bit integer (signed or not),
/// or a `bool`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ty {
    /// An `N`-bit integer; `signed` distinguishes `iN` from `uN` (it drives
    /// signed-vs-unsigned overflow, division, comparison, and shift semantics).
    Int {
        /// Width in bits (e.g. 8 for `u8`/`i8`, 32 for `u32`/`i32`).
        width: u32,
        /// `true` for `iN`, `false` for `uN`.
        signed: bool,
    },
    /// A `bool`.
    Bool,
}

impl Ty {
    /// The bit width if this is an integer type.
    #[must_use]
    pub fn width(self) -> Option<u32> {
        match self {
            Ty::Int { width, .. } => Some(width),
            Ty::Bool => None,
        }
    }

    /// Whether this integer type is signed (`false` for `bool`).
    #[must_use]
    pub fn is_signed(self) -> bool {
        matches!(self, Ty::Int { signed: true, .. })
    }
}

/// A binary operator over scalar expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    /// `+` (checked for overflow as a panic class).
    Add,
    /// `-` (checked for overflow/underflow).
    Sub,
    /// `*` (checked for overflow).
    Mul,
    /// `wrapping_add` — modular addition; never panics (no overflow class).
    WrappingAdd,
    /// `wrapping_sub` — modular subtraction; never panics.
    WrappingSub,
    /// `wrapping_mul` — modular multiplication; never panics.
    WrappingMul,
    /// `saturating_add` — clamps to the type's bound on overflow; never panics.
    SaturatingAdd,
    /// `saturating_sub` — clamps to the type's bound on overflow; never panics.
    SaturatingSub,
    /// `saturating_mul` — clamps to the type's bound on overflow; never panics.
    SaturatingMul,
    /// `a.min(b)` — the smaller operand (signedness from operand type).
    Min,
    /// `a.max(b)` — the larger operand (signedness from operand type).
    Max,
    /// `/` (checked for divide-by-zero; signedness from operand type).
    Div,
    /// `%` (checked for modulo-by-zero).
    Rem,
    /// `&` (bitwise on ints, logical-and on bools).
    BitAnd,
    /// `|` (bitwise on ints, logical-or on bools).
    BitOr,
    /// `^` (bitwise xor / bool xor).
    BitXor,
    /// `<<` (left shift; overflow-shift is a checked panic class).
    Shl,
    /// `>>` (right shift; arithmetic for signed, logical for unsigned).
    Shr,
    /// `==`.
    Eq,
    /// `!=`.
    Ne,
    /// `<`.
    Lt,
    /// `<=`.
    Le,
    /// `>`.
    Gt,
    /// `>=`.
    Ge,
    /// `&&` (short-circuit modeled as logical and over already-pure operands).
    And,
    /// `||`.
    Or,
}

/// A unary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    /// Arithmetic negation `-x` (checked: `iN::MIN` negation overflows).
    Neg,
    /// Bitwise `!x` on integers, logical not on bools.
    Not,
}

/// A pure scalar expression over parameters and locals.
#[derive(Debug, Clone)]
pub enum Expr {
    /// An integer literal of a given type.
    IntLit {
        /// The (unsigned bit-pattern) value, already masked to `ty.width()`.
        value: u128,
        /// The integer type.
        ty: Ty,
    },
    /// A boolean literal.
    BoolLit(bool),
    /// A variable reference by name (a parameter or `let` binding).
    Var(String),
    /// A binary operation.
    Binary {
        /// The operator.
        op: BinOp,
        /// Left operand.
        lhs: Box<Expr>,
        /// Right operand.
        rhs: Box<Expr>,
    },
    /// A unary operation.
    Unary {
        /// The operator.
        op: UnOp,
        /// The operand.
        operand: Box<Expr>,
    },
    /// Whether `lhs <op> rhs` would overflow the operand type (a *boolean*).
    /// `op` must be `Add`/`Sub`/`Mul`; lowers to the same `bv_*addo`/`subo`/`mulo`
    /// predicate the checked ops use. Used to model `checked_*` Option-flow
    /// (`unwrap_or` / `match`) without a panic class.
    Overflows {
        /// The arithmetic operator (`Add`, `Sub`, or `Mul`).
        op: BinOp,
        /// Left operand.
        lhs: Box<Expr>,
        /// Right operand.
        rhs: Box<Expr>,
    },
    /// `cond.then_else(a, b)` — the lowered form of an `if`/`else` *expression*
    /// (both arms scalar, same type).
    Ite {
        /// The boolean condition.
        cond: Box<Expr>,
        /// Value when `cond` holds.
        then: Box<Expr>,
        /// Value when `cond` is false.
        els: Box<Expr>,
    },
    /// `arr[idx]` — a fixed-length array/slice index. Indexing out of bounds is
    /// a checked panic class (`idx >= len`). The element type is `ty`.
    Index {
        /// The array variable name.
        array: String,
        /// The index expression.
        index: Box<Expr>,
        /// The element type.
        ty: Ty,
    },
    /// `expr.unwrap()` / `expr.expect(..)` on an `Option`: the inner value is
    /// `value`, reachable only when `is_some` holds; the `None` branch is a
    /// checked panic class. (`Some`/`None` are modeled by a symbolic
    /// discriminant the caller supplies as an input.)
    UnwrapOption {
        /// The boolean discriminant: `true` ⇒ `Some(value)`.
        is_some: Box<Expr>,
        /// The carried value (used when `is_some`).
        value: Box<Expr>,
    },
}

/// A statement in the (whitelisted) body.
#[derive(Debug, Clone)]
pub enum Stmt {
    /// `let name: ty = expr;`.
    Let {
        /// The binding name.
        name: String,
        /// The declared scalar type.
        ty: Ty,
        /// The initializer.
        value: Expr,
    },
    /// `name = expr;` — reassignment of an existing binding (same type).
    Assign {
        /// The target name.
        name: String,
        /// The new value.
        value: Expr,
    },
    /// `if cond { then } else { els }` as a *statement* (each block a sub-body).
    If {
        /// The condition.
        cond: Expr,
        /// The then-block.
        then: Vec<Stmt>,
        /// The optional else-block.
        els: Vec<Stmt>,
    },
    /// `assert!(cond)` / `assert_eq!(a, b)` — `!cond` reachable is a bug.
    Assert(Expr),
    /// `panic!(..)` / `unreachable!(..)` — reaching this point is a bug.
    Panic,
    /// A bare expression evaluated for its panic-class side effects (overflow,
    /// `unwrap`, indexing). Its value is discarded.
    Eval(Expr),
    /// `#[unwind(K)] for _ in 0..K { body }` — fully unrolled `K` times by the
    /// runtime (the bound is the honest unwind budget).
    For {
        /// The loop variable name (each iteration `i` gets a constant value).
        var: String,
        /// The integer type of the loop variable.
        var_ty: Ty,
        /// The (exclusive) bound `K`.
        bound: u128,
        /// The loop body.
        body: Vec<Stmt>,
    },
    /// `#[unwind(K)] while cond { body }` — bounded model checking by unrolling
    /// up to `bound` iterations: each iteration runs `body` under the path
    /// condition that `cond` (re-evaluated against the iteration's environment)
    /// still holds. Panic classes in `body` are checked at every reachable
    /// iteration; the guarantee is **bounded** ("no bug within `bound`
    /// iterations"), exactly like [`bounded_model_check`]'s
    /// `UnreachableWithinBound`. A data-dependent `cond` means later iterations
    /// run under a narrower path condition (they may be infeasible), so the
    /// check is sound without a fixed trip count.
    ///
    /// [`bounded_model_check`]: axeyum_solver::bounded_model_check
    While {
        /// The loop guard, re-evaluated per iteration.
        cond: Expr,
        /// The (maximum) number of iterations to unroll — the honest unwind
        /// budget `K`.
        bound: u128,
        /// The loop body.
        body: Vec<Stmt>,
    },
}

/// A declared input (parameter) of the verified function.
#[derive(Debug, Clone)]
pub struct Param {
    /// The parameter name.
    pub name: String,
    /// Its scalar type.
    pub ty: Ty,
}

/// A fixed-length array input: `name: [elem; len]` or a `&[elem]` whose length
/// is fixed to `len` for the bounded check. Each element is a fresh symbol.
#[derive(Debug, Clone)]
pub struct ArrayParam {
    /// The array variable name.
    pub name: String,
    /// The element type.
    pub elem: Ty,
    /// The (fixed) length used for the bounded check.
    pub len: u128,
}

/// A whole verified function lowered to the runtime AST.
#[derive(Debug, Clone)]
pub struct Program {
    /// The function name (used to name the generated test / report).
    pub name: String,
    /// Scalar parameters (the symbolic inputs).
    pub params: Vec<Param>,
    /// Fixed-length array parameters.
    pub arrays: Vec<ArrayParam>,
    /// The (whitelisted) body statements.
    pub body: Vec<Stmt>,
}
