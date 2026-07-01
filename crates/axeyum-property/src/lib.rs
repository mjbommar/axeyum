//! Typed prove-or-counterexample SDK over Axeyum evidence.
//!
//! This crate is a thin consumer-facing wrapper. It builds terms in an
//! [`axeyum_ir::TermArena`], then delegates proving to
//! [`axeyum_solver::prove`] or [`axeyum_solver::prove_minimized`]. It does not
//! add solver logic or weaken the underlying evidence contract.

use std::fmt::Write as _;

/// Counterexample → runnable `#[test]` rendering, shared by the EVM and verify
/// frontends (an app-agnostic [`Witness`] → [`render_reproduction_test`] layer).
pub mod reproduce;
pub use reproduce::{Reproduction, Witness, WitnessBinding, render_reproduction_test};

use axeyum_ir::{IrError, Sort, SymbolId, TermArena, TermId, Value};
pub use axeyum_property_macros::Symbolic;
pub use axeyum_solver::{
    EvidenceReport, Model, ProofFragment, ProofOutcome, ReconstructError, SolverConfig,
};
use axeyum_solver::{
    ModelMinimizeObjective, SolverError, UnknownKind, prove, prove_minimized_with_objectives,
    prove_unsat_to_lean_module,
};

/// Errors produced by the property SDK.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropertyError {
    /// Term construction failed.
    Ir(IrError),
    /// Solving or evidence production failed.
    Solver(SolverError),
    /// A model value had the wrong sort for the typed handle used to read it.
    ModelSortMismatch {
        /// The symbol whose value was being lifted.
        symbol: SymbolId,
        /// The value found in the model.
        value: Value,
    },
    /// A model value cannot be rendered as a native Rust literal by this SDK
    /// layer.
    UnsupportedRustLiteral {
        /// The original Axeyum symbol name.
        name: String,
        /// The value that could not be rendered.
        value: Value,
    },
    /// A requested Rust aggregate counterexample binding cannot be rendered.
    UnsupportedRustAggregate {
        /// The requested Axeyum input root, such as `transfer`.
        root: String,
        /// The binding name that made the aggregate unsupported, if any.
        binding: Option<String>,
        /// Why the aggregate cannot be rendered by this SDK layer.
        reason: String,
    },
}

impl core::fmt::Display for PropertyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            PropertyError::Ir(error) => write!(f, "{error}"),
            PropertyError::Solver(error) => write!(f, "{error}"),
            PropertyError::ModelSortMismatch { symbol, value } => write!(
                f,
                "model value for symbol #{} has the wrong sort: {value:?}",
                symbol.index()
            ),
            PropertyError::UnsupportedRustLiteral { name, value } => {
                write!(
                    f,
                    "cannot render counterexample input `{name}` with value {value:?} as a native Rust literal"
                )
            }
            PropertyError::UnsupportedRustAggregate {
                root,
                binding,
                reason,
            } => {
                if let Some(binding) = binding {
                    write!(
                        f,
                        "cannot render counterexample aggregate `{root}` because binding `{binding}` is unsupported: {reason}"
                    )
                } else {
                    write!(
                        f,
                        "cannot render counterexample aggregate `{root}`: {reason}"
                    )
                }
            }
        }
    }
}

impl std::error::Error for PropertyError {}

impl From<IrError> for PropertyError {
    fn from(error: IrError) -> Self {
        Self::Ir(error)
    }
}

impl From<SolverError> for PropertyError {
    fn from(error: SolverError) -> Self {
        Self::Solver(error)
    }
}

/// Declares a typed symbolic value and lifts it back from a replay-checked model.
///
/// Scalar, tuple, and derived-struct implementations let SDK users build
/// deterministic input bundles while keeping model lifting tied to typed
/// expression handles.
pub trait Symbolic {
    /// The expression handle or bundle of handles used while building terms.
    type Expr;
    /// The concrete Rust value recovered from a model.
    type Concrete;

    /// Declares this symbolic value under `name`.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if any underlying symbol declaration fails.
    fn symbolic(property: &mut Property, name: &str) -> Result<Self::Expr, PropertyError>;

    /// Lifts a concrete Rust value from `model` through `expr`.
    ///
    /// Returns `Ok(None)` if the model omits any required symbol.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if a model value has the wrong sort for its
    /// typed expression handle.
    fn concrete(expr: &Self::Expr, model: &Model) -> Result<Option<Self::Concrete>, PropertyError>;
}

/// Builder for macro-free symbolic values with named struct fields.
///
/// `#[derive(Symbolic)]` lowers named structs to this API. Frontends can also
/// use it directly when they need explicit control over field construction:
///
/// ```
/// # use axeyum_property::{Bool, Bv, Property, PropertyError};
/// struct Transfer {
///     enabled: Bool,
///     amount: Bv<64>,
/// }
///
/// # fn build() -> Result<Transfer, PropertyError> {
/// let mut property = Property::new();
/// let transfer = property.symbolic_struct("transfer", |fields| {
///     Ok(Transfer {
///         enabled: fields.field::<bool>("enabled")?,
///         amount: fields.field::<u64>("amount")?,
///     })
/// })?;
/// # Ok(transfer)
/// # }
/// ```
#[derive(Debug)]
pub struct SymbolicStruct<'a> {
    property: &'a mut Property,
    prefix: String,
}

impl SymbolicStruct<'_> {
    /// Declares a named field through [`Symbolic`].
    ///
    /// Field names are joined with `.` for Axeyum symbols, so
    /// `property.symbolic_struct("input", |f| f.field::<u8>("amount"))`
    /// declares `input.amount`. The counterexample renderer later sanitizes the
    /// dot to a Rust identifier such as `input_amount`.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if any underlying declaration fails.
    pub fn field<T: Symbolic>(&mut self, name: &str) -> Result<T::Expr, PropertyError> {
        T::symbolic(self.property, &join_symbolic_name(&self.prefix, name))
    }

    /// Declares a nested named field bundle.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if any declaration inside `build` fails.
    pub fn struct_field<R>(
        &mut self,
        name: &str,
        build: impl FnOnce(&mut SymbolicStruct<'_>) -> Result<R, PropertyError>,
    ) -> Result<R, PropertyError> {
        let prefix = join_symbolic_name(&self.prefix, name);
        let mut fields = SymbolicStruct {
            property: &mut *self.property,
            prefix,
        };
        build(&mut fields)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BvLiteralStyle {
    Unsigned,
    Signed,
}

/// One scalar input binding from a replay-checked counterexample model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputBinding {
    symbol: SymbolId,
    name: String,
    rust_ident: String,
    sort: Sort,
    value: Value,
    bv_literal_style: BvLiteralStyle,
}

impl InputBinding {
    /// The Axeyum symbol ID.
    #[must_use]
    pub fn symbol(&self) -> SymbolId {
        self.symbol
    }

    /// The original Axeyum symbol name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// A deterministic Rust-safe identifier derived from [`Self::name`].
    #[must_use]
    pub fn rust_ident(&self) -> &str {
        &self.rust_ident
    }

    /// The declared sort.
    #[must_use]
    pub fn sort(&self) -> Sort {
        self.sort
    }

    /// The model value.
    #[must_use]
    pub fn value(&self) -> &Value {
        &self.value
    }

    /// Renders this binding as a Rust `let` statement.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] for values outside the
    /// native scalar surface: Bool, Int, and BV widths up to 128 bits.
    pub fn render_rust_let(&self) -> Result<String, PropertyError> {
        match &self.value {
            Value::Bool(value) => Ok(format!("let {}: bool = {value};", self.rust_ident)),
            Value::Int(value) => Ok(format!(
                "let {}: i128 = {};",
                self.rust_ident,
                render_i128_literal(*value)
            )),
            Value::Bv { width, value } => match self.bv_literal_style {
                BvLiteralStyle::Unsigned => Ok(format!(
                    "let {}: {} = {}; // BV{}",
                    self.rust_ident,
                    rust_uint_type(*width),
                    render_uint_literal(*width, *value),
                    width
                )),
                BvLiteralStyle::Signed => Ok(format!(
                    "let {}: {} = {}; // BV{} two's-complement",
                    self.rust_ident,
                    rust_int_type(*width),
                    render_signed_bv_literal(*width, *value),
                    width
                )),
            },
            Value::WideBv(_)
            | Value::Array(_)
            | Value::GenericArray(_)
            | Value::Real(_)
            | Value::RealAlgebraic(_)
            | Value::Datatype { .. }
            // A sequence value is outside the native scalar Rust surface
            // (ADR-0051, P2.7); decline like the array/datatype siblings.
            | Value::Seq(_)
            | Value::Uninterpreted { .. } => Err(PropertyError::UnsupportedRustLiteral {
                name: self.name.clone(),
                value: self.value.clone(),
            }),
        }
    }
}

/// A deterministic view of a disproving model over SDK-declared inputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Counterexample {
    bindings: Vec<InputBinding>,
}

impl Counterexample {
    /// Creates a counterexample from already-normalized bindings.
    #[must_use]
    pub fn new(bindings: Vec<InputBinding>) -> Self {
        Self { bindings }
    }

    /// The input bindings in SDK declaration order.
    #[must_use]
    pub fn bindings(&self) -> &[InputBinding] {
        &self.bindings
    }

    /// Renders all bindings as Rust `let` statements.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] if any binding is not
    /// representable by a native Rust scalar literal.
    pub fn render_rust_let_bindings(&self) -> Result<String, PropertyError> {
        let mut out = String::new();
        for binding in &self.bindings {
            out.push_str(&binding.render_rust_let()?);
            out.push('\n');
        }
        Ok(out)
    }

    /// Renders a Rust named-struct binding from direct child inputs.
    ///
    /// The generated statement assumes [`Self::render_rust_let_bindings`] has
    /// already emitted the scalar field bindings it references. `root_name`
    /// selects direct children such as `transfer.enabled` and
    /// `transfer.amount`; nested children such as `transfer.limits.fee` are
    /// rejected because the SDK cannot infer the caller's nested Rust domain
    /// type. `rust_type` is inserted verbatim so callers can pass a path such as
    /// `crate::TransferInput`.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] if any selected scalar
    /// cannot be rendered, or [`PropertyError::UnsupportedRustAggregate`] if the
    /// selected names do not form direct Rust named fields.
    pub fn render_rust_named_struct_let(
        &self,
        root_name: &str,
        rust_type: &str,
        rust_ident: &str,
    ) -> Result<String, PropertyError> {
        let fields = self.direct_fields(root_name)?;
        let mut out = String::new();
        out.push_str("let ");
        out.push_str(&sanitize_rust_ident(rust_ident));
        out.push_str(": ");
        out.push_str(rust_type);
        out.push_str(" = ");
        out.push_str(rust_type);
        out.push_str(" {\n");
        for (field, binding) in fields {
            binding.render_rust_let()?;
            let Some(field_ident) = rust_field_ident(field) else {
                return Err(PropertyError::UnsupportedRustAggregate {
                    root: root_name.to_owned(),
                    binding: Some(binding.name().to_owned()),
                    reason: format!("field suffix `{field}` is not a Rust named field"),
                });
            };
            out.push_str("    ");
            out.push_str(&field_ident);
            out.push_str(": ");
            out.push_str(binding.rust_ident());
            out.push_str(",\n");
        }
        out.push_str("};\n");
        Ok(out)
    }

    /// Renders a Rust named-struct binding with explicit caller-owned fields.
    ///
    /// Direct scalar children of `root_name` are included exactly as in
    /// [`Self::render_rust_named_struct_let`]. Nested descendants are ignored
    /// instead of inferred; callers can render those nested aggregates
    /// separately and pass field expressions such as `("limits",
    /// "transfer_limits")` through `extra_fields`.
    ///
    /// This is the deliberate escape hatch for frontend/domain replay shapes:
    /// the SDK verifies and reuses scalar model bindings, but the caller owns
    /// the nested Rust domain expression it asks to splice into the initializer.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] if any included direct
    /// scalar cannot be rendered, or [`PropertyError::UnsupportedRustAggregate`]
    /// if a Rust field name is invalid, a caller-supplied field duplicates a
    /// direct field, or no direct/caller-supplied fields are available.
    pub fn render_rust_named_struct_let_with_fields<I, F, E>(
        &self,
        root_name: &str,
        rust_type: &str,
        rust_ident: &str,
        extra_fields: I,
    ) -> Result<String, PropertyError>
    where
        I: IntoIterator<Item = (F, E)>,
        F: AsRef<str>,
        E: AsRef<str>,
    {
        let prefix = format!("{root_name}.");
        let mut fields = Vec::new();
        for binding in &self.bindings {
            let Some(suffix) = binding.name().strip_prefix(&prefix) else {
                continue;
            };
            if suffix.is_empty() || suffix.contains('.') {
                continue;
            }
            binding.render_rust_let()?;
            let Some(field_ident) = rust_field_ident(suffix) else {
                return Err(PropertyError::UnsupportedRustAggregate {
                    root: root_name.to_owned(),
                    binding: Some(binding.name().to_owned()),
                    reason: format!("field suffix `{suffix}` is not a Rust named field"),
                });
            };
            fields.push((field_ident, binding.rust_ident().to_owned()));
        }

        for (field, expr) in extra_fields {
            let field = field.as_ref();
            let expr = expr.as_ref();
            let Some(field_ident) = rust_field_ident(field) else {
                return Err(PropertyError::UnsupportedRustAggregate {
                    root: root_name.to_owned(),
                    binding: None,
                    reason: format!("field suffix `{field}` is not a Rust named field"),
                });
            };
            if fields.iter().any(|(existing, _)| existing == &field_ident) {
                return Err(PropertyError::UnsupportedRustAggregate {
                    root: root_name.to_owned(),
                    binding: None,
                    reason: format!("field `{field}` is already initialized"),
                });
            }
            if expr.trim().is_empty() {
                return Err(PropertyError::UnsupportedRustAggregate {
                    root: root_name.to_owned(),
                    binding: None,
                    reason: format!("field `{field}` has an empty Rust expression"),
                });
            }
            fields.push((field_ident, expr.to_owned()));
        }

        if fields.is_empty() {
            return Err(PropertyError::UnsupportedRustAggregate {
                root: root_name.to_owned(),
                binding: None,
                reason: "no direct scalar fields or caller-supplied fields found for this root"
                    .to_owned(),
            });
        }

        Ok(render_named_struct_let(rust_type, rust_ident, &fields))
    }

    /// Renders a Rust tuple-struct binding from direct numeric child inputs.
    ///
    /// The generated statement assumes [`Self::render_rust_let_bindings`] has
    /// already emitted the scalar field bindings it references. `root_name`
    /// selects direct numeric children such as `pair.0` and `pair.1`.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] if any selected scalar
    /// cannot be rendered, or [`PropertyError::UnsupportedRustAggregate`] if the
    /// selected names do not form contiguous tuple positions starting at `0`.
    pub fn render_rust_tuple_struct_let(
        &self,
        root_name: &str,
        rust_type: &str,
        rust_ident: &str,
    ) -> Result<String, PropertyError> {
        let mut fields = Vec::new();
        for (field, binding) in self.direct_fields(root_name)? {
            binding.render_rust_let()?;
            let Ok(index) = field.parse::<usize>() else {
                return Err(PropertyError::UnsupportedRustAggregate {
                    root: root_name.to_owned(),
                    binding: Some(binding.name().to_owned()),
                    reason: format!("field suffix `{field}` is not a tuple index"),
                });
            };
            fields.push((index, binding));
        }
        fields.sort_by_key(|(index, _)| *index);
        for (expected, (actual, binding)) in fields.iter().enumerate() {
            if *actual != expected {
                return Err(PropertyError::UnsupportedRustAggregate {
                    root: root_name.to_owned(),
                    binding: Some(binding.name().to_owned()),
                    reason: format!("tuple fields must be contiguous from 0, found {actual}"),
                });
            }
        }

        let mut out = String::new();
        out.push_str("let ");
        out.push_str(&sanitize_rust_ident(rust_ident));
        out.push_str(": ");
        out.push_str(rust_type);
        out.push_str(" = ");
        out.push_str(rust_type);
        out.push('(');
        for (i, (_, binding)) in fields.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            out.push_str(binding.rust_ident());
        }
        out.push_str(");\n");
        Ok(out)
    }

    /// Renders a complete Rust `#[test]` skeleton.
    ///
    /// `body` is inserted after the generated input bindings and should contain
    /// the caller's domain replay/assertion code. This function intentionally
    /// does not invent replay semantics; it only makes the model values
    /// reproducible in Rust syntax.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] if any binding is not
    /// representable by a native Rust scalar literal.
    pub fn render_rust_test(&self, test_name: &str, body: &str) -> Result<String, PropertyError> {
        self.render_rust_test_with_prelude(
            test_name,
            std::iter::empty::<&str>(),
            std::iter::empty::<&str>(),
            body,
        )
    }

    /// Renders a complete Rust `#[test]` skeleton with caller-owned setup code.
    ///
    /// Scalar bindings are emitted first from the replay-checked model.
    /// `setup_snippets` are then inserted verbatim, one indented block at a
    /// time, before `body`. This is intended for frontend/domain replay code
    /// such as aggregate initializers rendered by
    /// [`Self::render_rust_named_struct_let`] or
    /// [`Self::render_rust_named_struct_let_with_fields`].
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] if any binding is not
    /// representable by a native Rust scalar literal.
    pub fn render_rust_test_with_setup<I, S>(
        &self,
        test_name: &str,
        setup_snippets: I,
        body: &str,
    ) -> Result<String, PropertyError>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        self.render_rust_test_with_prelude(
            test_name,
            std::iter::empty::<&str>(),
            setup_snippets,
            body,
        )
    }

    /// Renders a complete Rust `#[test]` skeleton with caller-owned prelude and setup code.
    ///
    /// `prelude_snippets` are inserted before the `#[test]` item without
    /// indentation, making them suitable for frontend-owned imports, helper
    /// type aliases, or small replay adapters. Scalar bindings are then emitted
    /// first inside the function from the replay-checked model, followed by
    /// caller-owned setup snippets and finally `body`.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] if any binding is not
    /// representable by a native Rust scalar literal.
    pub fn render_rust_test_with_prelude<PI, P, SI, S>(
        &self,
        test_name: &str,
        prelude_snippets: PI,
        setup_snippets: SI,
        body: &str,
    ) -> Result<String, PropertyError>
    where
        PI: IntoIterator<Item = P>,
        P: AsRef<str>,
        SI: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let mut out = String::new();
        let mut wrote_prelude = false;
        for snippet in prelude_snippets {
            let snippet = snippet.as_ref();
            if snippet.is_empty() {
                continue;
            }
            if wrote_prelude {
                out.push('\n');
            }
            push_unindented_block(&mut out, snippet);
            wrote_prelude = true;
        }
        if wrote_prelude {
            out.push('\n');
        }
        out.push_str("#[test]\n");
        out.push_str("fn ");
        out.push_str(&sanitize_rust_ident(test_name));
        out.push_str("() {\n");
        for binding in &self.bindings {
            out.push_str("    ");
            out.push_str(&binding.render_rust_let()?);
            out.push('\n');
        }
        for snippet in setup_snippets {
            push_indented_block(&mut out, snippet.as_ref());
        }
        push_indented_block(&mut out, body);
        out.push_str("}\n");
        Ok(out)
    }

    /// Renders a Rust replay call expression.
    ///
    /// `replay_fn` and `args` are caller-owned Rust expressions. This helper
    /// intentionally does not validate or interpret them; it only formats the
    /// repeated `replay_fn(args...)` shape used by the generated test adapters.
    pub fn render_rust_replay_call<I, A>(replay_fn: &str, args: I) -> String
    where
        I: IntoIterator<Item = A>,
        A: AsRef<str>,
    {
        let mut out = String::new();
        out.push_str(replay_fn);
        out.push('(');
        for (index, arg) in args.into_iter().enumerate() {
            if index > 0 {
                out.push_str(", ");
            }
            out.push_str(arg.as_ref());
        }
        out.push(')');
        out
    }

    /// Renders the common Rust Boolean replay assertion body.
    ///
    /// `replay_fn` and `args` are caller-owned Rust expressions. This helper
    /// intentionally does not validate or interpret them; it only formats the
    /// repeated `assert!(replay_fn(args...));` shape used by generated
    /// counterexample tests.
    pub fn render_rust_replay_assertion<I, A>(replay_fn: &str, args: I) -> String
    where
        I: IntoIterator<Item = A>,
        A: AsRef<str>,
    {
        let call = Self::render_rust_replay_call(replay_fn, args);
        let mut out = String::new();
        out.push_str("assert!(");
        out.push_str(&call);
        out.push_str(");\n");
        out
    }

    /// Renders a Rust replay body for frontends whose replay function returns
    /// `Result<(), E>`.
    ///
    /// The helper formats `replay_fn(args...).expect(message);`; the replay
    /// function path, argument expressions, and domain result type remain
    /// caller-owned.
    pub fn render_rust_replay_expect_ok<I, A>(
        replay_fn: &str,
        args: I,
        expect_message: &str,
    ) -> String
    where
        I: IntoIterator<Item = A>,
        A: AsRef<str>,
    {
        let mut out = Self::render_rust_replay_call(replay_fn, args);
        out.push_str(".expect(");
        push_rust_string_literal(&mut out, expect_message);
        out.push_str(");\n");
        out
    }

    /// Renders a Rust replay body for frontends whose replay function returns
    /// `Result<bool, E>`.
    ///
    /// The helper formats `assert!(replay_fn(args...).expect(message));`; the
    /// replay function path, argument expressions, and domain result type
    /// remain caller-owned.
    pub fn render_rust_replay_expect_ok_assertion<I, A>(
        replay_fn: &str,
        args: I,
        expect_message: &str,
    ) -> String
    where
        I: IntoIterator<Item = A>,
        A: AsRef<str>,
    {
        let call = Self::render_rust_replay_call(replay_fn, args);
        let mut out = String::new();
        out.push_str("assert!(");
        out.push_str(&call);
        out.push_str(".expect(");
        push_rust_string_literal(&mut out, expect_message);
        out.push_str("));\n");
        out
    }

    /// Renders a Rust `#[test]` skeleton whose body is a replay assertion.
    ///
    /// This is a convenience wrapper over
    /// [`Self::render_rust_test_with_prelude`] and
    /// [`Self::render_rust_replay_assertion`]. Prelude snippets, setup
    /// snippets, the replay function path, and argument expressions remain
    /// caller-owned so the SDK still does not invent frontend/domain replay
    /// semantics.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] if any binding is not
    /// representable by a native Rust scalar literal.
    pub fn render_rust_test_with_replay_assertion<PI, P, SI, S, AI, A>(
        &self,
        test_name: &str,
        prelude_snippets: PI,
        setup_snippets: SI,
        replay_fn: &str,
        args: AI,
    ) -> Result<String, PropertyError>
    where
        PI: IntoIterator<Item = P>,
        P: AsRef<str>,
        SI: IntoIterator<Item = S>,
        S: AsRef<str>,
        AI: IntoIterator<Item = A>,
        A: AsRef<str>,
    {
        let body = Self::render_rust_replay_assertion(replay_fn, args);
        self.render_rust_test_with_prelude(
            test_name,
            prelude_snippets,
            setup_snippets,
            body.as_str(),
        )
    }

    /// Renders a Rust `#[test]` skeleton whose body expects a successful
    /// `Result<(), E>` replay.
    ///
    /// This is a convenience wrapper over
    /// [`Self::render_rust_test_with_prelude`] and
    /// [`Self::render_rust_replay_expect_ok`]. Prelude snippets, setup
    /// snippets, the replay function path, argument expressions, and failure
    /// message remain caller-owned.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] if any binding is not
    /// representable by a native Rust scalar literal.
    pub fn render_rust_test_with_replay_expect_ok<PI, P, SI, S, AI, A>(
        &self,
        test_name: &str,
        prelude_snippets: PI,
        setup_snippets: SI,
        replay_fn: &str,
        args: AI,
        expect_message: &str,
    ) -> Result<String, PropertyError>
    where
        PI: IntoIterator<Item = P>,
        P: AsRef<str>,
        SI: IntoIterator<Item = S>,
        S: AsRef<str>,
        AI: IntoIterator<Item = A>,
        A: AsRef<str>,
    {
        let body = Self::render_rust_replay_expect_ok(replay_fn, args, expect_message);
        self.render_rust_test_with_prelude(
            test_name,
            prelude_snippets,
            setup_snippets,
            body.as_str(),
        )
    }

    /// Renders a Rust `#[test]` skeleton whose body expects a successful
    /// `Result<bool, E>` replay and asserts the returned Boolean.
    ///
    /// This is a convenience wrapper over
    /// [`Self::render_rust_test_with_prelude`] and
    /// [`Self::render_rust_replay_expect_ok_assertion`]. Prelude snippets,
    /// setup snippets, the replay function path, argument expressions, and
    /// failure message remain caller-owned.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::UnsupportedRustLiteral`] if any binding is not
    /// representable by a native Rust scalar literal.
    pub fn render_rust_test_with_replay_expect_ok_assertion<PI, P, SI, S, AI, A>(
        &self,
        test_name: &str,
        prelude_snippets: PI,
        setup_snippets: SI,
        replay_fn: &str,
        args: AI,
        expect_message: &str,
    ) -> Result<String, PropertyError>
    where
        PI: IntoIterator<Item = P>,
        P: AsRef<str>,
        SI: IntoIterator<Item = S>,
        S: AsRef<str>,
        AI: IntoIterator<Item = A>,
        A: AsRef<str>,
    {
        let body = Self::render_rust_replay_expect_ok_assertion(replay_fn, args, expect_message);
        self.render_rust_test_with_prelude(
            test_name,
            prelude_snippets,
            setup_snippets,
            body.as_str(),
        )
    }

    /// Renders a `#[cfg(test)]` Rust module around generated test items.
    ///
    /// `module_prelude_snippets` and `test_snippets` are caller-owned Rust
    /// item blocks. This helper only supplies deterministic module framing and
    /// indentation, so imports, helper functions, domain fixtures, and generated
    /// `#[test]` items remain under frontend control.
    pub fn render_rust_test_module<PI, P, TI, T>(
        module_name: &str,
        module_prelude_snippets: PI,
        test_snippets: TI,
    ) -> String
    where
        PI: IntoIterator<Item = P>,
        P: AsRef<str>,
        TI: IntoIterator<Item = T>,
        T: AsRef<str>,
    {
        let mut out = String::new();
        out.push_str("#[cfg(test)]\n");
        out.push_str("mod ");
        out.push_str(&sanitize_rust_ident(module_name));
        out.push_str(" {\n");
        let mut wrote_block = false;
        for snippet in module_prelude_snippets {
            let snippet = snippet.as_ref();
            if snippet.is_empty() {
                continue;
            }
            if wrote_block {
                out.push('\n');
            }
            push_indented_block(&mut out, snippet);
            wrote_block = true;
        }
        for snippet in test_snippets {
            let snippet = snippet.as_ref();
            if snippet.is_empty() {
                continue;
            }
            if wrote_block {
                out.push('\n');
            }
            push_indented_block(&mut out, snippet);
            wrote_block = true;
        }
        out.push_str("}\n");
        out
    }

    /// Renders a Rust fixture file from caller-owned top-level blocks.
    ///
    /// `file_prelude_snippets` are intended for crate attributes, imports, type
    /// definitions, and shared helpers. `test_item_snippets` are usually
    /// generated modules from [`Self::render_rust_test_module`] or standalone
    /// `#[test]` items. Blocks are emitted without indentation and separated by
    /// one blank line; empty snippets are ignored.
    pub fn render_rust_test_file<PI, P, TI, T>(
        file_prelude_snippets: PI,
        test_item_snippets: TI,
    ) -> String
    where
        PI: IntoIterator<Item = P>,
        P: AsRef<str>,
        TI: IntoIterator<Item = T>,
        T: AsRef<str>,
    {
        let mut out = String::new();
        let mut wrote_block = false;
        for snippet in file_prelude_snippets {
            let snippet = snippet.as_ref();
            if snippet.is_empty() {
                continue;
            }
            if wrote_block {
                out.push('\n');
            }
            push_unindented_block(&mut out, snippet);
            wrote_block = true;
        }
        for snippet in test_item_snippets {
            let snippet = snippet.as_ref();
            if snippet.is_empty() {
                continue;
            }
            if wrote_block {
                out.push('\n');
            }
            push_unindented_block(&mut out, snippet);
            wrote_block = true;
        }
        out
    }

    fn direct_fields<'a>(
        &'a self,
        root_name: &str,
    ) -> Result<Vec<(&'a str, &'a InputBinding)>, PropertyError> {
        let prefix = format!("{root_name}.");
        let mut fields = Vec::new();
        for binding in &self.bindings {
            let Some(suffix) = binding.name().strip_prefix(&prefix) else {
                continue;
            };
            if suffix.is_empty() || suffix.contains('.') {
                return Err(PropertyError::UnsupportedRustAggregate {
                    root: root_name.to_owned(),
                    binding: Some(binding.name().to_owned()),
                    reason: "only direct scalar fields can be rendered as a Rust aggregate"
                        .to_owned(),
                });
            }
            fields.push((suffix, binding));
        }
        if fields.is_empty() {
            return Err(PropertyError::UnsupportedRustAggregate {
                root: root_name.to_owned(),
                binding: None,
                reason: "no direct scalar fields found for this root".to_owned(),
            });
        }
        Ok(fields)
    }
}

fn render_named_struct_let(
    rust_type: &str,
    rust_ident: &str,
    fields: &[(String, String)],
) -> String {
    let mut out = String::new();
    out.push_str("let ");
    out.push_str(&sanitize_rust_ident(rust_ident));
    out.push_str(": ");
    out.push_str(rust_type);
    out.push_str(" = ");
    out.push_str(rust_type);
    out.push_str(" {\n");
    for (field, expr) in fields {
        out.push_str("    ");
        out.push_str(field);
        out.push_str(": ");
        out.push_str(expr);
        out.push_str(",\n");
    }
    out.push_str("};\n");
    out
}

fn push_unindented_block(out: &mut String, block: &str) {
    for line in block.lines() {
        out.push_str(line);
        out.push('\n');
    }
}

fn push_rust_string_literal(out: &mut String, value: &str) {
    out.push('"');
    for ch in value.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch.is_control() => {
                write!(out, "\\u{{{:x}}}", ch as u32).expect("write string");
            }
            ch => out.push(ch),
        }
    }
    out.push('"');
}

fn push_indented_block(out: &mut String, block: &str) {
    for line in block.lines() {
        if line.is_empty() {
            out.push('\n');
        } else {
            out.push_str("    ");
            out.push_str(line);
            out.push('\n');
        }
    }
}

/// A standalone Lean module proving a refuted property query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanModule {
    /// The reconstruction route that produced the module.
    pub fragment: ProofFragment,
    /// Self-contained Lean 4 source for the refutation.
    pub source: String,
}

/// A property proof attempt with optional Lean-module packaging.
#[derive(Debug, Clone)]
pub struct ProofCertificate {
    /// The ordinary checked Axeyum proof outcome.
    pub outcome: ProofOutcome,
    /// A standalone Lean module when reconstruction supports the proved fragment.
    pub lean_module: Option<LeanModule>,
    /// Why Lean-module reconstruction was unavailable for a proved result.
    ///
    /// This is `None` for disproved/unknown outcomes because no unsat refutation
    /// exists to reconstruct.
    pub lean_error: Option<ReconstructError>,
}

/// Frontend-friendly summary of a [`ProofCertificate`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofCertificateSummary {
    /// Decided proof status without carrying a full model or proof artifact.
    pub outcome: ProofOutcomeSummary,
    /// Evidence route and trust summary for proved outcomes.
    pub evidence: Option<EvidenceSummary>,
    /// Lean reconstruction availability.
    pub lean: LeanSummary,
}

/// Compact proof outcome for UI/reporting code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofOutcomeSummary {
    /// The property was proved from checked Axeyum evidence.
    Proved,
    /// The property was disproved by a replay-checked model.
    Disproved,
    /// The property was not decided.
    Unknown {
        /// Stable classified unknown kind.
        kind: &'static str,
        /// Backend or route detail.
        detail: String,
    },
}

/// Evidence/provenance summary for a proved property.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvidenceSummary {
    /// Stable evidence variant label.
    pub kind: &'static str,
    /// Deciding route/backend recorded in the evidence provenance.
    pub backend: String,
    /// Number of assertions in the refutation query.
    pub assertion_count: usize,
    /// Executable-semantics version used by the checker.
    pub semantics_version: &'static str,
    /// Trust reductions this result depended on, in canonical order.
    pub trust_steps: Vec<TrustStepSummary>,
}

/// One trust-ledger row used by a specific proof result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustStepSummary {
    /// Stable trust-step label.
    pub label: &'static str,
    /// One-line meaning from the trust ledger.
    pub meaning: &'static str,
    /// ADR/reference for the reduction.
    pub reference: &'static str,
    /// cvc5-style pedantic score.
    pub pedantic_level: u8,
    /// Whether the global ledger marks every use of this reduction certified.
    pub ledger_certified: bool,
    /// Whether this particular proof run carried an independent certificate.
    pub certified_this_run: bool,
}

/// Lean reconstruction summary for a proof attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanSummary {
    /// Whether a Lean module is available, unsupported, or not applicable.
    pub status: LeanStatus,
    /// Reconstruction fragment when a module was produced.
    pub fragment: Option<ProofFragment>,
    /// Size of the generated Lean source, when present.
    pub source_bytes: Option<usize>,
    /// Reconstruction diagnostic for proved results outside the current Lean
    /// surface.
    pub error: Option<ReconstructError>,
}

/// Lean reconstruction availability.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LeanStatus {
    /// A standalone Lean module was produced.
    Available,
    /// The property was proved, but this fragment did not reconstruct to Lean.
    Unsupported,
    /// No refutation exists to reconstruct, because the property was disproved
    /// or unknown.
    NotApplicable,
}

impl ProofCertificate {
    /// Returns the checked evidence report for proved outcomes.
    #[must_use]
    pub fn evidence_report(&self) -> Option<&EvidenceReport> {
        match &self.outcome {
            ProofOutcome::Proved(report) => Some(report),
            ProofOutcome::Disproved(_) | ProofOutcome::Unknown(_) => None,
        }
    }

    /// Builds a compact owned summary for frontend reports.
    #[must_use]
    pub fn summary(&self) -> ProofCertificateSummary {
        ProofCertificateSummary {
            outcome: summarize_proof_outcome(&self.outcome),
            evidence: self.evidence_report().map(summarize_evidence_report),
            lean: summarize_lean(self),
        }
    }
}

fn summarize_proof_outcome(outcome: &ProofOutcome) -> ProofOutcomeSummary {
    match outcome {
        ProofOutcome::Proved(_) => ProofOutcomeSummary::Proved,
        ProofOutcome::Disproved(_) => ProofOutcomeSummary::Disproved,
        ProofOutcome::Unknown(reason) => ProofOutcomeSummary::Unknown {
            kind: unknown_kind_label(reason.kind),
            detail: reason.detail.clone(),
        },
    }
}

fn summarize_evidence_report(report: &EvidenceReport) -> EvidenceSummary {
    EvidenceSummary {
        kind: report.evidence.kind_label(),
        backend: report.provenance.backend.clone(),
        assertion_count: report.provenance.assertion_count,
        semantics_version: report.provenance.semantics_version,
        trust_steps: report
            .trusted_steps
            .iter()
            .map(|step| {
                let id = step.id;
                TrustStepSummary {
                    label: id.label(),
                    meaning: id.meaning(),
                    reference: id.reference(),
                    pedantic_level: id.pedantic_level(),
                    ledger_certified: id.is_certified(),
                    certified_this_run: step.certified,
                }
            })
            .collect(),
    }
}

fn summarize_lean(certificate: &ProofCertificate) -> LeanSummary {
    if let Some(module) = &certificate.lean_module {
        LeanSummary {
            status: LeanStatus::Available,
            fragment: Some(module.fragment),
            source_bytes: Some(module.source.len()),
            error: None,
        }
    } else if let Some(error) = &certificate.lean_error {
        LeanSummary {
            status: LeanStatus::Unsupported,
            fragment: None,
            source_bytes: None,
            error: Some(error.clone()),
        }
    } else {
        LeanSummary {
            status: LeanStatus::NotApplicable,
            fragment: None,
            source_bytes: None,
            error: None,
        }
    }
}

fn unknown_kind_label(kind: UnknownKind) -> &'static str {
    match kind {
        UnknownKind::Timeout => "timeout",
        UnknownKind::ResourceLimit => "resource-limit",
        UnknownKind::MemoryLimit => "memory-limit",
        UnknownKind::NodeBudget => "node-budget",
        UnknownKind::EncodingBudget => "encoding-budget",
        UnknownKind::Incomplete => "incomplete",
        UnknownKind::Other => "other",
        _ => "unknown",
    }
}

/// A typed property-building context.
#[derive(Debug, Clone)]
pub struct Property {
    arena: TermArena,
    hypotheses: Vec<TermId>,
    counterexample_symbols: Vec<SymbolId>,
    counterexample_bv_literal_styles: Vec<(SymbolId, BvLiteralStyle)>,
    config: SolverConfig,
}

impl Default for Property {
    fn default() -> Self {
        Self::new()
    }
}

impl Property {
    /// Creates an empty property context with the default solver configuration.
    #[must_use]
    pub fn new() -> Self {
        Self {
            arena: TermArena::new(),
            hypotheses: Vec::new(),
            counterexample_symbols: Vec::new(),
            counterexample_bv_literal_styles: Vec::new(),
            config: SolverConfig::default(),
        }
    }

    /// Creates an empty property context with an explicit solver configuration.
    #[must_use]
    pub fn with_config(config: SolverConfig) -> Self {
        Self {
            config,
            ..Self::new()
        }
    }

    /// The underlying term arena.
    #[must_use]
    pub fn arena(&self) -> &TermArena {
        &self.arena
    }

    /// The underlying term arena, for advanced term construction.
    pub fn arena_mut(&mut self) -> &mut TermArena {
        &mut self.arena
    }

    /// The solver configuration used by future proof calls.
    #[must_use]
    pub fn config(&self) -> &SolverConfig {
        &self.config
    }

    /// Mutates the solver configuration used by future proof calls.
    pub fn config_mut(&mut self) -> &mut SolverConfig {
        &mut self.config
    }

    /// Declares a Boolean input symbol and includes it in minimization order.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if the symbol name conflicts with an existing
    /// declaration.
    pub fn bool(&mut self, name: &str) -> Result<Bool, PropertyError> {
        let symbol = self.arena.declare(name, Sort::Bool)?;
        let term = self.arena.var(symbol);
        self.track_symbol(symbol);
        Ok(Bool {
            term,
            symbol: Some(symbol),
        })
    }

    /// Declares a bit-vector input symbol and includes it in minimization order.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if `W` is not a valid bit-vector width or the
    /// symbol name conflicts with an existing declaration.
    pub fn bv<const W: u32>(&mut self, name: &str) -> Result<Bv<W>, PropertyError> {
        self.bv_with_literal_style(name, BvLiteralStyle::Unsigned)
    }

    /// Declares a bit-vector input symbol rendered as a signed Rust integer.
    ///
    /// The SMT sort is still `BitVec(W)` and all bit-vector operations remain
    /// explicit on [`Bv`]. This method records two's-complement Rust intent for
    /// counterexample rendering and signed-order counterexample minimization.
    /// Unsupported signed minimization widths are reported by
    /// [`Self::prove_minimized`].
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if `W` is not a valid bit-vector width or the
    /// symbol name conflicts with an existing declaration.
    pub fn signed_bv<const W: u32>(&mut self, name: &str) -> Result<Bv<W>, PropertyError> {
        self.bv_with_literal_style(name, BvLiteralStyle::Signed)
    }

    fn bv_with_literal_style<const W: u32>(
        &mut self,
        name: &str,
        literal_style: BvLiteralStyle,
    ) -> Result<Bv<W>, PropertyError> {
        let symbol = self.arena.declare(name, Sort::BitVec(W))?;
        let term = self.arena.var(symbol);
        self.track_bv_symbol(symbol, literal_style);
        Ok(Bv {
            term,
            symbol: Some(symbol),
        })
    }

    /// Declares an integer input symbol and includes it in minimization order.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if the symbol name conflicts with an existing
    /// declaration.
    pub fn int(&mut self, name: &str) -> Result<Int, PropertyError> {
        let symbol = self.arena.declare(name, Sort::Int)?;
        let term = self.arena.var(symbol);
        self.track_symbol(symbol);
        Ok(Int {
            term,
            symbol: Some(symbol),
        })
    }

    /// Declares a typed symbolic value through [`Symbolic`].
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if any underlying declaration fails.
    pub fn symbolic<T: Symbolic>(&mut self, name: &str) -> Result<T::Expr, PropertyError> {
        T::symbolic(self, name)
    }

    /// Declares a named symbolic field bundle.
    ///
    /// This is the macro-free path for struct-shaped inputs. It keeps the
    /// declaration and counterexample-objective order exactly as the closure
    /// requests fields.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if any declaration inside `build` fails.
    pub fn symbolic_struct<R>(
        &mut self,
        name: &str,
        build: impl FnOnce(&mut SymbolicStruct<'_>) -> Result<R, PropertyError>,
    ) -> Result<R, PropertyError> {
        let mut fields = SymbolicStruct {
            property: self,
            prefix: name.to_owned(),
        };
        build(&mut fields)
    }

    /// Creates a Boolean constant.
    pub fn bool_const(&mut self, value: bool) -> Bool {
        Bool {
            term: self.arena.bool_const(value),
            symbol: None,
        }
    }

    /// Creates a bit-vector constant.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if `W` is invalid or `value` does not fit.
    pub fn bv_const<const W: u32>(&mut self, value: u128) -> Result<Bv<W>, PropertyError> {
        Ok(Bv {
            term: self.arena.bv_const(W, value)?,
            symbol: None,
        })
    }

    /// Creates an integer constant.
    pub fn int_const(&mut self, value: i128) -> Int {
        Int {
            term: self.arena.int_const(value),
            symbol: None,
        }
    }

    /// Adds a hypothesis that must hold for the property.
    pub fn assume(&mut self, condition: Bool) {
        self.hypotheses.push(condition.term);
    }

    /// Builds a conjunction over `conditions`.
    ///
    /// Empty input returns `true`. This is the builder-style equivalent of
    /// repeated [`Bool::and`] calls and deliberately keeps term-construction
    /// errors explicit.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if any conjunction term cannot be built.
    pub fn all(
        &mut self,
        conditions: impl IntoIterator<Item = Bool>,
    ) -> Result<Bool, PropertyError> {
        let mut acc: Option<Bool> = None;
        for condition in conditions {
            acc = Some(match acc {
                Some(current) => current.and(self, condition)?,
                None => condition,
            });
        }
        Ok(acc.unwrap_or_else(|| self.bool_const(true)))
    }

    /// Builds a disjunction over `conditions`.
    ///
    /// Empty input returns `false`. This is the builder-style equivalent of
    /// repeated [`Bool::or`] calls and deliberately keeps term-construction
    /// errors explicit.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if any disjunction term cannot be built.
    pub fn any(
        &mut self,
        conditions: impl IntoIterator<Item = Bool>,
    ) -> Result<Bool, PropertyError> {
        let mut acc: Option<Bool> = None;
        for condition in conditions {
            acc = Some(match acc {
                Some(current) => current.or(self, condition)?,
                None => condition,
            });
        }
        Ok(acc.unwrap_or_else(|| self.bool_const(false)))
    }

    /// Builder-style Boolean negation.
    ///
    /// This is equivalent to [`Bool::not`] but keeps the arena owner first in
    /// call sites that prefer `property.bool_not(x)?`.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bool_not(&mut self, condition: Bool) -> Result<Bool, PropertyError> {
        condition.not(self)
    }

    /// Builder-style Boolean conjunction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bool_and(&mut self, lhs: Bool, rhs: Bool) -> Result<Bool, PropertyError> {
        lhs.and(self, rhs)
    }

    /// Builder-style Boolean disjunction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bool_or(&mut self, lhs: Bool, rhs: Bool) -> Result<Bool, PropertyError> {
        lhs.or(self, rhs)
    }

    /// Builder-style Boolean implication.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bool_implies(&mut self, lhs: Bool, rhs: Bool) -> Result<Bool, PropertyError> {
        lhs.implies(self, rhs)
    }

    /// Builder-style Boolean equality.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bool_equals(&mut self, lhs: Bool, rhs: Bool) -> Result<Bool, PropertyError> {
        lhs.equals(self, rhs)
    }

    /// Builder-style BV wrapping addition.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_add<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bv<W>, PropertyError> {
        lhs.add(self, rhs)
    }

    /// Builder-style BV wrapping subtraction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_sub<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bv<W>, PropertyError> {
        lhs.sub(self, rhs)
    }

    /// Builder-style BV wrapping multiplication.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_mul<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bv<W>, PropertyError> {
        lhs.mul(self, rhs)
    }

    /// Builder-style BV bitwise negation.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_not<const W: u32>(&mut self, value: Bv<W>) -> Result<Bv<W>, PropertyError> {
        value.not(self)
    }

    /// Builder-style BV bitwise conjunction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_and<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bv<W>, PropertyError> {
        lhs.and(self, rhs)
    }

    /// Builder-style BV bitwise disjunction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_or<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bv<W>, PropertyError> {
        lhs.or(self, rhs)
    }

    /// Builder-style BV bitwise exclusive-or.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_xor<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bv<W>, PropertyError> {
        lhs.xor(self, rhs)
    }

    /// Builder-style BV equality.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_equals<const W: u32>(
        &mut self,
        lhs: Bv<W>,
        rhs: Bv<W>,
    ) -> Result<Bool, PropertyError> {
        lhs.equals(self, rhs)
    }

    /// Builder-style unsigned BV less-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_ult<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bool, PropertyError> {
        lhs.ult(self, rhs)
    }

    /// Builder-style unsigned BV less-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_ule<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bool, PropertyError> {
        lhs.ule(self, rhs)
    }

    /// Builder-style unsigned BV greater-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_ugt<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bool, PropertyError> {
        lhs.ugt(self, rhs)
    }

    /// Builder-style unsigned BV greater-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_uge<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bool, PropertyError> {
        lhs.uge(self, rhs)
    }

    /// Builder-style signed BV less-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_slt<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bool, PropertyError> {
        lhs.slt(self, rhs)
    }

    /// Builder-style signed BV less-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_sle<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bool, PropertyError> {
        lhs.sle(self, rhs)
    }

    /// Builder-style signed BV greater-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_sgt<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bool, PropertyError> {
        lhs.sgt(self, rhs)
    }

    /// Builder-style signed BV greater-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn bv_sge<const W: u32>(&mut self, lhs: Bv<W>, rhs: Bv<W>) -> Result<Bool, PropertyError> {
        lhs.sge(self, rhs)
    }

    /// Builder-style Int addition.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn int_add(&mut self, lhs: Int, rhs: Int) -> Result<Int, PropertyError> {
        lhs.add(self, rhs)
    }

    /// Builder-style Int subtraction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn int_sub(&mut self, lhs: Int, rhs: Int) -> Result<Int, PropertyError> {
        lhs.sub(self, rhs)
    }

    /// Builder-style Int multiplication.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn int_mul(&mut self, lhs: Int, rhs: Int) -> Result<Int, PropertyError> {
        lhs.mul(self, rhs)
    }

    /// Builder-style Int equality.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn int_equals(&mut self, lhs: Int, rhs: Int) -> Result<Bool, PropertyError> {
        lhs.equals(self, rhs)
    }

    /// Builder-style Int less-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn int_lt(&mut self, lhs: Int, rhs: Int) -> Result<Bool, PropertyError> {
        lhs.lt(self, rhs)
    }

    /// Builder-style Int less-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn int_le(&mut self, lhs: Int, rhs: Int) -> Result<Bool, PropertyError> {
        lhs.le(self, rhs)
    }

    /// Builder-style Int greater-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn int_gt(&mut self, lhs: Int, rhs: Int) -> Result<Bool, PropertyError> {
        lhs.gt(self, rhs)
    }

    /// Builder-style Int greater-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn int_ge(&mut self, lhs: Int, rhs: Int) -> Result<Bool, PropertyError> {
        lhs.ge(self, rhs)
    }

    /// The current hypotheses as raw terms.
    #[must_use]
    pub fn hypotheses(&self) -> &[TermId] {
        &self.hypotheses
    }

    /// Symbols used as lexicographic objectives for minimized counterexamples.
    #[must_use]
    pub fn counterexample_symbols(&self) -> &[SymbolId] {
        &self.counterexample_symbols
    }

    /// Proves `goal` from the current hypotheses.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if evidence production fails or the underlying
    /// solver reports a construction error.
    pub fn prove(&mut self, goal: Bool) -> Result<ProofOutcome, PropertyError> {
        Ok(prove(
            &mut self.arena,
            &self.hypotheses,
            goal.term,
            &self.config,
        )?)
    }

    /// Proves `goal` and attaches a best-effort standalone Lean module.
    ///
    /// The returned [`ProofCertificate::outcome`] is exactly the ordinary
    /// checked Axeyum proof outcome. When that outcome is
    /// [`ProofOutcome::Proved`] and the refutation fragment is covered by Lean
    /// reconstruction, [`ProofCertificate::lean_module`] contains a
    /// self-contained Lean 4 module for `hypotheses ∧ ¬goal ⊢ False`.
    /// Unsupported Lean reconstruction is reported in
    /// [`ProofCertificate::lean_error`] without weakening the underlying
    /// evidence result.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if evidence production fails or the underlying
    /// solver reports a construction error.
    pub fn prove_with_certificate(
        &mut self,
        goal: Bool,
    ) -> Result<ProofCertificate, PropertyError> {
        let refutation_query = self.refutation_query(goal)?;
        let outcome = self.prove(goal)?;
        Ok(self.attach_lean_module(outcome, &refutation_query))
    }

    /// Proves `goal`, minimizing a disproving model over declared SDK inputs.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if evidence production, minimization, or term
    /// construction fails. Unsupported objective sorts are reported by the
    /// underlying solver; this v0 SDK tracks only Bool, BV, and Int symbols.
    pub fn prove_minimized(&mut self, goal: Bool) -> Result<ProofOutcome, PropertyError> {
        let objectives = self.counterexample_objectives();
        Ok(prove_minimized_with_objectives(
            &mut self.arena,
            &self.hypotheses,
            goal.term,
            &objectives,
            &self.config,
        )?)
    }

    /// Proves `goal` with minimized counterexamples and best-effort Lean output.
    ///
    /// This is [`Self::prove_minimized`] plus the same optional Lean-module
    /// packaging as [`Self::prove_with_certificate`]. Lean reconstruction is
    /// attempted only for proved outcomes; disproved outcomes still use the
    /// SDK's signed/unsigned counterexample minimization order.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if evidence production, minimization, or term
    /// construction fails.
    pub fn prove_minimized_with_certificate(
        &mut self,
        goal: Bool,
    ) -> Result<ProofCertificate, PropertyError> {
        let refutation_query = self.refutation_query(goal)?;
        let outcome = self.prove_minimized(goal)?;
        Ok(self.attach_lean_module(outcome, &refutation_query))
    }

    /// Extracts a deterministic counterexample view from a model.
    ///
    /// Only symbols declared through this SDK are included, and they are emitted
    /// in declaration order. Missing symbols are skipped; present values are
    /// checked against the arena declaration before being returned.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::ModelSortMismatch`] if a model value does not
    /// match the symbol's declared sort.
    pub fn counterexample(&self, model: &Model) -> Result<Counterexample, PropertyError> {
        let mut used_idents = Vec::new();
        let mut bindings = Vec::new();
        for &symbol in &self.counterexample_symbols {
            let Some(value) = model.get(symbol) else {
                continue;
            };
            let (name, sort) = self.arena.symbol(symbol);
            if value.sort() != sort {
                return Err(PropertyError::ModelSortMismatch { symbol, value });
            }
            let rust_ident = unique_rust_ident(name, &mut used_idents);
            bindings.push(InputBinding {
                symbol,
                name: name.to_owned(),
                rust_ident,
                sort,
                value,
                bv_literal_style: self.bv_literal_style(symbol),
            });
        }
        Ok(Counterexample::new(bindings))
    }

    /// Extracts a counterexample when `outcome` is disproved.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError::ModelSortMismatch`] if a model value does not
    /// match the symbol's declared sort.
    pub fn counterexample_from_outcome(
        &self,
        outcome: &ProofOutcome,
    ) -> Result<Option<Counterexample>, PropertyError> {
        match outcome {
            ProofOutcome::Disproved(model) => Ok(Some(self.counterexample(model)?)),
            ProofOutcome::Proved(_) | ProofOutcome::Unknown(_) => Ok(None),
        }
    }

    /// Lifts a typed symbolic value from a model through [`Symbolic`].
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if a model value has the wrong sort for its
    /// typed expression handle.
    pub fn concrete<T: Symbolic>(
        &self,
        expr: &T::Expr,
        model: &Model,
    ) -> Result<Option<T::Concrete>, PropertyError> {
        T::concrete(expr, model)
    }

    fn track_symbol(&mut self, symbol: SymbolId) {
        if !self.counterexample_symbols.contains(&symbol) {
            self.counterexample_symbols.push(symbol);
        }
    }

    fn track_bv_symbol(&mut self, symbol: SymbolId, literal_style: BvLiteralStyle) {
        self.track_symbol(symbol);
        if let Some((_, existing)) = self
            .counterexample_bv_literal_styles
            .iter_mut()
            .find(|(existing, _)| *existing == symbol)
        {
            *existing = literal_style;
        } else {
            self.counterexample_bv_literal_styles
                .push((symbol, literal_style));
        }
    }

    fn bv_literal_style(&self, symbol: SymbolId) -> BvLiteralStyle {
        self.counterexample_bv_literal_styles
            .iter()
            .find_map(|(existing, style)| (*existing == symbol).then_some(*style))
            .unwrap_or(BvLiteralStyle::Unsigned)
    }

    fn counterexample_objectives(&self) -> Vec<ModelMinimizeObjective> {
        self.counterexample_symbols
            .iter()
            .copied()
            .map(|symbol| match self.bv_literal_style(symbol) {
                BvLiteralStyle::Unsigned => ModelMinimizeObjective::Symbol(symbol),
                BvLiteralStyle::Signed => ModelMinimizeObjective::SignedBv(symbol),
            })
            .collect()
    }

    fn refutation_query(&mut self, goal: Bool) -> Result<Vec<TermId>, PropertyError> {
        let negated_goal = self.arena.not(goal.term)?;
        let mut query = self.hypotheses.clone();
        query.push(negated_goal);
        Ok(query)
    }

    fn attach_lean_module(
        &mut self,
        outcome: ProofOutcome,
        refutation_query: &[TermId],
    ) -> ProofCertificate {
        if matches!(outcome, ProofOutcome::Proved(_)) {
            match prove_unsat_to_lean_module(&mut self.arena, refutation_query) {
                Ok((fragment, source)) => ProofCertificate {
                    outcome,
                    lean_module: Some(LeanModule { fragment, source }),
                    lean_error: None,
                },
                Err(error) => ProofCertificate {
                    outcome,
                    lean_module: None,
                    lean_error: Some(error),
                },
            }
        } else {
            ProofCertificate {
                outcome,
                lean_module: None,
                lean_error: None,
            }
        }
    }
}

/// Typed Boolean expression handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Bool {
    term: TermId,
    symbol: Option<SymbolId>,
}

impl Bool {
    /// The underlying term.
    #[must_use]
    pub fn term(self) -> TermId {
        self.term
    }

    /// The underlying input symbol, when this handle is a declared variable.
    #[must_use]
    pub fn symbol(self) -> Option<SymbolId> {
        self.symbol
    }

    /// Boolean negation.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn not(self, property: &mut Property) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.not(self.term)?))
    }

    /// Boolean conjunction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn and(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.and(self.term, rhs.term)?))
    }

    /// Boolean disjunction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn or(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.or(self.term, rhs.term)?))
    }

    /// Boolean implication.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn implies(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.implies(self.term, rhs.term)?))
    }

    /// Boolean equality.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn eq(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.eq(self.term, rhs.term)?))
    }

    /// Boolean equality with a name that avoids Rust's trait-method collision.
    ///
    /// This is an alias for [`Self::eq`].
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn equals(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        self.eq(property, rhs)
    }

    /// Reads this Boolean variable from a model.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if a model entry exists but has the wrong sort.
    pub fn value(self, model: &Model) -> Result<Option<bool>, PropertyError> {
        let Some(symbol) = self.symbol else {
            return Ok(None);
        };
        match model.get(symbol) {
            Some(Value::Bool(value)) => Ok(Some(value)),
            Some(value) => Err(PropertyError::ModelSortMismatch { symbol, value }),
            None => Ok(None),
        }
    }

    fn expr(term: TermId) -> Self {
        Self { term, symbol: None }
    }
}

fn render_i128_literal(value: i128) -> String {
    if value == i128::MIN {
        "i128::MIN".to_owned()
    } else {
        format!("{value}_i128")
    }
}

fn render_uint_literal(width: u32, value: u128) -> String {
    let ty = rust_uint_type(width);
    let digits = usize::try_from(width.max(1).div_ceil(4)).expect("width fits usize");
    format!("0x{value:0>digits$x}_{ty}")
}

fn render_signed_bv_literal(width: u32, value: u128) -> String {
    let ty = rust_int_type(width);
    let value = signed_bv_to_i128(width, value);
    if signed_min_literal(ty).is_some_and(|min| min == value) {
        format!("{ty}::MIN")
    } else {
        format!("{value}_{ty}")
    }
}

fn rust_uint_type(width: u32) -> &'static str {
    match width {
        0..=8 => "u8",
        9..=16 => "u16",
        17..=32 => "u32",
        33..=64 => "u64",
        _ => "u128",
    }
}

fn rust_int_type(width: u32) -> &'static str {
    match width {
        0..=8 => "i8",
        9..=16 => "i16",
        17..=32 => "i32",
        33..=64 => "i64",
        _ => "i128",
    }
}

fn signed_min_literal(ty: &str) -> Option<i128> {
    match ty {
        "i8" => Some(i128::from(i8::MIN)),
        "i16" => Some(i128::from(i16::MIN)),
        "i32" => Some(i128::from(i32::MIN)),
        "i64" => Some(i128::from(i64::MIN)),
        "i128" => Some(i128::MIN),
        _ => None,
    }
}

fn signed_bv_to_i128(width: u32, value: u128) -> i128 {
    if width == 0 {
        return 0;
    }
    if width >= 128 {
        return signed_u128_to_i128(value);
    }
    let mask = (1u128 << width) - 1;
    let value = value & mask;
    let sign_bit = 1u128 << (width - 1);
    if value & sign_bit == 0 {
        i128::try_from(value).expect("positive signed BV value fits i128")
    } else {
        let magnitude = ((!value) & mask) + 1;
        -i128::try_from(magnitude).expect("negative signed BV magnitude fits i128")
    }
}

fn signed_u128_to_i128(value: u128) -> i128 {
    if value <= i128::MAX as u128 {
        return i128::try_from(value).expect("value was checked to fit i128");
    }
    let magnitude = (!value).wrapping_add(1);
    if magnitude == (1u128 << 127) {
        i128::MIN
    } else {
        -i128::try_from(magnitude).expect("negative two's-complement magnitude fits i128")
    }
}

fn join_symbolic_name(prefix: &str, field: &str) -> String {
    match (prefix.is_empty(), field.is_empty()) {
        (true, true) => String::new(),
        (true, false) => field.to_owned(),
        (false, true) => prefix.to_owned(),
        (false, false) => format!("{prefix}.{field}"),
    }
}

fn unique_rust_ident(name: &str, used: &mut Vec<String>) -> String {
    let base = sanitize_rust_ident(name);
    if !used.iter().any(|existing| existing == &base) {
        used.push(base.clone());
        return base;
    }
    for i in 1.. {
        let candidate = format!("{base}_{i}");
        if !used.iter().any(|existing| existing == &candidate) {
            used.push(candidate.clone());
            return candidate;
        }
    }
    unreachable!("unbounded suffix search always finds a fresh identifier")
}

fn sanitize_rust_ident(name: &str) -> String {
    let mut out = String::new();
    for (i, ch) in name.chars().enumerate() {
        let ok = ch == '_' || ch.is_ascii_alphanumeric();
        let ch = if ok { ch } else { '_' };
        if i == 0 && !(ch == '_' || ch.is_ascii_alphabetic()) {
            out.push('_');
        }
        out.push(ch);
    }
    if out.is_empty() || out == "_" {
        out.clear();
        out.push_str("input");
    }
    if is_rust_keyword(&out) {
        out.push('_');
    }
    out
}

fn rust_field_ident(field: &str) -> Option<String> {
    if let Some(raw) = field.strip_prefix("r#")
        && is_plain_rust_ident(raw)
        && is_rust_keyword(raw)
    {
        return Some(format!("r#{raw}"));
    }
    if !is_plain_rust_ident(field) {
        return None;
    }
    if is_rust_keyword(field) {
        Some(format!("r#{field}"))
    } else {
        Some(field.to_owned())
    }
}

fn is_plain_rust_ident(ident: &str) -> bool {
    let mut chars = ident.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return false;
    }
    chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn is_rust_keyword(ident: &str) -> bool {
    matches!(
        ident,
        "as" | "break"
            | "const"
            | "continue"
            | "crate"
            | "else"
            | "enum"
            | "extern"
            | "false"
            | "fn"
            | "for"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "loop"
            | "match"
            | "mod"
            | "move"
            | "mut"
            | "pub"
            | "ref"
            | "return"
            | "self"
            | "Self"
            | "static"
            | "struct"
            | "super"
            | "trait"
            | "true"
            | "type"
            | "unsafe"
            | "use"
            | "where"
            | "while"
            | "async"
            | "await"
            | "dyn"
            | "abstract"
            | "become"
            | "box"
            | "do"
            | "final"
            | "macro"
            | "override"
            | "priv"
            | "typeof"
            | "unsized"
            | "virtual"
            | "yield"
            | "try"
    )
}

impl Symbolic for bool {
    type Expr = Bool;
    type Concrete = bool;

    fn symbolic(property: &mut Property, name: &str) -> Result<Self::Expr, PropertyError> {
        property.bool(name)
    }

    fn concrete(expr: &Self::Expr, model: &Model) -> Result<Option<Self::Concrete>, PropertyError> {
        expr.value(model)
    }
}

macro_rules! impl_symbolic_unsigned {
    ($ty:ty, $width:literal) => {
        impl Symbolic for $ty {
            type Expr = Bv<$width>;
            type Concrete = $ty;

            fn symbolic(property: &mut Property, name: &str) -> Result<Self::Expr, PropertyError> {
                property.bv::<$width>(name)
            }

            fn concrete(
                expr: &Self::Expr,
                model: &Model,
            ) -> Result<Option<Self::Concrete>, PropertyError> {
                let Some(value) = expr.value_u128(model)? else {
                    return Ok(None);
                };
                Ok(Some(<$ty>::try_from(value).expect(
                    "model value is masked to the bit-width of the unsigned Rust type",
                )))
            }
        }
    };
}

impl_symbolic_unsigned!(u8, 8);
impl_symbolic_unsigned!(u16, 16);
impl_symbolic_unsigned!(u32, 32);
impl_symbolic_unsigned!(u64, 64);

macro_rules! impl_symbolic_signed_bv {
    ($ty:ty, $width:literal) => {
        impl Symbolic for $ty {
            type Expr = Bv<$width>;
            type Concrete = $ty;

            fn symbolic(property: &mut Property, name: &str) -> Result<Self::Expr, PropertyError> {
                property.signed_bv::<$width>(name)
            }

            fn concrete(
                expr: &Self::Expr,
                model: &Model,
            ) -> Result<Option<Self::Concrete>, PropertyError> {
                let Some(value) = expr.value_u128(model)? else {
                    return Ok(None);
                };
                let signed = signed_bv_to_i128($width, value);
                Ok(Some(<$ty>::try_from(signed).expect(
                    "model value is sign-extended from the matching signed Rust bit-width",
                )))
            }
        }
    };
}

impl_symbolic_signed_bv!(i8, 8);
impl_symbolic_signed_bv!(i16, 16);
impl_symbolic_signed_bv!(i32, 32);
impl_symbolic_signed_bv!(i64, 64);

impl Symbolic for u128 {
    type Expr = Bv<128>;
    type Concrete = u128;

    fn symbolic(property: &mut Property, name: &str) -> Result<Self::Expr, PropertyError> {
        property.bv::<128>(name)
    }

    fn concrete(expr: &Self::Expr, model: &Model) -> Result<Option<Self::Concrete>, PropertyError> {
        expr.value_u128(model)
    }
}

impl Symbolic for i128 {
    type Expr = Int;
    type Concrete = i128;

    fn symbolic(property: &mut Property, name: &str) -> Result<Self::Expr, PropertyError> {
        property.int(name)
    }

    fn concrete(expr: &Self::Expr, model: &Model) -> Result<Option<Self::Concrete>, PropertyError> {
        expr.value(model)
    }
}

impl Symbolic for () {
    type Expr = ();
    type Concrete = ();

    fn symbolic(_property: &mut Property, _name: &str) -> Result<Self::Expr, PropertyError> {
        Ok(())
    }

    fn concrete(
        _expr: &Self::Expr,
        _model: &Model,
    ) -> Result<Option<Self::Concrete>, PropertyError> {
        Ok(Some(()))
    }
}

impl<A, B> Symbolic for (A, B)
where
    A: Symbolic,
    B: Symbolic,
{
    type Expr = (A::Expr, B::Expr);
    type Concrete = (A::Concrete, B::Concrete);

    fn symbolic(property: &mut Property, name: &str) -> Result<Self::Expr, PropertyError> {
        Ok((
            A::symbolic(property, &format!("{name}.0"))?,
            B::symbolic(property, &format!("{name}.1"))?,
        ))
    }

    fn concrete(expr: &Self::Expr, model: &Model) -> Result<Option<Self::Concrete>, PropertyError> {
        let Some(a) = A::concrete(&expr.0, model)? else {
            return Ok(None);
        };
        let Some(b) = B::concrete(&expr.1, model)? else {
            return Ok(None);
        };
        Ok(Some((a, b)))
    }
}

impl<A, B, C> Symbolic for (A, B, C)
where
    A: Symbolic,
    B: Symbolic,
    C: Symbolic,
{
    type Expr = (A::Expr, B::Expr, C::Expr);
    type Concrete = (A::Concrete, B::Concrete, C::Concrete);

    fn symbolic(property: &mut Property, name: &str) -> Result<Self::Expr, PropertyError> {
        Ok((
            A::symbolic(property, &format!("{name}.0"))?,
            B::symbolic(property, &format!("{name}.1"))?,
            C::symbolic(property, &format!("{name}.2"))?,
        ))
    }

    fn concrete(expr: &Self::Expr, model: &Model) -> Result<Option<Self::Concrete>, PropertyError> {
        let Some(a) = A::concrete(&expr.0, model)? else {
            return Ok(None);
        };
        let Some(b) = B::concrete(&expr.1, model)? else {
            return Ok(None);
        };
        let Some(c) = C::concrete(&expr.2, model)? else {
            return Ok(None);
        };
        Ok(Some((a, b, c)))
    }
}

/// Typed bit-vector expression handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Bv<const W: u32> {
    term: TermId,
    symbol: Option<SymbolId>,
}

impl<const W: u32> Bv<W> {
    /// The underlying term.
    #[must_use]
    pub fn term(self) -> TermId {
        self.term
    }

    /// The underlying input symbol, when this handle is a declared variable.
    #[must_use]
    pub fn symbol(self) -> Option<SymbolId> {
        self.symbol
    }

    /// Wrapping addition.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn add(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_add(self.term, rhs.term)?))
    }

    /// Wrapping subtraction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn sub(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_sub(self.term, rhs.term)?))
    }

    /// Wrapping multiplication.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn mul(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_mul(self.term, rhs.term)?))
    }

    /// Bitwise negation.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn not(self, property: &mut Property) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_not(self.term)?))
    }

    /// Bitwise conjunction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn and(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_and(self.term, rhs.term)?))
    }

    /// Bitwise disjunction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn or(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_or(self.term, rhs.term)?))
    }

    /// Bitwise exclusive-or.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn xor(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.bv_xor(self.term, rhs.term)?))
    }

    /// Equality comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn eq(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.eq(self.term, rhs.term)?))
    }

    /// Equality comparison with a name that avoids Rust's trait-method collision.
    ///
    /// This is an alias for [`Self::eq`].
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn equals(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        self.eq(property, rhs)
    }

    /// Unsigned less-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn ult(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_ult(self.term, rhs.term)?))
    }

    /// Unsigned less-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn ule(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_ule(self.term, rhs.term)?))
    }

    /// Unsigned greater-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn ugt(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_ugt(self.term, rhs.term)?))
    }

    /// Unsigned greater-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn uge(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_uge(self.term, rhs.term)?))
    }

    /// Signed less-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn slt(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_slt(self.term, rhs.term)?))
    }

    /// Signed less-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn sle(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_sle(self.term, rhs.term)?))
    }

    /// Signed greater-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn sgt(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_sgt(self.term, rhs.term)?))
    }

    /// Signed greater-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn sge(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_sge(self.term, rhs.term)?))
    }

    /// Unsigned addition overflow predicate.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn uadd_overflows(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_uaddo(self.term, rhs.term)?))
    }

    /// Unsigned subtraction overflow/borrow predicate.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn usub_overflows(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_usubo(self.term, rhs.term)?))
    }

    /// Unsigned multiplication overflow predicate.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn umul_overflows(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.bv_umulo(self.term, rhs.term)?))
    }

    /// Reads this bit-vector variable from a model as an Axeyum value.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if a model entry exists but has the wrong
    /// bit-vector width or sort.
    pub fn value(self, model: &Model) -> Result<Option<Value>, PropertyError> {
        let Some(symbol) = self.symbol else {
            return Ok(None);
        };
        match model.get(symbol) {
            Some(value @ Value::Bv { width, .. }) if width == W => Ok(Some(value)),
            Some(value) if matches!(&value, Value::WideBv(wide) if wide.width() == W) => {
                Ok(Some(value))
            }
            Some(value) => Err(PropertyError::ModelSortMismatch { symbol, value }),
            None => Ok(None),
        }
    }

    /// Reads this bit-vector variable from a model as a `u128` when `W <= 128`.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if a model entry exists but has the wrong sort.
    pub fn value_u128(self, model: &Model) -> Result<Option<u128>, PropertyError> {
        let Some(symbol) = self.symbol else {
            return Ok(None);
        };
        match model.get(symbol) {
            Some(Value::Bv { width, value }) if width == W => Ok(Some(value)),
            Some(value) => Err(PropertyError::ModelSortMismatch { symbol, value }),
            None => Ok(None),
        }
    }

    fn expr(term: TermId) -> Self {
        Self { term, symbol: None }
    }
}

/// Typed integer expression handle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Int {
    term: TermId,
    symbol: Option<SymbolId>,
}

impl Int {
    /// The underlying term.
    #[must_use]
    pub fn term(self) -> TermId {
        self.term
    }

    /// The underlying input symbol, when this handle is a declared variable.
    #[must_use]
    pub fn symbol(self) -> Option<SymbolId> {
        self.symbol
    }

    /// Integer addition.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn add(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.int_add(self.term, rhs.term)?))
    }

    /// Integer subtraction.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn sub(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.int_sub(self.term, rhs.term)?))
    }

    /// Integer multiplication.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn mul(self, property: &mut Property, rhs: Self) -> Result<Self, PropertyError> {
        Ok(Self::expr(property.arena.int_mul(self.term, rhs.term)?))
    }

    /// Equality comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn eq(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.eq(self.term, rhs.term)?))
    }

    /// Equality comparison with a name that avoids Rust's trait-method collision.
    ///
    /// This is an alias for [`Self::eq`].
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn equals(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        self.eq(property, rhs)
    }

    /// Less-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn lt(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.int_lt(self.term, rhs.term)?))
    }

    /// Less-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn le(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.int_le(self.term, rhs.term)?))
    }

    /// Greater-than comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn gt(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.int_gt(self.term, rhs.term)?))
    }

    /// Greater-or-equal comparison.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if term construction fails.
    pub fn ge(self, property: &mut Property, rhs: Self) -> Result<Bool, PropertyError> {
        Ok(Bool::expr(property.arena.int_ge(self.term, rhs.term)?))
    }

    /// Reads this integer variable from a model.
    ///
    /// # Errors
    ///
    /// Returns [`PropertyError`] if a model entry exists but has the wrong sort.
    pub fn value(self, model: &Model) -> Result<Option<i128>, PropertyError> {
        let Some(symbol) = self.symbol else {
            return Ok(None);
        };
        match model.get(symbol) {
            Some(Value::Int(value)) => Ok(Some(value)),
            Some(value) => Err(PropertyError::ModelSortMismatch { symbol, value }),
            None => Ok(None),
        }
    }

    fn expr(term: TermId) -> Self {
        Self { term, symbol: None }
    }
}
