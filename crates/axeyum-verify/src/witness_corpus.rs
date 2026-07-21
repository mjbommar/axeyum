//! Deterministic replay-checked solver-witness corpora (Track 5, T5.4.2).
//!
//! A solver countermodel is useful fuzz input only after the owning frontend
//! replays it against the original semantics. This module enforces that order:
//! constructors invoke a caller-supplied replay check before creating a
//! [`WitnessSeed`], and a [`WitnessSeedCorpus`] then emits byte-stable JSON and
//! Rust regression tests through the existing reproduction renderers.
//!
//! The module returns bytes; it never writes files or invokes tools. A caller
//! can review and commit those bytes explicitly.
//!
//! ```
//! use axeyum_verify::witness_corpus::{ReplayRecipe, WitnessSeed, WitnessSeedCorpus};
//! use axeyum_verify::{Verdict, Witness};
//!
//! let verdict = Verdict::Counterexample {
//!     class: "add overflow".into(),
//!     inputs: vec![Witness::Int {
//!         name: "x".into(),
//!         width: 8,
//!         signed: false,
//!         bits: 255,
//!     }],
//! };
//! let recipe = ReplayRecipe::panic_call("overflowing_inc", ["x"]);
//! let seed = WitnessSeed::from_verdict("overflowing_inc_repro", &verdict, recipe, |inputs| {
//!     matches!(inputs, [Witness::Int { bits: 255, .. }])
//! })?;
//! let mut corpus = WitnessSeedCorpus::new("integer_regressions")?;
//! corpus.add(seed)?;
//! assert!(corpus.render_json()?.contains("\"replay_checked\":true"));
//! assert!(corpus.render_tests()?.contains("fn overflowing_inc_repro()"));
//! # Ok::<(), axeyum_verify::witness_corpus::WitnessSeedError>(())
//! ```

use core::fmt;
use std::fmt::Write as _;

use axeyum_property::{Reproduction, render_reproduction_test};

use crate::reproduce::{render_counterexample_test, witness_binding};
use crate::{Verdict, Witness};

/// The canonical v1 corpus schema.
pub const WITNESS_SEED_CORPUS_SCHEMA: &str = "axeyum.verify.witness-seed-corpus.v1";

/// How a generated regression test replays one checked witness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReplayRecipe {
    /// Call a function with the carried inputs and require that it panics.
    ///
    /// The function is a Rust path. Each argument must be exactly an input
    /// name or `&name`, in declaration order; arbitrary model text cannot enter
    /// generated source.
    PanicCall {
        /// Rust function path to call.
        function: String,
        /// Declaration-ordered argument references.
        arguments: Vec<String>,
    },
    /// Use an explicit caller-owned Rust assertion body.
    ///
    /// This is for normally returning contract violations and equivalence
    /// refutations. The body is source supplied by the integration author, not
    /// derived from a solver model or diagnostic string.
    RustBody {
        /// Rust statements that consume the generated witness bindings.
        body: String,
    },
}

impl ReplayRecipe {
    /// Builds a constrained panic-call recipe.
    pub fn panic_call<I, S>(function: impl Into<String>, arguments: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self::PanicCall {
            function: function.into(),
            arguments: arguments.into_iter().map(Into::into).collect(),
        }
    }

    /// Builds a caller-owned assertion-body recipe.
    #[must_use]
    pub fn rust_body(body: impl Into<String>) -> Self {
        Self::RustBody { body: body.into() }
    }

    fn kind(&self) -> &'static str {
        match self {
            Self::PanicCall { .. } => "panic_call",
            Self::RustBody { .. } => "rust_body",
        }
    }
}

/// A precise failure while validating or rendering witness-corpus input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WitnessSeedError {
    /// A named field violates its stable syntax or value contract.
    InvalidField {
        /// Field name.
        field: &'static str,
        /// Observed value.
        value: String,
        /// Required contract.
        detail: &'static str,
    },
    /// One typed witness cannot be represented by the v1 native-Rust corpus.
    UnsupportedWitness {
        /// Input name.
        name: String,
        /// Precise reason.
        detail: String,
    },
    /// A verdict without a counterexample was offered as a witness seed.
    NotCounterexample {
        /// Actual verdict class.
        outcome: &'static str,
    },
    /// The owning frontend's replay callback rejected the counterexample.
    ReplayFailed {
        /// Stable seed ID.
        id: String,
    },
    /// A corpus already contains the same stable seed ID.
    DuplicateSeed {
        /// Duplicate ID.
        id: String,
    },
    /// Rendering was requested before any replay-checked seed was added.
    EmptyCorpus {
        /// Stable suite ID.
        suite: String,
    },
}

impl fmt::Display for WitnessSeedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidField {
                field,
                value,
                detail,
            } => write!(f, "invalid witness-corpus {field} `{value}`: {detail}"),
            Self::UnsupportedWitness { name, detail } => {
                write!(f, "unsupported witness input `{name}`: {detail}")
            }
            Self::NotCounterexample { outcome } => {
                write!(f, "cannot create a witness seed from verdict `{outcome}`")
            }
            Self::ReplayFailed { id } => {
                write!(f, "witness seed `{id}` failed original-semantics replay")
            }
            Self::DuplicateSeed { id } => {
                write!(f, "witness corpus already contains seed `{id}`")
            }
            Self::EmptyCorpus { suite } => {
                write!(f, "witness corpus `{suite}` has no replay-checked seeds")
            }
        }
    }
}

impl std::error::Error for WitnessSeedError {}

/// One typed counterexample admitted only after original-semantics replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WitnessSeed {
    id: String,
    class: String,
    inputs: Vec<Witness>,
    recipe: ReplayRecipe,
}

impl WitnessSeed {
    /// Creates a seed from a verifier verdict, accepting only a replayed
    /// [`Verdict::Counterexample`].
    ///
    /// `replay` is invoked exactly once after structural validation. Returning
    /// `false` rejects the seed before any artifact bytes exist.
    ///
    /// # Errors
    ///
    /// Returns a typed error when the verdict is not a counterexample, a
    /// corpus field or witness is invalid, or original-semantics replay fails.
    pub fn from_verdict<F>(
        id: impl Into<String>,
        verdict: &Verdict,
        recipe: ReplayRecipe,
        replay: F,
    ) -> Result<Self, WitnessSeedError>
    where
        F: FnOnce(&[Witness]) -> bool,
    {
        match verdict {
            Verdict::Counterexample { class, inputs } => {
                Self::from_counterexample(id, class.clone(), inputs.clone(), recipe, replay)
            }
            Verdict::Verified { .. } => Err(WitnessSeedError::NotCounterexample {
                outcome: "verified",
            }),
            Verdict::Unknown { .. } => {
                Err(WitnessSeedError::NotCounterexample { outcome: "unknown" })
            }
        }
    }

    /// Creates a seed from a lifted raw/reflection countermodel after replay.
    ///
    /// The caller must lift model values into the existing [`Witness`] type and
    /// replay them against the owning semantics in `replay`.
    ///
    /// # Errors
    ///
    /// Returns a typed error when a corpus field or witness is invalid, or
    /// when original-semantics replay fails.
    pub fn from_counterexample<F>(
        id: impl Into<String>,
        class: impl Into<String>,
        inputs: Vec<Witness>,
        recipe: ReplayRecipe,
        replay: F,
    ) -> Result<Self, WitnessSeedError>
    where
        F: FnOnce(&[Witness]) -> bool,
    {
        let id = id.into();
        let class = class.into();
        validate_stable_id("seed_id", &id)?;
        validate_class(&class)?;
        validate_inputs(&inputs)?;
        validate_recipe(&recipe, &inputs)?;
        if !replay(&inputs) {
            return Err(WitnessSeedError::ReplayFailed { id });
        }
        Ok(Self {
            id,
            class,
            inputs,
            recipe,
        })
    }

    /// Stable lexical seed ID and generated Rust test name.
    #[must_use]
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Counterexample class supplied by the owning verifier.
    #[must_use]
    pub fn class(&self) -> &str {
        &self.class
    }

    /// Declaration-ordered typed witness inputs.
    #[must_use]
    pub fn inputs(&self) -> &[Witness] {
        &self.inputs
    }

    /// Stable replay recipe kind (`panic_call` or `rust_body`).
    #[must_use]
    pub fn replay_kind(&self) -> &'static str {
        self.recipe.kind()
    }

    /// Renders this seed as one deterministic Rust regression test.
    #[must_use]
    pub fn render_test(&self) -> String {
        match &self.recipe {
            ReplayRecipe::PanicCall {
                function,
                arguments,
            } => render_counterexample_test(
                &self.id,
                function,
                &arguments.join(", "),
                &self.class,
                &self.inputs,
            ),
            ReplayRecipe::RustBody { body } => {
                let bindings = self.inputs.iter().map(witness_binding).collect();
                render_reproduction_test(&Reproduction::new(&self.id, bindings).body(body))
            }
        }
    }
}

/// A lexically ordered collection of replay-checked witness seeds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WitnessSeedCorpus {
    suite: String,
    seeds: Vec<WitnessSeed>,
}

impl WitnessSeedCorpus {
    /// Creates an empty corpus builder with a stable suite ID.
    ///
    /// Rendering remains fail-closed until at least one seed is added.
    ///
    /// # Errors
    ///
    /// Returns [`WitnessSeedError::InvalidField`] when `suite` is not a stable
    /// lowercase identifier.
    pub fn new(suite: impl Into<String>) -> Result<Self, WitnessSeedError> {
        let suite = suite.into();
        validate_stable_id("suite", &suite)?;
        Ok(Self {
            suite,
            seeds: Vec::new(),
        })
    }

    /// Adds a seed in lexical ID order, rejecting duplicate IDs.
    ///
    /// # Errors
    ///
    /// Returns [`WitnessSeedError::DuplicateSeed`] when the corpus already
    /// contains the seed ID.
    pub fn add(&mut self, seed: WitnessSeed) -> Result<(), WitnessSeedError> {
        match self
            .seeds
            .binary_search_by(|existing| existing.id.cmp(&seed.id))
        {
            Ok(_) => Err(WitnessSeedError::DuplicateSeed {
                id: seed.id.clone(),
            }),
            Err(index) => {
                self.seeds.insert(index, seed);
                Ok(())
            }
        }
    }

    /// Stable suite ID.
    #[must_use]
    pub fn suite(&self) -> &str {
        &self.suite
    }

    /// Replay-checked seeds in lexical ID order.
    #[must_use]
    pub fn seeds(&self) -> &[WitnessSeed] {
        &self.seeds
    }

    /// Number of replay-checked seeds.
    #[must_use]
    pub fn len(&self) -> usize {
        self.seeds.len()
    }

    /// Whether no replay-checked seed has been added yet.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.seeds.is_empty()
    }

    /// Renders all regression tests in lexical seed order.
    ///
    /// # Errors
    ///
    /// Returns [`WitnessSeedError::EmptyCorpus`] when no checked seed exists.
    pub fn render_tests(&self) -> Result<String, WitnessSeedError> {
        self.require_nonempty()?;
        let mut output = String::new();
        for (index, seed) in self.seeds.iter().enumerate() {
            if index != 0 {
                output.push('\n');
            }
            output.push_str(&seed.render_test());
        }
        Ok(output)
    }

    /// Renders canonical compact JSON in lexical seed order.
    ///
    /// Integer values are emitted as Rust-literal strings, preserving all 128
    /// bits for consumers that cannot losslessly parse JSON integers.
    ///
    /// # Errors
    ///
    /// Returns [`WitnessSeedError::EmptyCorpus`] when no checked seed exists.
    pub fn render_json(&self) -> Result<String, WitnessSeedError> {
        self.require_nonempty()?;
        let mut output = String::new();
        write!(
            output,
            "{{\"schema\":{},\"suite\":{},\"seeds\":[",
            json_quote(WITNESS_SEED_CORPUS_SCHEMA),
            json_quote(&self.suite)
        )
        .expect("writing to String");
        for (seed_index, seed) in self.seeds.iter().enumerate() {
            if seed_index != 0 {
                output.push(',');
            }
            write!(
                output,
                "{{\"id\":{},\"class\":{},\"replay_kind\":{},\"replay_checked\":true,\"inputs\":[",
                json_quote(&seed.id),
                json_quote(&seed.class),
                json_quote(seed.recipe.kind())
            )
            .expect("writing to String");
            for (input_index, witness) in seed.inputs.iter().enumerate() {
                if input_index != 0 {
                    output.push(',');
                }
                let binding = witness_binding(witness);
                write!(
                    output,
                    "{{\"name\":{},\"rust_type\":{},\"rust_value\":{}}}",
                    json_quote(&binding.name),
                    json_quote(&binding.ty),
                    json_quote(&binding.value)
                )
                .expect("writing to String");
            }
            write!(
                output,
                "],\"test_source\":{}}}",
                json_quote(&seed.render_test())
            )
            .expect("writing to String");
        }
        output.push_str("]}\n");
        Ok(output)
    }

    fn require_nonempty(&self) -> Result<(), WitnessSeedError> {
        if self.seeds.is_empty() {
            Err(WitnessSeedError::EmptyCorpus {
                suite: self.suite.clone(),
            })
        } else {
            Ok(())
        }
    }
}

fn validate_stable_id(field: &'static str, value: &str) -> Result<(), WitnessSeedError> {
    let mut chars = value.chars();
    let valid_first = chars.next().is_some_and(|c| c.is_ascii_lowercase());
    if !valid_first || !chars.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_') {
        return Err(WitnessSeedError::InvalidField {
            field,
            value: value.to_owned(),
            detail: "expected [a-z][a-z0-9_]*",
        });
    }
    Ok(())
}

fn validate_class(value: &str) -> Result<(), WitnessSeedError> {
    if value.is_empty()
        || !value.chars().all(|c| {
            c.is_ascii_alphanumeric()
                || matches!(c, ' ' | '_' | '-' | '+' | '/' | ':' | '.' | '(' | ')')
        })
    {
        return Err(WitnessSeedError::InvalidField {
            field: "class",
            value: value.to_owned(),
            detail: "expected a nonempty printable diagnostic label without source delimiters",
        });
    }
    Ok(())
}

fn validate_inputs(inputs: &[Witness]) -> Result<(), WitnessSeedError> {
    if inputs.is_empty() {
        return Err(WitnessSeedError::InvalidField {
            field: "inputs",
            value: "0".into(),
            detail: "expected at least one typed input",
        });
    }
    let mut names = Vec::with_capacity(inputs.len());
    for witness in inputs {
        let name = witness_name(witness);
        validate_rust_identifier("input_name", name)?;
        if names.iter().any(|existing| existing == &name) {
            return Err(WitnessSeedError::InvalidField {
                field: "input_name",
                value: name.to_owned(),
                detail: "duplicate input name",
            });
        }
        names.push(name);
        match witness {
            Witness::Bool { .. } => {}
            Witness::Int {
                width, bits, name, ..
            } => validate_integer_value(name, *width, *bits)?,
            Witness::Array {
                width, ints, name, ..
            } => {
                validate_native_width(name, *width)?;
                for (index, &bits) in ints.iter().enumerate() {
                    if !fits_width(*width, bits) {
                        return Err(WitnessSeedError::UnsupportedWitness {
                            name: name.clone(),
                            detail: format!(
                                "array element {index} value {bits} exceeds declared width {width}"
                            ),
                        });
                    }
                }
            }
        }
    }
    Ok(())
}

fn validate_integer_value(name: &str, width: u32, bits: u128) -> Result<(), WitnessSeedError> {
    validate_native_width(name, width)?;
    if !fits_width(width, bits) {
        return Err(WitnessSeedError::UnsupportedWitness {
            name: name.to_owned(),
            detail: format!("value {bits} exceeds declared width {width}"),
        });
    }
    Ok(())
}

fn validate_native_width(name: &str, width: u32) -> Result<(), WitnessSeedError> {
    if !matches!(width, 8 | 16 | 32 | 64 | 128) {
        return Err(WitnessSeedError::UnsupportedWitness {
            name: name.to_owned(),
            detail: format!("width {width} has no native Rust integer type in corpus v1"),
        });
    }
    Ok(())
}

fn fits_width(width: u32, bits: u128) -> bool {
    width == 128 || bits < (1_u128 << width)
}

fn witness_name(witness: &Witness) -> &str {
    match witness {
        Witness::Int { name, .. } | Witness::Bool { name, .. } | Witness::Array { name, .. } => {
            name
        }
    }
}

fn validate_recipe(recipe: &ReplayRecipe, inputs: &[Witness]) -> Result<(), WitnessSeedError> {
    match recipe {
        ReplayRecipe::PanicCall {
            function,
            arguments,
        } => {
            validate_rust_path(function)?;
            if arguments.len() != inputs.len() {
                return Err(WitnessSeedError::InvalidField {
                    field: "panic_arguments",
                    value: arguments.len().to_string(),
                    detail: "argument count must equal carried input count",
                });
            }
            for (index, (argument, witness)) in arguments.iter().zip(inputs).enumerate() {
                let bare = argument.strip_prefix('&').unwrap_or(argument);
                if bare != witness_name(witness)
                    || (!argument.starts_with('&') && argument.contains('&'))
                {
                    return Err(WitnessSeedError::InvalidField {
                        field: "panic_argument",
                        value: argument.clone(),
                        detail: "expected the declaration-ordered input name or &name",
                    });
                }
                if argument.starts_with("&&") || bare.is_empty() {
                    return Err(WitnessSeedError::InvalidField {
                        field: "panic_argument",
                        value: argument.clone(),
                        detail: "expected the declaration-ordered input name or &name",
                    });
                }
                debug_assert_eq!(bare, witness_name(&inputs[index]));
            }
        }
        ReplayRecipe::RustBody { body } => {
            if body.trim().is_empty() {
                return Err(WitnessSeedError::InvalidField {
                    field: "rust_body",
                    value: body.clone(),
                    detail: "caller-owned assertion body must be nonempty",
                });
            }
            if body.contains('\0') {
                return Err(WitnessSeedError::InvalidField {
                    field: "rust_body",
                    value: body.clone(),
                    detail: "Rust source cannot contain NUL",
                });
            }
        }
    }
    Ok(())
}

fn validate_rust_path(path: &str) -> Result<(), WitnessSeedError> {
    let valid = !path.is_empty()
        && path.split("::").all(|segment| {
            matches!(segment, "crate" | "self" | "super") || is_rust_identifier(segment)
        });
    if !valid {
        return Err(WitnessSeedError::InvalidField {
            field: "panic_function",
            value: path.to_owned(),
            detail: "expected a Rust path of identifier segments",
        });
    }
    Ok(())
}

fn validate_rust_identifier(field: &'static str, value: &str) -> Result<(), WitnessSeedError> {
    if !is_rust_identifier(value) {
        return Err(WitnessSeedError::InvalidField {
            field,
            value: value.to_owned(),
            detail: "expected a non-keyword ASCII Rust identifier",
        });
    }
    Ok(())
}

fn is_rust_identifier(value: &str) -> bool {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
        && !is_rust_keyword(value)
}

fn is_rust_keyword(value: &str) -> bool {
    matches!(
        value,
        "Self"
            | "abstract"
            | "as"
            | "async"
            | "await"
            | "become"
            | "box"
            | "break"
            | "const"
            | "continue"
            | "crate"
            | "do"
            | "dyn"
            | "else"
            | "enum"
            | "extern"
            | "false"
            | "final"
            | "fn"
            | "for"
            | "gen"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "loop"
            | "macro"
            | "match"
            | "mod"
            | "move"
            | "mut"
            | "override"
            | "priv"
            | "pub"
            | "ref"
            | "return"
            | "self"
            | "static"
            | "struct"
            | "super"
            | "trait"
            | "true"
            | "try"
            | "type"
            | "typeof"
            | "union"
            | "unsafe"
            | "unsized"
            | "use"
            | "virtual"
            | "where"
            | "while"
            | "yield"
    )
}

fn json_quote(value: &str) -> String {
    let mut output = String::with_capacity(value.len() + 2);
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\u{08}' => output.push_str("\\b"),
            '\u{0c}' => output.push_str("\\f"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character <= '\u{1f}' => {
                write!(output, "\\u{:04x}", u32::from(character)).expect("writing to String");
            }
            character => output.push(character),
        }
    }
    output.push('"');
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(name: &str, width: u32, signed: bool, bits: u128) -> Witness {
        Witness::Int {
            name: name.into(),
            width,
            signed,
            bits,
        }
    }

    #[test]
    fn corpus_orders_ids_and_escapes_caller_body() {
        let z = WitnessSeed::from_counterexample(
            "z_seed",
            "equivalence mismatch",
            vec![int("x", 8, false, 1)],
            ReplayRecipe::rust_body("assert!(true);\n// quote \" slash \\ tab\t\u{1}"),
            |_| true,
        )
        .unwrap();
        let a = WitnessSeed::from_counterexample(
            "a_seed",
            "add overflow",
            vec![int("x", 8, false, 255)],
            ReplayRecipe::panic_call("crate::overflow", ["x"]),
            |_| true,
        )
        .unwrap();
        let mut corpus = WitnessSeedCorpus::new("ordered_suite").unwrap();
        corpus.add(z).unwrap();
        corpus.add(a).unwrap();
        assert_eq!(
            corpus
                .seeds()
                .iter()
                .map(WitnessSeed::id)
                .collect::<Vec<_>>(),
            ["a_seed", "z_seed"]
        );
        let json = corpus.render_json().unwrap();
        assert!(json.starts_with(
            "{\"schema\":\"axeyum.verify.witness-seed-corpus.v1\",\"suite\":\"ordered_suite\",\"seeds\":[{\"id\":\"a_seed\""
        ));
        assert!(json.contains("quote \\\" slash \\\\ tab\\t\\u0001"));
        assert!(json.ends_with("]}\n"));
    }

    #[test]
    fn verdict_and_replay_failures_are_typed() {
        let recipe = ReplayRecipe::panic_call("overflow", ["x"]);
        let verified = Verdict::Verified {
            certified: true,
            lean_module: None,
        };
        assert_eq!(
            WitnessSeed::from_verdict("verified_seed", &verified, recipe.clone(), |_| true),
            Err(WitnessSeedError::NotCounterexample {
                outcome: "verified"
            })
        );
        let unknown = Verdict::Unknown {
            reason: "timeout".into(),
        };
        assert_eq!(
            WitnessSeed::from_verdict("unknown_seed", &unknown, recipe.clone(), |_| true),
            Err(WitnessSeedError::NotCounterexample { outcome: "unknown" })
        );
        let verdict = Verdict::Counterexample {
            class: "add overflow".into(),
            inputs: vec![int("x", 8, false, 255)],
        };
        assert_eq!(
            WitnessSeed::from_verdict("failed_seed", &verdict, recipe, |_| false),
            Err(WitnessSeedError::ReplayFailed {
                id: "failed_seed".into()
            })
        );
    }

    #[test]
    fn malformed_artifact_inputs_fail_precisely() {
        let recipe = ReplayRecipe::panic_call("overflow", ["x"]);
        let invalid_id = WitnessSeed::from_counterexample(
            "Bad-ID",
            "add overflow",
            vec![int("x", 8, false, 255)],
            recipe.clone(),
            |_| true,
        )
        .unwrap_err();
        assert_eq!(
            invalid_id.to_string(),
            "invalid witness-corpus seed_id `Bad-ID`: expected [a-z][a-z0-9_]*"
        );

        let unsupported_width = WitnessSeed::from_counterexample(
            "bad_width",
            "add overflow",
            vec![int("x", 7, false, 127)],
            recipe.clone(),
            |_| true,
        )
        .unwrap_err();
        assert_eq!(
            unsupported_width.to_string(),
            "unsupported witness input `x`: width 7 has no native Rust integer type in corpus v1"
        );

        let bad_argument = WitnessSeed::from_counterexample(
            "bad_argument",
            "add overflow",
            vec![int("x", 8, false, 255)],
            ReplayRecipe::panic_call("overflow", ["x + 1"]),
            |_| true,
        )
        .unwrap_err();
        assert_eq!(
            bad_argument.to_string(),
            "invalid witness-corpus panic_argument `x + 1`: expected the declaration-ordered input name or &name"
        );

        let bad_class = WitnessSeed::from_counterexample(
            "bad_class",
            "bad\"; panic!()",
            vec![int("x", 8, false, 255)],
            recipe,
            |_| true,
        )
        .unwrap_err();
        assert!(matches!(
            bad_class,
            WitnessSeedError::InvalidField { field: "class", .. }
        ));
    }

    #[test]
    fn duplicate_and_empty_corpora_fail_closed() {
        let seed = WitnessSeed::from_counterexample(
            "one_seed",
            "add overflow",
            vec![int("x", 8, false, 255)],
            ReplayRecipe::panic_call("overflow", ["x"]),
            |_| true,
        )
        .unwrap();
        let mut corpus = WitnessSeedCorpus::new("suite").unwrap();
        assert_eq!(
            corpus.render_json(),
            Err(WitnessSeedError::EmptyCorpus {
                suite: "suite".into()
            })
        );
        corpus.add(seed.clone()).unwrap();
        assert_eq!(
            corpus.add(seed),
            Err(WitnessSeedError::DuplicateSeed {
                id: "one_seed".into()
            })
        );
    }
}
