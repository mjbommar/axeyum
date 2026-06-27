//! Counterexample → runnable `#[test]` rendering (shared with the EVM and
//! verify apps).
//!
//! When a property check returns a counterexample, the witness
//! is a concrete value (or tuple/struct of values). This module turns that
//! witness into the *source text of a Rust `#[test]`* that re-runs the failing
//! input — so a found counterexample becomes a committed regression test rather
//! than a transient log line.
//!
//! The abstraction is deliberately app-agnostic. A witness only has to describe
//! its concrete inputs as a list of named, typed [`WitnessBinding`]s (via the
//! [`Witness`] trait); the caller supplies the test name and the body that
//! consumes those bindings. So:
//!
//! - the **verify** app (witness = function arguments) renders
//!   `assert!(... original_fn(a, b) panics ...)`; and
//! - the **EVM** app (witness = calldata bytes) renders
//!   `run_contract(&[0x.., ..])` —
//!
//! both through the same [`render_reproduction_test`].
//!
//! ```rust
//! use axeyum_property::{render_reproduction_test, Reproduction, WitnessBinding};
//!
//! // A 2-tuple counterexample (a, b) = (1u8, 255u8) for `a + b >= a`.
//! let bindings = vec![
//!     WitnessBinding::new("a", "u8", "1u8"),
//!     WitnessBinding::new("b", "u8", "255u8"),
//! ];
//! let src = render_reproduction_test(
//!     &Reproduction::new("bv8_add_wraps_repro", bindings)
//!         .body("assert!(a.checked_add(b).is_none(), \"expected wrap at a={a}, b={b}\");"),
//! );
//! assert!(src.contains("#[test]"));
//! assert!(src.contains("fn bv8_add_wraps_repro()"));
//! assert!(src.contains("let a: u8 = 1u8;"));
//! ```

/// One concrete input of a counterexample, rendered as a typed `let` binding.
#[derive(Debug, Clone)]
pub struct WitnessBinding {
    /// The binding name (a valid Rust identifier).
    pub name: String,
    /// The Rust type annotation (e.g. `"u64"`, `"i128"`, `"[u128; 4]"`).
    pub ty: String,
    /// The Rust expression initialising it (e.g. `"255u8"`, `"[1, 2, 3]"`).
    pub value: String,
}

impl WitnessBinding {
    /// A binding `let <name>: <ty> = <value>;`.
    pub fn new(name: impl Into<String>, ty: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            ty: ty.into(),
            value: value.into(),
        }
    }

    /// The rendered `let name: ty = value;` line.
    #[must_use]
    pub fn render(&self) -> String {
        format!("let {}: {} = {};", self.name, self.ty, self.value)
    }
}

/// A concrete counterexample that can describe itself as typed bindings.
///
/// Implement this for an app's witness type (the verify app's argument tuple,
/// the EVM app's calldata) so its counterexamples drop into
/// [`render_reproduction_test`] uniformly. The SDK provides a blanket-style
/// path via [`Reproduction::new`] for callers that already have the bindings.
pub trait Witness {
    /// The named, typed bindings reproducing this witness, in argument order.
    fn bindings(&self) -> Vec<WitnessBinding>;
}

/// A request to render a reproduction `#[test]`: the test name, the witness
/// bindings, and the test body that consumes them.
#[derive(Debug, Clone)]
pub struct Reproduction {
    test_name: String,
    bindings: Vec<WitnessBinding>,
    body: String,
    ignore: bool,
}

impl Reproduction {
    /// A reproduction with the given (snake-case) test name and witness
    /// bindings; the body defaults to a `// TODO` placeholder until set with
    /// [`Reproduction::body`].
    #[must_use]
    pub fn new(test_name: impl Into<String>, bindings: Vec<WitnessBinding>) -> Self {
        Self {
            test_name: test_name.into(),
            bindings,
            body: "// TODO: invoke the property under test on the bindings above".to_string(),
            ignore: false,
        }
    }

    /// Builds a reproduction directly from any [`Witness`].
    #[must_use]
    pub fn from_witness(test_name: impl Into<String>, witness: &impl Witness) -> Self {
        Self::new(test_name, witness.bindings())
    }

    /// Sets the test body (Rust statements that use the binding names).
    #[must_use]
    pub fn body(mut self, body: impl Into<String>) -> Self {
        self.body = body.into();
        self
    }

    /// Marks the rendered test `#[ignore]` (e.g. a slow reproduction).
    #[must_use]
    pub fn ignore(mut self, ignore: bool) -> Self {
        self.ignore = ignore;
        self
    }
}

/// Renders a `Reproduction` into the source text of a self-contained Rust
/// `#[test]` function.
///
/// The output is *source*, not a compiled test — the caller writes it into a
/// generated test file (or a proc-macro emits it). Indentation is fixed and
/// deterministic (stable output is a public promise).
#[must_use]
pub fn render_reproduction_test(repro: &Reproduction) -> String {
    use std::fmt::Write as _;
    let mut out = String::new();
    out.push_str("#[test]\n");
    if repro.ignore {
        out.push_str("#[ignore]\n");
    }
    let _ = writeln!(out, "fn {}() {{", repro.test_name);
    // Witness bindings, one indented `let` per input, in order.
    for b in &repro.bindings {
        out.push_str("    ");
        out.push_str(&b.render());
        out.push('\n');
    }
    if !repro.bindings.is_empty() {
        out.push('\n');
    }
    // Body: re-indent each line by four spaces, preserving blank lines.
    for line in repro.body.lines() {
        if line.is_empty() {
            out.push('\n');
        } else {
            out.push_str("    ");
            out.push_str(line);
            out.push('\n');
        }
    }
    out.push_str("}\n");
    out
}
