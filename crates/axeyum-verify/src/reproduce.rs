//! Soundness-floor helpers: confirm a reported counterexample actually makes the
//! *original* Rust function panic/overflow.
//!
//! No external tool is involved (Kani is not installed in this environment): the
//! independent ground truth is the original function itself, run on the witness
//! inputs. The macro-generated reproduction test calls the original fn inside
//! [`panics_on`]; a witness that does not panic is a lowering defect to fix, not
//! a finding to report (DISAGREE = 0).

use std::panic::{AssertUnwindSafe, catch_unwind};

use axeyum_property::{Reproduction, WitnessBinding, render_reproduction_test};

use crate::verify::{Witness, signed_value};

/// Runs `f` (a closure that calls the original function on the witness inputs)
/// and returns `true` iff it panics. Panic output is suppressed for clean test
/// logs.
///
/// Used by the macro-generated reproduction `#[test]`: it asserts
/// `panics_on(|| original(witness...))` so a non-reproducing counterexample
/// fails the build.
#[must_use]
pub fn panics_on<F: FnOnce()>(f: F) -> bool {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = catch_unwind(AssertUnwindSafe(f));
    std::panic::set_hook(prev);
    result.is_err()
}

/// Renders one verify [`Witness`] as a typed [`WitnessBinding`] for the shared
/// [`render_reproduction_test`] layer: a `name: ty = value` line whose value is
/// a Rust literal of the witness's type (`uN`/`iN` for scalars, `[T; N]` for
/// arrays). Used by [`render_counterexample_test`] so a found counterexample can
/// be written out as a committed regression `#[test]` — the same format the
/// `axeyum-property` SDK (App B) and EVM app (App A) use.
#[must_use]
pub(crate) fn witness_binding(w: &Witness) -> WitnessBinding {
    match w {
        Witness::Bool { name, value } => {
            WitnessBinding::new(name.clone(), "bool", value.to_string())
        }
        Witness::Int {
            name,
            width,
            signed,
            bits,
        } => {
            let ty = format!("{}{}", if *signed { "i" } else { "u" }, width);
            let value = format!("{}{ty}", Witness::render_int(*width, *signed, *bits));
            WitnessBinding::new(name.clone(), ty, value)
        }
        Witness::Array {
            name,
            width,
            signed,
            ints,
        } => {
            let elem_ty = format!("{}{}", if *signed { "i" } else { "u" }, width);
            let ty = format!("[{elem_ty}; {}]", ints.len());
            let elems: Vec<String> = ints
                .iter()
                .map(|&bits| {
                    if *signed {
                        format!("{}{elem_ty}", signed_value(*width, bits))
                    } else {
                        format!("{bits}{elem_ty}")
                    }
                })
                .collect();
            let value = format!("[{}]", elems.join(", "));
            WitnessBinding::new(name.clone(), ty, value)
        }
    }
}

/// Renders a found counterexample as the **source text** of a self-contained
/// regression `#[test]`, via the shared [`render_reproduction_test`] layer.
///
/// The bindings are the witness inputs in declaration order; the body asserts the
/// original function `fn_name(<args>)` panics (the bug). `call_args` is the
/// comma-separated argument list (typically the witness names in order, with `&`
/// added for reference params) — the caller knows the fn's exact signature.
///
/// The output is *source* (not a compiled test); write it into a generated test
/// file to turn a transient finding into a committed regression. This aligns
/// App C's counterexample rendering with App B's `Reproduction` format.
#[must_use]
pub fn render_counterexample_test(
    test_name: &str,
    fn_name: &str,
    call_args: &str,
    class: &str,
    inputs: &[Witness],
) -> String {
    let bindings: Vec<WitnessBinding> = inputs.iter().map(witness_binding).collect();
    let body = format!(
        "// class: {class} — the original function panics on this input.\n\
         let reproduces = std::panic::catch_unwind(|| {{\n\
         \x20   let _ = {fn_name}({call_args});\n\
         }})\n\
         .is_err();\n\
         assert!(reproduces, \"expected `{fn_name}` to panic ({class})\");"
    );
    let repro = Reproduction::new(test_name, bindings).body(body);
    render_reproduction_test(&repro)
}
