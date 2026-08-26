//! Check a portable `GF(2)` tensor-decomposition JSON artifact.

use std::fs;
use std::path::PathBuf;

use axeyum_cas::gf2_tensor::{
    Gf2Tensor, Gf2TensorCheck, Gf2TensorCheckLimits, Gf2TensorDecomposition,
    check_gf2_tensor_decomposition,
};

fn fail(message: &str, code: i32) -> ! {
    eprintln!("GF2_TENSOR_CHECK|failed|{message}");
    std::process::exit(code);
}

fn main() {
    let mut arguments = std::env::args_os();
    let _program = arguments.next();
    let Some(raw_n) = arguments.next() else {
        fail(
            "usage: check_gf2_tensor <full-polynomial-n> <decomposition.json>",
            2,
        );
    };
    let Some(raw_path) = arguments.next() else {
        fail(
            "usage: check_gf2_tensor <full-polynomial-n> <decomposition.json>",
            2,
        );
    };
    if arguments.next().is_some() {
        fail(
            "usage: check_gf2_tensor <full-polynomial-n> <decomposition.json>",
            2,
        );
    }
    let Some(n) = raw_n.to_str().and_then(|value| value.parse::<usize>().ok()) else {
        fail("full-polynomial-n must be a positive integer", 2);
    };
    let path = PathBuf::from(raw_path);
    let bytes = fs::read(&path).unwrap_or_else(|error| fail(&format!("read: {error}"), 2));
    let decomposition: Gf2TensorDecomposition =
        serde_json::from_slice(&bytes).unwrap_or_else(|error| fail(&format!("parse: {error}"), 2));
    let target = Gf2Tensor::full_polynomial_multiplication(n)
        .unwrap_or_else(|error| fail(&format!("target: {error:?}"), 2));
    match check_gf2_tensor_decomposition(&target, &decomposition, Gf2TensorCheckLimits::default()) {
        Ok(Gf2TensorCheck::Verified {
            rank,
            coefficients_checked,
        }) => println!(
            "GF2_TENSOR_CHECK|verified|family=full-polynomial|n={n}|rank={rank}|coefficients={coefficients_checked}"
        ),
        Ok(Gf2TensorCheck::Failed {
            coordinate,
            expected,
            observed,
        }) => fail(
            &format!("coordinate={coordinate:?}|expected={expected}|observed={observed}"),
            1,
        ),
        Err(error) => fail(&format!("malformed-or-declined={error:?}"), 2),
    }
}
