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
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let usage = "usage: check_gf2_tensor <N> <decomposition.json> | matrix <M> <N> <P> <decomposition.json>";
    let parse_dimension = |text: &str, name: &str| {
        text.parse::<usize>()
            .unwrap_or_else(|_| fail(&format!("{name} must be a positive integer"), 2))
    };
    let (family, target, path) = match arguments.as_slice() {
        [n, path] => {
            let n = parse_dimension(n, "full-polynomial N");
            (
                format!("full-polynomial|n={n}"),
                Gf2Tensor::full_polynomial_multiplication(n),
                PathBuf::from(path),
            )
        }
        [kind, m, n, p, path] if kind == "matrix" => {
            let m = parse_dimension(m, "matrix M");
            let n = parse_dimension(n, "matrix N");
            let p = parse_dimension(p, "matrix P");
            (
                format!("matrix|m={m}|n={n}|p={p}"),
                Gf2Tensor::matrix_multiplication(m, n, p),
                PathBuf::from(path),
            )
        }
        _ => fail(usage, 2),
    };
    let bytes = fs::read(&path).unwrap_or_else(|error| fail(&format!("read: {error}"), 2));
    let decomposition: Gf2TensorDecomposition =
        serde_json::from_slice(&bytes).unwrap_or_else(|error| fail(&format!("parse: {error}"), 2));
    let target = target.unwrap_or_else(|error| fail(&format!("target: {error:?}"), 2));
    match check_gf2_tensor_decomposition(&target, &decomposition, Gf2TensorCheckLimits::default()) {
        Ok(Gf2TensorCheck::Verified {
            rank,
            coefficients_checked,
        }) => println!(
            "GF2_TENSOR_CHECK|verified|family={family}|rank={rank}|coefficients={coefficients_checked}"
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
