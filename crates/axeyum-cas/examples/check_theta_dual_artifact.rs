//! Strict external front door for an exact Lovasz-theta clique dual.

use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;

use axeyum_cas::sos::psd_big::BigPsd;
use axeyum_cas::sos::psd_big::BigPsdLimits;
use axeyum_cas::sos::theta::{
    ThetaCliqueDualArtifactV1, ThetaDualCheck, check_theta_clique_dual, parse_simple_edge_list,
    theta_dual_from_artifact,
};
use sha2::{Digest, Sha256};

fn fail(message: &str, code: i32) -> ! {
    eprintln!("THETA_DUAL_CHECK|failed|{message}");
    std::process::exit(code);
}

fn hash(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(encoded, "{byte:02x}").expect("writing to String cannot fail");
    }
    encoded
}

const MAX_INPUT_BYTES: u64 = 512 * 1024 * 1024;

fn read_bounded(path: &PathBuf, label: &str) -> Vec<u8> {
    let metadata =
        fs::metadata(path).unwrap_or_else(|error| fail(&format!("{label} metadata: {error}"), 2));
    if metadata.len() > MAX_INPUT_BYTES {
        fail(
            &format!(
                "{label} bytes {} exceed limit {MAX_INPUT_BYTES}",
                metadata.len()
            ),
            2,
        );
    }
    fs::read(path).unwrap_or_else(|error| fail(&format!("{label} read: {error}"), 2))
}

fn main() {
    let mut arguments = std::env::args_os();
    let _program = arguments.next();
    let Some(graph_path) = arguments.next() else {
        fail("usage: check_theta_dual_artifact GRAPH.txt DUAL.json", 2);
    };
    let Some(dual_path) = arguments.next() else {
        fail("usage: check_theta_dual_artifact GRAPH.txt DUAL.json", 2);
    };
    if arguments.next().is_some() {
        fail("usage: check_theta_dual_artifact GRAPH.txt DUAL.json", 2);
    }
    let graph_path = PathBuf::from(graph_path);
    let dual_path = PathBuf::from(dual_path);
    let graph_bytes = read_bounded(&graph_path, "graph");
    let graph_text = std::str::from_utf8(&graph_bytes)
        .unwrap_or_else(|error| fail(&format!("graph UTF-8: {error}"), 2));
    let adjacency = parse_simple_edge_list(graph_text)
        .unwrap_or_else(|error| fail(&format!("graph parse: {error}"), 2));
    let dual_bytes = read_bounded(&dual_path, "dual");
    let artifact: ThetaCliqueDualArtifactV1 = serde_json::from_slice(&dual_bytes)
        .unwrap_or_else(|error| fail(&format!("dual JSON: {error}"), 2));
    let certificate = theta_dual_from_artifact(&artifact)
        .unwrap_or_else(|error| fail(&format!("dual artifact: {error}"), 2));
    match check_theta_clique_dual(&adjacency, &certificate, BigPsdLimits::default()) {
        ThetaDualCheck::Verified {
            slack:
                BigPsd::Yes {
                    pivots,
                    zero_pivots,
                    max_intermediate_bits,
                },
        } => println!(
            "THETA_DUAL_CHECK|verified|order={}|edges={}|multipliers={}|bound={}/{}|graph_sha256={}|dual_sha256={}|positive_pivots={}|zero_pivots={zero_pivots}|max_intermediate_bits={max_intermediate_bits}",
            adjacency.len(),
            adjacency
                .iter()
                .map(|row| row.iter().filter(|&&edge| edge).count())
                .sum::<usize>()
                / 2,
            certificate.nonedge_multipliers.len(),
            certificate.bound.numer(),
            certificate.bound.denom(),
            hash(&graph_bytes),
            hash(&dual_bytes),
            pivots.len(),
        ),
        ThetaDualCheck::Verified { .. } => unreachable!("verified theta slack is PSD"),
        ThetaDualCheck::Rejected(reason) => fail(&format!("rejected={reason}"), 1),
        ThetaDualCheck::Declined(reason) => fail(&format!("declined={reason:?}"), 2),
    }
}
