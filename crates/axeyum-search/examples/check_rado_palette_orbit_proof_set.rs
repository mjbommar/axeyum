//! Independently check one labelled Hamming-ball DRAT proof for every palette
//! permutation of a Rado witness.
//!
//! Completeness comes from Axeyum's bounded lexicographic permutation
//! enumerator, not a producer manifest. A missing or invalid proof fails the
//! command. Acceptance proves the union of all labelled balls, which is exactly
//! the palette-orbit ball.

use std::fs::{self, File};
use std::io::{BufReader, Read};
use std::path::{Path, PathBuf};

use axeyum_cnf::{WeightedAtMostLimits, check_drat_backward_reader};
use axeyum_search::{ColouringFamily, Rado, Witness, palette_permutations};

const MAX_PERMUTATIONS: usize = 40_320;
const MAX_PROOF_BYTES: u64 = 64 * 1024 * 1024 * 1024;
const MAX_TOTAL_PROOF_BYTES: u64 = 1024 * 1024 * 1024 * 1024;

fn fail(message: impl std::fmt::Display) -> ! {
    eprintln!("RADO_PALETTE_ORBIT_PROOF_SET|failed|{message}");
    std::process::exit(2);
}

fn number(text: &str, what: &str) -> usize {
    text.parse()
        .unwrap_or_else(|error| fail(format!("invalid {what}: {error}")))
}

fn proof_path(dir: &Path, permutation: &[usize]) -> PathBuf {
    let name = permutation
        .iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join("-");
    dir.join(format!("perm-{name}.drat"))
}

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() != 8 {
        fail("usage: A B K N WITNESS POINTS MAX_CHANGES PROOF_DIR");
    }
    let a = number(&args[0], "a");
    let b = number(&args[1], "b");
    let colours = number(&args[2], "k");
    let points = number(&args[3], "n");
    let witness_path = Path::new(&args[4]);
    let compared_points = number(&args[5], "compared points");
    let max_changes = args[6]
        .parse::<u64>()
        .unwrap_or_else(|error| fail(format!("invalid maximum changes: {error}")));
    let proof_dir = Path::new(&args[7]);

    let witness_text = fs::read_to_string(witness_path)
        .unwrap_or_else(|error| fail(format!("{}: {error}", witness_path.display())));
    let witness = Witness::parse(colours, &witness_text).unwrap_or_else(|error| fail(error));
    let problem = Rado::new(a, b, colours)
        .and_then(|family| family.problem(points))
        .unwrap_or_else(|error| fail(error));
    let permutations =
        palette_permutations(colours, MAX_PERMUTATIONS).unwrap_or_else(|error| fail(error));
    let mut total_proof_bytes = 0u64;

    for (index, permutation) in permutations.iter().enumerate() {
        let permuted = witness
            .permute_palette(permutation)
            .unwrap_or_else(|error| fail(error));
        let encoding = problem
            .encode_with_witness_hamming_ball(
                &permuted,
                compared_points,
                max_changes,
                WeightedAtMostLimits::default(),
            )
            .unwrap_or_else(|error| fail(error));
        let path = proof_path(proof_dir, permutation);
        let bytes = fs::metadata(&path)
            .unwrap_or_else(|error| fail(format!("{}: {error}", path.display())))
            .len();
        if bytes > MAX_PROOF_BYTES {
            fail(format!(
                "{} has {bytes} bytes above the per-proof limit",
                path.display()
            ));
        }
        total_proof_bytes = total_proof_bytes
            .checked_add(bytes)
            .unwrap_or_else(|| fail("total proof bytes overflow u64"));
        if total_proof_bytes > MAX_TOTAL_PROOF_BYTES {
            fail("proof set exceeds the total byte limit");
        }
        let file =
            File::open(&path).unwrap_or_else(|error| fail(format!("{}: {error}", path.display())));
        let accepted =
            check_drat_backward_reader(encoding.formula(), BufReader::with_capacity(1 << 20, file))
                .unwrap_or_else(|error| fail(format!("{}: {error}", path.display())));
        if !accepted {
            fail(format!(
                "{} does not derive the empty clause",
                path.display()
            ));
        }
        eprintln!(
            "RADO_PALETTE_ORBIT_PROOF_SET_PROGRESS|proofs={}/{}|permutation={}",
            index + 1,
            permutations.len(),
            permutation
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join(",")
        );
    }

    let mut witness_file = File::open(witness_path)
        .unwrap_or_else(|error| fail(format!("{}: {error}", witness_path.display())));
    let mut witness_bytes = Vec::new();
    witness_file
        .read_to_end(&mut witness_bytes)
        .unwrap_or_else(|error| fail(format!("{}: {error}", witness_path.display())));
    println!("schema=axeyum.rado-palette-orbit-proof-set-check.v1");
    println!("a={a}");
    println!("b={b}");
    println!("colours={colours}");
    println!("points={points}");
    println!("compared-points={compared_points}");
    println!("max-changes={max_changes}");
    println!("permutations={}", permutations.len());
    println!("proof-bytes={total_proof_bytes}");
    println!("witness-bytes={}", witness_bytes.len());
    println!("checker=file-backed-backward-drat-per-complete-palette-permutation");
    println!("verdict=orbit-unsat-checked");
}
