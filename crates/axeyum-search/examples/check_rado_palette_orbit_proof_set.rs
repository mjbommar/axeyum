//! Independently check one labelled Hamming-ball DRAT proof for every palette
//! permutation of a Rado witness.
//!
//! Completeness comes from Axeyum's bounded lexicographic permutation
//! enumerator, not a producer manifest. A missing or invalid proof fails the
//! command. Acceptance proves the union of all labelled balls, which is exactly
//! the palette-orbit ball.

use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc;

use axeyum_cnf::{
    WeightedAtMostLimits, check_drat_backward_reader, open_drat_reader, resolve_drat_or_gzip_path,
};
use axeyum_search::{ColouringFamily, ColouringProblem, Rado, Witness, palette_permutations};

const MAX_PERMUTATIONS: usize = 40_320;
const MAX_PROOF_BYTES: u64 = 64 * 1024 * 1024 * 1024;
const MAX_TOTAL_PROOF_BYTES: u64 = 1024 * 1024 * 1024 * 1024;
const MAX_WORKERS: usize = 64;

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

fn worker_count(arg: Option<&str>) -> Result<usize, String> {
    let Some(arg) = arg else {
        return Ok(1);
    };
    let Some(value) = arg.strip_prefix("--workers=") else {
        return Err(format!(
            "unexpected ninth argument {arg:?}; expected --workers=N"
        ));
    };
    let workers = value
        .parse::<usize>()
        .map_err(|error| format!("invalid worker count: {error}"))?;
    if !(1..=MAX_WORKERS).contains(&workers) {
        return Err(format!("worker count must be in 1..={MAX_WORKERS}"));
    }
    Ok(workers)
}

fn check_proof(
    problem: &ColouringProblem,
    witness: &Witness,
    permutation: &[usize],
    compared_points: usize,
    max_changes: u64,
    proof_dir: &Path,
) -> Result<u64, String> {
    let requested_path = proof_path(proof_dir, permutation);
    let path = resolve_drat_or_gzip_path(&requested_path)
        .map_err(|error| format!("{}: {error}", requested_path.display()))?;
    let permuted = witness
        .permute_palette(permutation)
        .map_err(|error| error.to_string())?;
    let encoding = problem
        .encode_with_witness_hamming_ball(
            &permuted,
            compared_points,
            max_changes,
            WeightedAtMostLimits::default(),
        )
        .map_err(|error| error.to_string())?;
    let bytes = fs::metadata(&path)
        .map_err(|error| format!("{}: {error}", path.display()))?
        .len();
    if bytes > MAX_PROOF_BYTES {
        return Err(format!(
            "{} has {bytes} bytes above the per-proof limit",
            path.display()
        ));
    }
    let reader = open_drat_reader(&path, 1 << 20, MAX_PROOF_BYTES)
        .map_err(|error| format!("{}: {error}", path.display()))?;
    let accepted = check_drat_backward_reader(encoding.formula(), reader)
        .map_err(|error| format!("{}: {error}", path.display()))?;
    if !accepted {
        return Err(format!(
            "{} does not derive the empty clause",
            path.display()
        ));
    }
    Ok(bytes)
}

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if !(8..=9).contains(&args.len()) {
        fail("usage: A B K N WITNESS POINTS MAX_CHANGES PROOF_DIR [--workers=N]");
    }
    let workers = worker_count(args.get(8).map(String::as_str)).unwrap_or_else(|error| fail(error));
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
    let next = AtomicUsize::new(0);
    let (sender, receiver) = mpsc::channel();
    let mut ordered = BTreeMap::new();
    let mut next_report = 0usize;
    let mut total_proof_bytes = 0u64;

    std::thread::scope(|scope| {
        for _ in 0..workers.min(permutations.len()) {
            let sender = sender.clone();
            let next = &next;
            let permutations = &permutations;
            let problem = &problem;
            let witness = &witness;
            scope.spawn(move || {
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(permutation) = permutations.get(index) else {
                        break;
                    };
                    let checked = check_proof(
                        problem,
                        witness,
                        permutation,
                        compared_points,
                        max_changes,
                        proof_dir,
                    );
                    if sender.send((index, checked)).is_err() {
                        break;
                    }
                }
            });
        }
        drop(sender);
        for (index, checked) in receiver {
            ordered.insert(index, checked);
            while let Some(checked) = ordered.remove(&next_report) {
                let bytes = checked.unwrap_or_else(|error| fail(error));
                total_proof_bytes = total_proof_bytes
                    .checked_add(bytes)
                    .unwrap_or_else(|| fail("total proof bytes overflow u64"));
                if total_proof_bytes > MAX_TOTAL_PROOF_BYTES {
                    fail("proof set exceeds the total byte limit");
                }
                let permutation = &permutations[next_report];
                eprintln!(
                    "RADO_PALETTE_ORBIT_PROOF_SET_PROGRESS|proofs={}/{}|permutation={}",
                    next_report + 1,
                    permutations.len(),
                    permutation
                        .iter()
                        .map(usize::to_string)
                        .collect::<Vec<_>>()
                        .join(",")
                );
                next_report += 1;
            }
        }
    });

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
    println!("workers={workers}");
    println!("verdict=orbit-unsat-checked");
}

#[cfg(test)]
mod tests {
    use super::worker_count;

    #[test]
    fn worker_count_is_bounded_and_backwards_compatible() {
        assert_eq!(worker_count(None), Ok(1));
        assert_eq!(worker_count(Some("--workers=4")), Ok(4));
        assert!(worker_count(Some("--workers=0")).is_err());
        assert!(worker_count(Some("--workers=65")).is_err());
        assert!(worker_count(Some("workers=4")).is_err());
    }
}
