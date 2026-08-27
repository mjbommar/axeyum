//! Check a recursively subdivided Boolean-product cube refutation.

use std::fs::File;
use std::io::{self, BufRead, BufReader, Read};
use std::path::{Path, PathBuf};

use axeyum_cnf::cube::{
    CubeRefutationReaderTree, augmented_formula, boolean_product_cubes,
    check_cube_refutation_reader_tree,
};
#[cfg(not(target_arch = "wasm32"))]
use axeyum_cnf::cube::{
    CubeTreeObligationEvent, CubeTreeObligationKind, CubeTreeObligationState,
    check_cube_refutation_reader_tree_fully_parallel_with_events,
};
use axeyum_cnf::{CnfFormula, CnfVar, parse_dimacs};

const MAX_TREE_DEPTH: usize = 16;
const MAX_TREE_NODES: usize = 65_536;
const MAX_PROOF_BYTES: u64 = 64 * 1024 * 1024 * 1024;
const MAX_TREE_PROOF_BYTES: u64 = 1024 * 1024 * 1024 * 1024;

#[derive(Default)]
struct Stats {
    splits: usize,
    leaves: usize,
    nodes: usize,
    proof_bytes: u64,
}

struct LazyProofReader {
    path: PathBuf,
    reader: Option<BufReader<File>>,
}

impl LazyProofReader {
    fn reader(&mut self) -> io::Result<&mut BufReader<File>> {
        if self.reader.is_none() {
            self.reader = Some(BufReader::new(File::open(&self.path)?));
        }
        Ok(self.reader.as_mut().expect("reader was initialized"))
    }
}

impl Read for LazyProofReader {
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        self.reader()?.read(buffer)
    }
}

impl BufRead for LazyProofReader {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        self.reader()?.fill_buf()
    }

    fn consume(&mut self, amount: usize) {
        self.reader
            .as_mut()
            .expect("consume follows a successful fill_buf")
            .consume(amount);
    }
}

fn fail(message: impl std::fmt::Display) -> ! {
    eprintln!("BOOLEAN_PRODUCT_TREE_CHECK|failed|{message}");
    std::process::exit(2);
}

#[cfg(not(target_arch = "wasm32"))]
fn report_obligation_event(event: &CubeTreeObligationEvent) {
    let kind = match event.kind {
        CubeTreeObligationKind::Leaf => "leaf",
        CubeTreeObligationKind::Covering => "covering",
        CubeTreeObligationKind::Structural => "structural",
    };
    let outcome = match event.state {
        CubeTreeObligationState::Started => "started",
        CubeTreeObligationState::Finished { accepted: true } => "accepted",
        CubeTreeObligationState::Finished { accepted: false } => "rejected",
    };
    let path = event
        .path
        .iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(".");
    eprintln!(
        "BOOLEAN_PRODUCT_TREE_EVENT|obligation={}/{}|path={path}|kind={kind}|state={outcome}",
        event.index + 1,
        event.total,
    );
}

fn parse_usize(text: &str, what: &str) -> usize {
    text.parse::<usize>()
        .unwrap_or_else(|error| fail(format!("invalid {what}: {error}")))
}

fn proof_reader(path: &Path, stats: &mut Stats) -> LazyProofReader {
    let metadata = std::fs::metadata(path)
        .unwrap_or_else(|error| fail(format!("{} metadata: {error}", path.display())));
    if metadata.len() > MAX_PROOF_BYTES {
        fail(format!(
            "{} has {} bytes, above limit {MAX_PROOF_BYTES}",
            path.display(),
            metadata.len()
        ));
    }
    stats.proof_bytes = stats
        .proof_bytes
        .checked_add(metadata.len())
        .unwrap_or_else(|| fail("tree proof-byte total overflows u64"));
    if stats.proof_bytes > MAX_TREE_PROOF_BYTES {
        fail(format!(
            "tree proof bytes {} exceed limit {MAX_TREE_PROOF_BYTES}",
            stats.proof_bytes
        ));
    }
    LazyProofReader {
        path: path.to_owned(),
        reader: None,
    }
}

fn manifest_cubes(dir: &Path, formula: &CnfFormula) -> Vec<Vec<axeyum_cnf::CnfLit>> {
    let path = dir.join("manifest.txt");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| fail(format!("{}: {error}", path.display())));
    let mut lines = text.lines();
    if lines.next() != Some("schema=axeyum.cnf-boolean-product-cover.v1") {
        fail(format!("{} has wrong schema", path.display()));
    }
    let Some(base_line) = lines.next() else {
        fail(format!("{} lacks base", path.display()));
    };
    if !base_line.starts_with("base=") || base_line == "base=" {
        fail(format!("{} has malformed base", path.display()));
    }
    let variables = lines
        .next()
        .and_then(|line| line.strip_prefix("variables="))
        .map_or_else(
            || fail(format!("{} lacks variables", path.display())),
            |value| parse_usize(value, "manifest variable count"),
        );
    let clauses = lines
        .next()
        .and_then(|line| line.strip_prefix("clauses="))
        .map_or_else(
            || fail(format!("{} lacks clauses", path.display())),
            |value| parse_usize(value, "manifest clause count"),
        );
    if variables != formula.variable_count() || clauses != formula.clauses().len() {
        fail(format!(
            "{} describes {variables} variables/{clauses} clauses, reconstructed node has {}/{}",
            path.display(),
            formula.variable_count(),
            formula.clauses().len()
        ));
    }
    let selector_text = lines
        .next()
        .and_then(|line| line.strip_prefix("selectors="))
        .unwrap_or_else(|| fail(format!("{} lacks selectors", path.display())));
    let selectors: Vec<CnfVar> = selector_text
        .split(',')
        .map(|value| {
            let number = parse_usize(value, "manifest selector");
            if number == 0 || number > formula.variable_count() {
                fail(format!("selector {number} is out of range"));
            }
            CnfVar::new(number - 1).unwrap_or_else(|error| fail(error))
        })
        .collect();
    let cubes = boolean_product_cubes(&selectors).unwrap_or_else(|error| fail(error));
    let declared = lines
        .next()
        .and_then(|line| line.strip_prefix("cubes="))
        .map_or_else(
            || fail(format!("{} lacks cube count", path.display())),
            |value| parse_usize(value, "manifest cube count"),
        );
    if declared != cubes.len() {
        fail(format!(
            "{} declares {declared} cubes, selectors generate {}",
            path.display(),
            cubes.len()
        ));
    }
    for (index, cube) in cubes.iter().enumerate() {
        let expected = format!(
            "cube={index}\tliterals={}\tformula=cube-{index:06}.cnf",
            cube.iter()
                .map(|literal| literal.dimacs().to_string())
                .collect::<Vec<_>>()
                .join(",")
        );
        if lines.next() != Some(expected.as_str()) {
            fail(format!("{} has malformed cube row {index}", path.display()));
        }
    }
    if lines.next().is_some() {
        fail(format!("{} has trailing rows", path.display()));
    }
    cubes
}

fn build_tree(
    formula: &CnfFormula,
    dir: &Path,
    depth: usize,
    stats: &mut Stats,
) -> CubeRefutationReaderTree<LazyProofReader> {
    if depth >= MAX_TREE_DEPTH {
        fail(format!("tree depth reaches limit {MAX_TREE_DEPTH}"));
    }
    stats.splits += 1;
    stats.nodes += 1;
    if stats.nodes > MAX_TREE_NODES {
        fail(format!("tree nodes exceed limit {MAX_TREE_NODES}"));
    }
    let cubes = manifest_cubes(dir, formula);
    let mut children = Vec::with_capacity(cubes.len());
    for (index, cube) in cubes.iter().enumerate() {
        let child_formula = augmented_formula(formula, cube).unwrap_or_else(|error| fail(error));
        let subtree = dir.join(format!("cube-{index:06}-subcover-v1"));
        if subtree.is_dir() {
            children.push(build_tree(&child_formula, &subtree, depth + 1, stats));
        } else {
            stats.leaves += 1;
            stats.nodes += 1;
            if stats.nodes > MAX_TREE_NODES {
                fail(format!("tree nodes exceed limit {MAX_TREE_NODES}"));
            }
            children.push(CubeRefutationReaderTree::Leaf(proof_reader(
                &dir.join(format!("cube-{index:06}.drat")),
                stats,
            )));
        }
    }
    CubeRefutationReaderTree::Split {
        cubes,
        children,
        covering_proof: proof_reader(&dir.join("covering.drat"), stats),
    }
}

fn main() {
    let mut args = std::env::args_os().skip(1);
    let first = args.next().unwrap_or_else(|| {
        fail("usage: [--workers=N] BASE.cnf TREE-DIR [PREFIX-INDEX PREFIX-SELECTOR...]")
    });
    let first_text = first.to_string_lossy();
    let (workers, base_path) = if let Some(value) = first_text.strip_prefix("--workers=") {
        let workers = parse_usize(value, "worker count");
        if workers == 0 {
            fail("worker count must be positive");
        }
        let base = args.next().unwrap_or_else(|| {
            fail("usage: [--workers=N] BASE.cnf TREE-DIR [PREFIX-INDEX PREFIX-SELECTOR...]")
        });
        (workers, PathBuf::from(base))
    } else {
        (1, PathBuf::from(first))
    };
    #[cfg(target_arch = "wasm32")]
    if workers != 1 {
        fail("parallel cube-tree checking is unavailable on wasm32");
    }
    let tree_dir = PathBuf::from(
        args.next()
            .unwrap_or_else(|| fail("usage: BASE.cnf TREE-DIR [PREFIX-INDEX PREFIX-SELECTOR...]")),
    );
    let base = parse_dimacs(
        &std::fs::read_to_string(&base_path)
            .unwrap_or_else(|error| fail(format!("{}: {error}", base_path.display()))),
    )
    .unwrap_or_else(|error| fail(error));
    let remaining: Vec<_> = args.collect();
    let root = if remaining.is_empty() {
        base
    } else {
        if remaining.len() < 2 {
            fail("a prefix index requires at least one prefix selector");
        }
        let index = parse_usize(&remaining[0].to_string_lossy(), "prefix index");
        let selectors: Vec<CnfVar> = remaining[1..]
            .iter()
            .map(|value| {
                let number = parse_usize(&value.to_string_lossy(), "prefix selector");
                if number == 0 || number > base.variable_count() {
                    fail(format!("prefix selector {number} is out of range"));
                }
                CnfVar::new(number - 1).unwrap_or_else(|error| fail(error))
            })
            .collect();
        let cubes = boolean_product_cubes(&selectors).unwrap_or_else(|error| fail(error));
        let cube = cubes
            .get(index)
            .unwrap_or_else(|| fail(format!("prefix index {index} is out of range")));
        augmented_formula(&base, cube).unwrap_or_else(|error| fail(error))
    };
    let mut stats = Stats::default();
    let tree = build_tree(&root, &tree_dir, 0, &mut stats);
    #[cfg(not(target_arch = "wasm32"))]
    if workers > 1 {
        check_cube_refutation_reader_tree_fully_parallel_with_events(
            &root,
            tree,
            workers,
            |completed, total| {
                eprintln!("BOOLEAN_PRODUCT_TREE_PROGRESS|obligations={completed}/{total}");
            },
            |event| report_obligation_event(&event),
        )
        .unwrap_or_else(|error| fail(error));
    } else {
        check_cube_refutation_reader_tree(&root, tree).unwrap_or_else(|error| fail(error));
    }
    #[cfg(target_arch = "wasm32")]
    check_cube_refutation_reader_tree(&root, tree).unwrap_or_else(|error| fail(error));
    println!("schema=axeyum.cnf-boolean-product-tree-check.v1");
    println!("base={}", base_path.display());
    println!("root-clauses={}", root.clauses().len());
    println!("splits={}", stats.splits);
    println!("leaves={}", stats.leaves);
    println!("nodes={}", stats.nodes);
    println!("proof-bytes={}", stats.proof_bytes);
    println!("workers={workers}");
    println!("checker=file-backed-whole-tree-parallel-backward-plus-covering-drat");
    println!("verdict=unsat-checked");
}
