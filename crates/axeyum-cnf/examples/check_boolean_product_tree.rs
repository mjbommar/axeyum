//! Check a recursively subdivided Boolean-product cube refutation.

use std::fs::File;
use std::io::BufReader;
use std::path::{Path, PathBuf};

use axeyum_cnf::cube::{
    CubeRefutationReaderTree, augmented_formula, boolean_product_cubes,
    check_cube_refutation_reader_tree,
};
use axeyum_cnf::{CnfFormula, CnfVar, parse_dimacs};

const MAX_TREE_DEPTH: usize = 16;
// The current reader tree owns one open file per proof. Keep the cap below the
// common 1,024-descriptor soft limit, including manifests and process overhead.
const MAX_TREE_NODES: usize = 512;
const MAX_PROOF_BYTES: u64 = 64 * 1024 * 1024 * 1024;

#[derive(Default)]
struct Stats {
    splits: usize,
    leaves: usize,
    nodes: usize,
}

fn fail(message: impl std::fmt::Display) -> ! {
    eprintln!("BOOLEAN_PRODUCT_TREE_CHECK|failed|{message}");
    std::process::exit(2);
}

fn parse_usize(text: &str, what: &str) -> usize {
    text.parse::<usize>()
        .unwrap_or_else(|error| fail(format!("invalid {what}: {error}")))
}

fn proof_reader(path: &Path) -> BufReader<File> {
    let metadata = std::fs::metadata(path)
        .unwrap_or_else(|error| fail(format!("{} metadata: {error}", path.display())));
    if metadata.len() > MAX_PROOF_BYTES {
        fail(format!(
            "{} has {} bytes, above limit {MAX_PROOF_BYTES}",
            path.display(),
            metadata.len()
        ));
    }
    BufReader::new(
        File::open(path).unwrap_or_else(|error| fail(format!("{}: {error}", path.display()))),
    )
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
) -> CubeRefutationReaderTree<BufReader<File>> {
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
            )));
        }
    }
    CubeRefutationReaderTree::Split {
        cubes,
        children,
        covering_proof: proof_reader(&dir.join("covering.drat")),
    }
}

fn main() {
    let mut args = std::env::args_os().skip(1);
    let base_path = PathBuf::from(
        args.next()
            .unwrap_or_else(|| fail("usage: BASE.cnf TREE-DIR [PREFIX-INDEX PREFIX-SELECTOR...]")),
    );
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
    check_cube_refutation_reader_tree(&root, tree).unwrap_or_else(|error| fail(error));
    println!("schema=axeyum.cnf-boolean-product-tree-check.v1");
    println!("base={}", base_path.display());
    println!("root-clauses={}", root.clauses().len());
    println!("splits={}", stats.splits);
    println!("leaves={}", stats.leaves);
    println!("nodes={}", stats.nodes);
    println!("checker=file-backed-recursive-backward-plus-covering-drat");
    println!("verdict=unsat-checked");
}
