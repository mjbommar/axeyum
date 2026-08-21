//! `axeyum-render` -- the Doc-IR command line.
//!
//! Three subcommands and no argument-parsing dependency, because the surface is
//! three subcommands:
//!
//! ```text
//! axeyum-render render   --manifest M --format md|tex|html [--out DIR] [--strict]
//! axeyum-render render   --manifest-dir D --format html --out DIR   (batch)
//! axeyum-render validate --manifest M [--strict]
//! axeyum-render hash     FILE...
//! ```
//!
//! Exit status: `0` success, `1` the build refused (any fail-closed rule), `2`
//! bad usage. Nothing here exits 0 on completion alone -- `render` exits 0 only
//! when every reference resolved, every declared input re-hashed to its recorded
//! digest, and every claim carried evidence.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use axeyum_render::assemble::{AssembleOptions, Assembler, hex_digest};
use axeyum_render::emitter_for;

const USAGE: &str = "\
axeyum-render -- render Doc-IR documents that cannot lie

USAGE:
  axeyum-render render   --manifest <file> --format <md|tex|html> [options]
  axeyum-render validate --manifest <file> [options]
  axeyum-render hash     <file>...

OPTIONS:
  --manifest <file>    the Doc-IR document to assemble
  --manifest-dir <dir> assemble every `*.doc.json` in <dir>, in sorted order
  --name-by <rule>     output file naming: `doc-id` (default for --manifest)
                       or `source` (default for --manifest-dir)
  --format <name>      md | tex | html
  --out <dir>          write outputs here (default: primary to stdout)
  --repo-root <dir>    root that input paths resolve against (default: .)
  --facts-dir <dir>    the fact ledger (default: <repo-root>/artifacts/facts)
  --strict             red evidence is a build error, not a demoted claim
  --fail-on-diagnostics  refuse the build if the emitter could not draw a block

EXIT STATUS:
  0  rendered; every reference resolved and every input hash matched
  1  the build refused (fail-closed)
  2  bad usage
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(Fail::Usage(msg)) => {
            eprintln!("axeyum-render: {msg}\n\n{USAGE}");
            ExitCode::from(2)
        }
        Err(Fail::Build(msg)) => {
            eprintln!("axeyum-render: BUILD REFUSED: {msg}");
            ExitCode::from(1)
        }
    }
}

enum Fail {
    Usage(String),
    Build(String),
}

struct Args {
    manifest: Option<PathBuf>,
    manifest_dir: Option<PathBuf>,
    name_by: Option<String>,
    format: Option<String>,
    out: Option<PathBuf>,
    repo_root: PathBuf,
    facts_dir: Option<PathBuf>,
    strict: bool,
    fail_on_diagnostics: bool,
    rest: Vec<String>,
}

fn parse(args: &[String]) -> Result<Args, Fail> {
    let mut a = Args {
        manifest: None,
        manifest_dir: None,
        name_by: None,
        format: None,
        out: None,
        repo_root: PathBuf::from("."),
        facts_dir: None,
        strict: false,
        fail_on_diagnostics: false,
        rest: Vec::new(),
    };
    let mut i = 0;
    while i < args.len() {
        let arg = args[i].as_str();
        match arg {
            "--manifest" => a.manifest = Some(PathBuf::from(value(args, &mut i, arg)?)),
            "--manifest-dir" => a.manifest_dir = Some(PathBuf::from(value(args, &mut i, arg)?)),
            "--name-by" => a.name_by = Some(value(args, &mut i, arg)?),
            "--format" => a.format = Some(value(args, &mut i, arg)?),
            "--out" => a.out = Some(PathBuf::from(value(args, &mut i, arg)?)),
            "--repo-root" => a.repo_root = PathBuf::from(value(args, &mut i, arg)?),
            "--facts-dir" => a.facts_dir = Some(PathBuf::from(value(args, &mut i, arg)?)),
            "--strict" => a.strict = true,
            "--fail-on-diagnostics" => a.fail_on_diagnostics = true,
            "-h" | "--help" => return Err(Fail::Usage("help".to_string())),
            other if other.starts_with("--") => {
                return Err(Fail::Usage(format!("unknown option {other}")));
            }
            other => a.rest.push(other.to_string()),
        }
        i += 1;
    }
    Ok(a)
}

/// Consume the value that follows a flag, advancing the cursor.
fn value(args: &[String], i: &mut usize, name: &str) -> Result<String, Fail> {
    *i += 1;
    args.get(*i)
        .cloned()
        .ok_or_else(|| Fail::Usage(format!("{name} needs a value")))
}

fn run(args: &[String]) -> Result<(), Fail> {
    let Some(sub) = args.first() else {
        return Err(Fail::Usage("no subcommand".to_string()));
    };
    let parsed = parse(&args[1..])?;
    match sub.as_str() {
        "render" => cmd_render(&parsed),
        "validate" => cmd_validate(&parsed),
        "hash" => cmd_hash(&parsed),
        other => Err(Fail::Usage(format!("unknown subcommand `{other}`"))),
    }
}

fn options_for(a: &Args, manifest: &Path) -> AssembleOptions {
    let manifest_dir = manifest.parent().unwrap_or(Path::new(".")).to_path_buf();
    let mut opts = AssembleOptions::new(a.repo_root.clone(), manifest_dir);
    if let Some(f) = &a.facts_dir {
        opts.facts_dir.clone_from(f);
    }
    opts.strict = a.strict;
    opts
}

/// How an output file is named.
///
/// THIS IS LOAD-BEARING, not a convenience. Doc-IR carries a reference to
/// another document as the relative path of that document's SOURCE
/// (`cards/F-nat-add-comm.doc.json`), and every emitter resolves it to the same
/// path with the extension swapped. So a corpus whose cross-references resolve
/// is a corpus named after its sources -- `F-nat-add-comm.html`, not
/// `fact-nat-add-comm.html`, which is what `doc_id` would give.
///
/// `doc-id` remains the default for a single `--manifest`, because that is what
/// P0's deliverables and their golden tests are named after, and changing it
/// silently would rename files under a build script that renames them again.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NameBy {
    DocId,
    Source,
}

impl NameBy {
    fn parse(v: &str) -> Result<Self, Fail> {
        match v {
            "doc-id" | "docid" => Ok(Self::DocId),
            "source" | "file" => Ok(Self::Source),
            other => Err(Fail::Usage(format!(
                "--name-by `{other}` (expected `doc-id` or `source`)"
            ))),
        }
    }
}

/// The stem an output file gets, given the rule and the manifest it came from.
fn out_stem(rule: NameBy, manifest: &Path, doc_id: &str) -> String {
    match rule {
        NameBy::DocId => doc_id.to_string(),
        NameBy::Source => manifest.file_name().and_then(|f| f.to_str()).map_or_else(
            || doc_id.to_string(),
            |f| f.strip_suffix(".doc.json").unwrap_or(f).to_string(),
        ),
    }
}

fn cmd_render(a: &Args) -> Result<(), Fail> {
    if let Some(dir) = &a.manifest_dir {
        return cmd_render_batch(a, dir);
    }
    let manifest = a
        .manifest
        .as_ref()
        .ok_or_else(|| Fail::Usage("render needs --manifest or --manifest-dir".to_string()))?;
    let format = a
        .format
        .as_deref()
        .ok_or_else(|| Fail::Usage("render needs --format".to_string()))?;

    // The `html` emitter is DESIGN's and is not wired in round 1. Say so
    // explicitly: silently falling back to another format would hand a caller
    // bytes that are not what they asked for.
    let Some(emitter) = emitter_for(format) else {
        if format == "html" {
            return Err(Fail::Usage(
                "format `html` is not wired in this build. The HTML emitter \
                 (render/src/emit_html.rs) lands in round 2 behind the `html` \
                 cargo feature; build with `--features html` once it exists. \
                 Refusing rather than falling back to another format."
                    .to_string(),
            ));
        }
        return Err(Fail::Usage(format!(
            "unknown format `{format}` (md | tex | html)"
        )));
    };

    let mut assembler = Assembler::new(options_for(a, manifest));
    let doc = assembler
        .assemble_path(manifest)
        .map_err(|e| Fail::Build(e.to_string()))?;
    let out = emitter.emit(&doc);

    // Contract point 2: an emitter reports what it could not draw. The bytes
    // exist either way and the page says so in a loud box; this turns that
    // report into an exit status for a gate that asked for one. Printed
    // ALWAYS, so a human running the command sees it even without the flag --
    // a diagnostic nobody is shown is the silent-drop failure wearing a
    // different hat.
    let diagnostics = emitter.diagnostics(&doc);
    for d in &diagnostics {
        eprintln!("axeyum-render: DIAGNOSTIC: {d}");
    }
    if a.fail_on_diagnostics && !diagnostics.is_empty() {
        return Err(Fail::Build(format!(
            "the {} emitter could not draw {} block(s); the rendered document says so in \
             an `unrenderable` box. Refusing because --fail-on-diagnostics was given.",
            emitter.format_name(),
            diagnostics.len()
        )));
    }

    match &a.out {
        None => print!("{}", out.primary),
        Some(dir) => {
            std::fs::create_dir_all(dir)
                .map_err(|e| Fail::Build(format!("cannot create {}: {e}", dir.display())))?;
            let rule = match a.name_by.as_deref() {
                Some(v) => NameBy::parse(v)?,
                None => NameBy::DocId,
            };
            let primary = dir.join(format!(
                "{}.{}",
                out_stem(rule, manifest, &doc.doc_id),
                emitter.primary_extension()
            ));
            write(&primary, &out.primary)?;
            eprintln!("wrote {}", primary.display());
            for (name, contents) in &out.aux {
                let p = dir.join(name);
                write(&p, contents)?;
                eprintln!("wrote {}", p.display());
            }
        }
    }
    Ok(())
}

/// Render every `*.doc.json` in one directory, in sorted order, in one process.
///
/// Why a batch mode exists at all: the fact corpus is 324 cards, and rendering
/// them one process at a time spends more time starting processes than
/// assembling documents. Everything else is IDENTICAL to the single-manifest
/// path -- the same assembler, the same fail-closed rules, the same diagnostics
/// -- and each document gets its OWN `Assembler`, so nothing is cached across
/// documents and no card can be rendered from bytes another card verified.
/// Batch is a loop, not a shortcut; a card that would be refused alone is
/// refused here.
///
/// The whole run is refused if ANY document is, and the refusals are reported
/// together rather than one per invocation, because a caller fixing a corpus
/// wants the list.
fn cmd_render_batch(a: &Args, dir: &Path) -> Result<(), Fail> {
    let format = a
        .format
        .as_deref()
        .ok_or_else(|| Fail::Usage("render needs --format".to_string()))?;
    let Some(emitter) = emitter_for(format) else {
        return Err(Fail::Usage(format!(
            "unknown or unwired format `{format}` (md | tex | html)"
        )));
    };
    let out = a
        .out
        .as_ref()
        .ok_or_else(|| Fail::Usage("--manifest-dir needs --out".to_string()))?;
    let rule = match a.name_by.as_deref() {
        Some(v) => NameBy::parse(v)?,
        None => NameBy::Source,
    };

    // Sorted, so the run order -- and therefore every message and every
    // failure list -- is the same on every machine.
    let mut manifests: Vec<PathBuf> = std::fs::read_dir(dir)
        .map_err(|e| Fail::Build(format!("cannot read {}: {e}", dir.display())))?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| {
            p.file_name()
                .and_then(|f| f.to_str())
                .is_some_and(|f| f.ends_with(".doc.json"))
        })
        .collect();
    manifests.sort();
    if manifests.is_empty() {
        // An empty batch that exits 0 is indistinguishable from a batch that
        // rendered everything, which is the shape of inert gate this
        // repository keeps finding.
        return Err(Fail::Build(format!(
            "no `*.doc.json` in {} -- refusing to report a successful batch over zero \
             documents",
            dir.display()
        )));
    }

    std::fs::create_dir_all(out)
        .map_err(|e| Fail::Build(format!("cannot create {}: {e}", out.display())))?;
    let mut failures: Vec<String> = Vec::new();
    let mut diagnostics = 0usize;
    let mut written = 0usize;
    for manifest in &manifests {
        let mut assembler = Assembler::new(options_for(a, manifest));
        let doc = match assembler.assemble_path(manifest) {
            Ok(d) => d,
            Err(e) => {
                failures.push(format!("{}: {e}", manifest.display()));
                continue;
            }
        };
        let rendered = emitter.emit(&doc);
        let diags = emitter.diagnostics(&doc);
        for d in &diags {
            eprintln!("axeyum-render: DIAGNOSTIC: {}: {d}", manifest.display());
        }
        diagnostics += diags.len();
        if a.fail_on_diagnostics && !diags.is_empty() {
            failures.push(format!(
                "{}: {} emitter diagnostic(s)",
                manifest.display(),
                diags.len()
            ));
            continue;
        }
        let stem = out_stem(rule, manifest, &doc.doc_id);
        write(
            &out.join(format!("{stem}.{}", emitter.primary_extension())),
            &rendered.primary,
        )?;
        written += 1;
        for (name, contents) in &rendered.aux {
            write(&out.join(name), contents)?;
        }
    }
    if !failures.is_empty() {
        for f in &failures {
            eprintln!("axeyum-render: REFUSED {f}");
        }
        return Err(Fail::Build(format!(
            "{} of {} document(s) in {} were refused",
            failures.len(),
            manifests.len(),
            dir.display()
        )));
    }
    eprintln!(
        "rendered {written} document(s) from {} as {format} ({diagnostics} diagnostic(s))",
        dir.display()
    );
    Ok(())
}

fn cmd_validate(a: &Args) -> Result<(), Fail> {
    let manifest = a
        .manifest
        .as_ref()
        .ok_or_else(|| Fail::Usage("validate needs --manifest".to_string()))?;
    let mut assembler = Assembler::new(options_for(a, manifest));
    let doc = assembler
        .assemble_path(manifest)
        .map_err(|e| Fail::Build(e.to_string()))?;

    println!("document `{}`: {} block(s)", doc.doc_id, doc.blocks.len());
    let mut hashed = 0usize;
    for b in &doc.blocks {
        if let Some(p) = &b.provenance {
            hashed += p.inputs.len();
        }
        if let axeyum_render::assemble::ResolvedKind::Table { source, .. } = &b.kind {
            hashed += source.inputs.len();
        }
        if let axeyum_render::assemble::ResolvedKind::Claim { evidence, .. } = &b.kind {
            hashed += evidence.iter().map(|e| e.inputs_verified).sum::<usize>();
        }
    }
    println!("{hashed} declared input(s) re-hashed and matched");
    if doc.claims.is_empty() {
        println!("no claims");
    } else {
        println!("claims:");
        for (label, status) in &doc.claims {
            println!("  [{}] {label}", status.badge());
        }
    }
    Ok(())
}

fn cmd_hash(a: &Args) -> Result<(), Fail> {
    if a.rest.is_empty() {
        return Err(Fail::Usage("hash needs at least one file".to_string()));
    }
    for path in &a.rest {
        let bytes =
            std::fs::read(path).map_err(|e| Fail::Build(format!("cannot read {path}: {e}")))?;
        println!("{}  {path}", hex_digest(&bytes));
    }
    Ok(())
}

fn write(path: &Path, contents: &str) -> Result<(), Fail> {
    std::fs::write(path, contents)
        .map_err(|e| Fail::Build(format!("cannot write {}: {e}", path.display())))
}
