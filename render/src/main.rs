//! `axeyum-render` -- the Doc-IR command line.
//!
//! Three subcommands and no argument-parsing dependency, because the surface is
//! three subcommands:
//!
//! ```text
//! axeyum-render render   --manifest M --format md|tex|html [--out DIR] [--strict]
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

fn cmd_render(a: &Args) -> Result<(), Fail> {
    let manifest = a
        .manifest
        .as_ref()
        .ok_or_else(|| Fail::Usage("render needs --manifest".to_string()))?;
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
            let primary = dir.join(format!("{}.{}", doc.doc_id, emitter.primary_extension()));
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
