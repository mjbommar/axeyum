//! Measure whether a reflexive theorem inherits an imported definition's footprint.

use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use serde_json::json;
use sha2::{Digest, Sha256};

const STREAM_SHA256: &str = "58c09fb4f8b3af7adacd8d0c22e945507e6ffb3920b0581c22d17afa1867d3b9";
const TEST_BIT_CONTROL: &str = "Axeyum.Autogenesis.ImportedTestBitReflexivityProbe";
const BITWISE_CONTROL: &str = "Axeyum.Autogenesis.ImportedBitwiseReflexivityProbe";

fn main() {
    if let Err(error) = run() {
        eprintln!("imported-definition-reflexivity-footprint: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: imported_definition_reflexivity_footprint <Nat.testBit_bitwise.ndjson>")?;
    if arguments.next().is_some() {
        return Err("unexpected trailing argument".to_owned());
    }

    let bytes = fs::read(path).map_err(|error| error.to_string())?;
    if hex_sha256(&bytes) != STREAM_SHA256 {
        return Err("candidate stream identity changed".to_owned());
    }
    let imported = import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("candidate import failed: {error:?}"))?;
    if imported.report().lean_version != "4.30.0"
        || imported.report().lean_githash != "d024af099ca4bf2c86f649261ebf59565dc8c622"
    {
        return Err(format!(
            "candidate source authority changed: Lean {} ({})",
            imported.report().lean_version,
            imported.report().lean_githash
        ));
    }
    let (mut kernel, report) = imported.into_parts();

    let test_bit = add_reflexivity_control(&mut kernel, "Nat.testBit", TEST_BIT_CONTROL)?;
    let bitwise = add_reflexivity_control(&mut kernel, "Nat.bitwise", BITWISE_CONTROL)?;
    let test_bit_row = control_row(&kernel, test_bit)?;
    let bitwise_row = control_row(&kernel, bitwise)?;

    for row in [&test_bit_row, &bitwise_row] {
        if row["axiom_footprint"] != json!(["propext"]) {
            return Err(format!(
                "unexpected control footprint for {}: {}",
                row["name"], row["axiom_footprint"]
            ));
        }
        if row["direct_theorem_dependencies"] != json!([]) {
            return Err(format!(
                "reflexivity control unexpectedly depends on a theorem: {}",
                row["name"]
            ));
        }
    }

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-imported-definition-reflexivity-footprint",
            "authority": "diagnostic only; no proof transport authority, no theorem admission authority, and no fact-transition authority",
            "lean_version": report.lean_version,
            "lean_githash": report.lean_githash,
            "source_stream_sha256": STREAM_SHA256,
            "controls": [test_bit_row, bitwise_row],
            "finding": "a reflexive theorem with no theorem dependencies inherits propext solely by mentioning either imported definition in its statement",
            "consequence": "an exact theorem over either imported operation cannot have an empty declaration-reached footprint while those definitions retain their current implementation closures",
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn add_reflexivity_control(
    kernel: &mut Kernel,
    definition: &str,
    control: &str,
) -> Result<NameId, String> {
    let definition = find_name(kernel, definition)?;
    let ty = match kernel.environment().get(definition) {
        Some(Declaration::Definition { uparams, ty, .. }) if uparams.is_empty() => *ty,
        _ => return Err("probe target is not a monomorphic definition".to_owned()),
    };
    let eq = find_name(kernel, "Eq")?;
    let eq_refl = find_name(kernel, "Eq.refl")?;
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let value = kernel.const_(definition, vec![]);
    let eq_const = kernel.const_(eq, vec![one]);
    let eq_ty = kernel.app(eq_const, ty);
    let eq_lhs = kernel.app(eq_ty, value);
    let theorem_ty = kernel.app(eq_lhs, value);
    let refl_const = kernel.const_(eq_refl, vec![one]);
    let refl_ty = kernel.app(refl_const, ty);
    let theorem_value = kernel.app(refl_ty, value);
    let anonymous = kernel.anon();
    let name = kernel.name_str(anonymous, control);
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: theorem_ty,
            value: theorem_value,
        })
        .map_err(|error| format!("control theorem failed: {error:?}"))?;
    Ok(name)
}

fn control_row(kernel: &Kernel, name: NameId) -> Result<serde_json::Value, String> {
    let declaration = kernel
        .environment()
        .get(name)
        .ok_or("control theorem disappeared")?;
    Ok(json!({
        "name": kernel.display_name(name).to_string(),
        "type": kernel.render_lean(declaration.ty()),
        "axiom_footprint": names(kernel, &kernel.axiom_footprint(name)),
        "direct_declaration_dependencies": names(kernel, &kernel.declaration_dependencies(name)),
        "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(name)),
    }))
}

fn names(kernel: &Kernel, names: &[NameId]) -> Vec<String> {
    let mut rendered = names
        .iter()
        .map(|name| kernel.display_name(*name).to_string())
        .collect::<Vec<_>>();
    rendered.sort();
    rendered
}

fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write;
        write!(output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}

fn find_name(kernel: &Kernel, rendered: &str) -> Result<NameId, String> {
    kernel
        .environment()
        .iter()
        .find_map(|(&name, _)| (kernel.display_name(name).to_string() == rendered).then_some(name))
        .ok_or_else(|| format!("missing declaration: {rendered}"))
}
