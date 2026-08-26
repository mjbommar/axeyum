//! Emit the constructed AVX2 byte-reversal witness and its checked one-step
//! DRAT lower-bound certificate.

use std::{env, fs, path::PathBuf};

use axeyum_cnf::write_drat;
use axeyum_search::simd::{ByteTags, byte_reverse_sequence, refute_one_step, replay_sequence};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let output = env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .ok_or("usage: certify_avx2_byte_reverse OUTPUT_DIRECTORY")?;
    fs::create_dir_all(&output)?;

    let sequence = byte_reverse_sequence();
    if replay_sequence(&sequence) != ByteTags::reversed() {
        return Err("constructed sequence did not replay to the target".into());
    }
    let certificate = refute_one_step(&ByteTags::reversed())
        .map_err(|error| format!("one-step certification failed: {error:?}"))?;
    let dimacs = certificate.formula.to_dimacs();
    let drat = write_drat(&certificate.proof);

    fs::write(
        output.join("sequence.txt"),
        "input-tags: 0,1,...,31\nstep-1: vpshufb control=15,14,...,0,15,14,...,0\nstep-2: vperm2i128 same-source low=high-half high=low-half imm8=0x01\noutput-tags: 31,30,...,0\n",
    )?;
    fs::write(output.join("one-step.cnf"), dimacs.as_bytes())?;
    fs::write(output.join("one-step.drat"), drat.as_bytes())?;
    fs::write(
        output.join("RESULT.txt"),
        format!(
            "VERIFIED\nscope: unary AVX2 {{vpshufb, same-source vperm2i128}}\ntarget: global reversal of 32 distinct byte provenance tags\nupper-bound: 2 instructions\nlower-bound: no 0- or 1-instruction sequence\ncnf-vars: {}\ncnf-clauses: {}\ndrat-steps: {}\n",
            certificate.formula.variable_count(),
            certificate.formula.clauses().len(),
            certificate.proof.len(),
        ),
    )?;
    println!(
        "VERIFIED: byte reverse needs exactly 2 instructions in the declared subset; artifacts={}",
        output.display()
    );
    Ok(())
}
