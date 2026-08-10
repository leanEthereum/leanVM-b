//! Pins `python-verifier/verifier.py` against `lean_vm::cpu::verify`: the same
//! protocol is written out in Rust, in Python, and in zkDSL, so any protocol
//! change must land in all three, and this is what catches the Python one
//! drifting.

use lean_compiler::{compile, parse_with_replacements};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};
use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

const SOURCE: &str = r#"
from snark_lib import *

LOOP_STEPS = LOOP_STEPS_PLACEHOLDER

def mix(value, tag):
    # A JUMP condition is K-valued (a g-power here), never an arbitrary word.
    if tag == 0:
        return value
    return value * GEN + value

def main():
    seed = [5, 7]
    digest = StackBuf(2)
    blake3(seed, seed, digest)

    chain = HeapBuf(LOOP_STEPS + 1)
    chain[1] = digest[0]
    for index in mul_range(1, GEN ** LOOP_STEPS):
        chain[index * GEN] = mix(chain[index] + index, index) + index

    public = GEN ** 0
    public[1] = chain[GEN ** LOOP_STEPS]
    public[GEN] = mix(digest[1], GEN ** 0)
    return
"#;

const LOOP_STEPS: usize = 16_384;

fn public_input() -> [F192; 2] {
    use lean_vm::blake3_flock::{FLAGS, IV, compression, digest, metadata};

    let seed = [F64(5), F64::ZERO, F64(7), F64::ZERO];
    let metadata = metadata(0, 64, FLAGS);
    let digest = digest(&compression(seed, seed, IV, metadata));
    let digest = [
        F192::new(digest[0].0, digest[1].0, 0),
        F192::new(digest[2].0, digest[3].0, 0),
    ];
    let mut value = digest[0];
    let mut index = F192::ONE;
    let generator = F192::from(g_pow(1));
    for _ in 0..LOOP_STEPS {
        let candidate = value + index;
        let product = candidate * generator;
        value = (if product == F192::ZERO {
            candidate
        } else {
            product + candidate
        }) + index;
        index *= generator;
    }
    [value, digest[1] * generator + digest[1]]
}

#[test]
fn test_python_verifier() {
    let replacements = BTreeMap::from([("LOOP_STEPS_PLACEHOLDER".to_string(), LOOP_STEPS.to_string())]);
    let ast = parse_with_replacements(SOURCE, &replacements).expect("parse zkDSL program");
    let program = compile(&ast);
    let public_input = public_input();
    let (proof, stats) = prove(&program, public_input, 1);
    // Python reads the RAW proof: same protocol, each query carrying its own
    // full Merkle path instead of one octopus over the batch. A Rust verify
    // expands the wire form, so the pruning is written once.
    let raw = verify(&program, &public_input, &proof)
        .expect("honest proof verifies")
        .raw;

    let directory = std::env::temp_dir().join(format!("leanvm-python-verifier-test-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("create test directory");
    let proof_path = directory.join("proof.bin");
    let bytecode_path = directory.join("bytecode.bin");
    let public_input_path = directory.join("public_input.bin");
    let encoded = bincode::serialize(&proof).expect("serialize proof");
    std::fs::write(&proof_path, bincode::serialize(&raw).expect("serialize raw proof")).expect("write proof");
    // The statement the verifier takes is the bytecode multilinear plus 256 bits
    // of public input, not a structured program.
    let table: Vec<u8> = lean_vm::cpu::layout::bytecode_table(&program.prog)
        .iter()
        .flat_map(|w| w.0.to_le_bytes())
        .collect();
    std::fs::write(&bytecode_path, &table).expect("write bytecode");
    let pi: Vec<u8> = public_input
        .iter()
        .flat_map(|v| [v.c0.to_le_bytes(), v.c1.to_le_bytes()].concat())
        .collect();
    std::fs::write(&public_input_path, &pi).expect("write public input");

    let verifier = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../python-verifier/verifier.py");
    let verification_started = Instant::now();
    let output = Command::new("python3")
        .arg(&verifier)
        .arg(&bytecode_path)
        .arg(&public_input_path)
        .arg(&proof_path)
        .output()
        .expect("run native Python verifier");
    let verification_time = verification_started.elapsed();
    assert!(
        output.status.success(),
        "native Python verification failed:\n{}",
        String::from_utf8_lossy(&output.stderr),
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "verification succeeded",);

    let mut malformed_announcement = proof.clone();
    malformed_announcement.stream[0].c1 = 1;
    assert!(verify(&program, &public_input, &malformed_announcement).is_err());
    let mut raw_announcement = raw.clone();
    raw_announcement.stream[0].c1 = 1;
    std::fs::write(
        &proof_path,
        bincode::serialize(&raw_announcement).expect("serialize malformed announcement"),
    )
    .expect("write malformed announcement");
    let output = Command::new("python3")
        .arg(&verifier)
        .arg(&bytecode_path)
        .arg(&public_input_path)
        .arg(&proof_path)
        .output()
        .expect("run Python verifier on malformed announcement");
    assert!(!output.status.success(), "Python accepted a noncanonical announcement");

    let mut malformed_root = proof.clone();
    let root_offset = lean_vm::tables::N_TABLES + 2;
    malformed_root.stream[root_offset].c2 = 1;
    assert!(verify(&program, &public_input, &malformed_root).is_err());
    let mut raw_root = raw.clone();
    raw_root.stream[root_offset].c2 = 1;
    std::fs::write(
        &proof_path,
        bincode::serialize(&raw_root).expect("serialize malformed root"),
    )
    .expect("write malformed root");
    let output = Command::new("python3")
        .arg(verifier)
        .arg(bytecode_path)
        .arg(public_input_path)
        .arg(proof_path)
        .output()
        .expect("run Python verifier on malformed root");
    assert!(
        !output.status.success(),
        "Python accepted a noncanonical commitment root"
    );

    println!(
        "zkDSL compiled to {} instructions; proved {} cycles in {} bytes; Python verified in {:.2?}",
        program.prog.len(),
        stats.cycles,
        encoded.len(),
        verification_time,
    );
    std::fs::remove_dir_all(directory).expect("remove test directory");
}
