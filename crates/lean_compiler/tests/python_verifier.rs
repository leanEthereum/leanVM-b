use lean_compiler::{compile, parse_with_replacements};
use lean_vm::cpu::{prove, DerefMode, Op, Program};
use primitives::field::{g_pow, F128T, F64};
use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

const SOURCE: &str = r#"
from snark_lib import *

LOOP_STEPS = LOOP_STEPS_PLACEHOLDER

def mix(value):
    product = value * GEN
    if product == 0:
        return value
    return product + value

def main():
    seed = [5, 7]
    digest = StackBuf(2)
    blake3(seed, seed, digest)

    chain = HeapBuf(LOOP_STEPS + 1)
    chain[1] = digest[0]
    for index in mul_range(1, GEN ** LOOP_STEPS):
        chain[index * GEN] = mix(chain[index] + index) + index

    public = GEN ** 0
    public[1] = chain[GEN ** LOOP_STEPS]
    public[GEN] = mix(digest[1])
    return
"#;

const LOOP_STEPS: usize = 16_384;

fn public_input() -> [F128T; 2] {
    use lean_vm::blake3_flock::{compression, digest, metadata, FLAGS, IV};

    // The seed is two E-words, which on the tower is four K-lanes; `digest` gives
    // four lanes back, i.e. the same two words.
    let seed = [F64(5), F64(0), F64(7), F64(0)];
    let metadata = metadata(0, 64, FLAGS);
    let d = digest(&compression(seed, seed, IV, metadata));
    let words = [F128T::new(d[0].0, d[1].0), F128T::new(d[2].0, d[3].0)];
    let g = F128T::new(g_pow(1).0, 0);
    let mut value = words[0];
    let mut index = F128T::ONE;
    for _ in 0..LOOP_STEPS {
        let candidate = value + index;
        let product = candidate * g;
        value = (if product == F128T::ZERO {
            candidate
        } else {
            product + candidate
        }) + index;
        index *= g;
    }
    [value, words[1] * g + words[1]]
}

fn field_json(value: F128T) -> String {
    format!("[{}, {}]", value.c0, value.c1)
}

fn operation_json(operation: Op) -> String {
    match operation {
        Op::Xor { a, b, c } => format!(r#"    {{"op":"xor","a":{a},"b":{b},"c":{c}}}"#),
        Op::Mul { a, b, c } => format!(r#"    {{"op":"mul","a":{a},"b":{b},"c":{c}}}"#),
        Op::Set { o, k } => format!(r#"    {{"op":"set","o":{o},"k":{}}}"#, field_json(k)),
        Op::Deref {
            alpha,
            beta,
            gamma,
            mode,
        } => {
            let mode = match mode {
                DerefMode::Cell => "cell",
                DerefMode::Pc => "pc",
                DerefMode::Fp => "fp",
            };
            format!(r#"    {{"op":"deref","alpha":{alpha},"beta":{beta},"gamma":{gamma},"mode":"{mode}"}}"#)
        }
        Op::Jump { oc, od, of } => {
            format!(r#"    {{"op":"jump","oc":{oc},"od":{od},"of":{of}}}"#)
        }
        Op::Pack64x2 { a, b, c } => {
            format!(r#"    {{"op":"pack64x2","a":{a},"b":{b},"c":{c}}}"#)
        }
        Op::Blake3 { ins, cv, out, metadata } => format!(
            r#"    {{"op":"blake3","ins":[{},{},{},{}],"cv":{cv},"out":{out},"metadata":{}}}"#,
            ins[0],
            ins[1],
            ins[2],
            ins[3],
            field_json(metadata),
        ),
    }
}

fn statement_json(program: &Program, public_input: [F128T; 2]) -> String {
    let operations = program
        .prog
        .iter()
        .copied()
        .map(operation_json)
        .collect::<Vec<_>>()
        .join(",\n");
    format!(
        "{{\n  \"public_input\": [{}, {}],\n  \"program\": [\n{}\n  ]\n}}\n",
        field_json(public_input[0]),
        field_json(public_input[1]),
        operations,
    )
}

#[test]
// The reference verifier's field and instruction set are ported to the 64-bit tower
// (`python-verifier/verifier.py`, pinned bit-exact by
// `primitives/tests/xcheck.rs`), but its Ligerito opening layer still assumes the
// GHASH commitment: level-0 opened rows are 16-byte E fields there and 8-byte K
// symbols here, so the byte parse desynchronises. Porting that layer (K-symbol
// rows, 512-byte interleaved leaves, the K x E level-0 fold, tower's rate/fold/query
// constants) re-enables this.
#[ignore = "reference verifier's Ligerito opening layer is not yet on the tower"]
fn test_python_verifier() {
    let replacements = BTreeMap::from([("LOOP_STEPS_PLACEHOLDER".to_string(), LOOP_STEPS.to_string())]);
    let ast = parse_with_replacements(SOURCE, &replacements).expect("parse zkDSL program");
    let program = compile(&ast);
    let public_input = public_input();
    let (proof, stats) = prove(&program, public_input);

    let directory = std::env::temp_dir().join(format!("leanvm-python-verifier-test-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("create test directory");
    let proof_path = directory.join("proof.bin");
    let statement_path = directory.join("statement.json");
    let encoded = bincode::serialize(&proof).expect("serialize proof");
    std::fs::write(&proof_path, &encoded).expect("write proof");
    std::fs::write(&statement_path, statement_json(&program, public_input)).expect("write statement");

    let verifier = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../python-verifier/verifier.py");
    let verification_started = Instant::now();
    let output = Command::new("python3")
        .arg(verifier)
        .arg(statement_path)
        .arg(proof_path)
        .output()
        .expect("run native Python verifier");
    let verification_time = verification_started.elapsed();
    assert!(
        output.status.success(),
        "native Python verification failed:\n{}",
        String::from_utf8_lossy(&output.stderr),
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "verification succeeded",);

    println!(
        "zkDSL compiled to {} instructions; proved {} cycles in {} bytes; Python verified in {:.2?}",
        program.prog.len(),
        stats.cycles,
        encoded.len(),
        verification_time,
    );
    std::fs::remove_dir_all(directory).expect("remove test directory");
}
