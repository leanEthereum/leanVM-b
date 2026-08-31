//! One source compiles to one program, always, and the same program it compiled
//! to yesterday.
//!
//! The bytecode digest leads the Fiat--Shamir transcript, so two builds of one
//! source that disagree are two incompatible proof systems, and the symptom is a
//! proof that stops verifying rather than a crash.
//!
//! Two different properties, and only the first is about determinism:
//!
//! * *Within a process*, compiling twice is a real perturbation rather than a
//!   repeat, since `RandomState` bumps its seed once per map, so the second
//!   compilation hashes with different keys than the first.
//! * *Across commits*, `GOLDEN` is a SNAPSHOT of the compiler's output. It does
//!   not prove determinism (nothing iterating a hash container reaches the
//!   bytecode today, and deliberately reversing the branch-output order at a join
//!   moves no digest). It earns its place a different way: a codegen change that
//!   was not intended shows up here and nowhere else, and every entry that moved
//!   this far was a change someone then had to justify.
//!
//! So a moved digest is a question, not a chore: update `GOLDEN` in the same
//! commit and say in the message which change moved it.

use std::collections::BTreeMap;
use std::fs;

use lean_compiler::{compile, parse};
use lean_vm::cpu::Program;

/// `tests/programs/<name>.py` against the digest of the bytecode it compiles to.
/// The list is closed: a new program must be added here, so one cannot be added
/// without a digest.
#[rustfmt::skip]
const GOLDEN: &[(&str, &str)] = &[
    ("conditionals", "583644bbf4d2a2b4cd9a87e52fa8d4a325a13acba4686b874d4c027dc3be21f7"),
    ("const_params", "6fa2cdbe74ca9df078e10050f9f295866ef3605ce351951ca2390795bf56da99"),
    ("fibonacci", "68558b18c6c0facbc6b9496aa0a85036e1360922b23631f3d4ca7f82223ed2d8"),
    ("hash_heap_chain", "875da272156250028125833405931700be63e01e7fe5634b4e4ad98680406e20"),
    ("hash_slices", "a499a753adec66a0730e48ed6f7c4a38ab82a8f4ca12599d70135db9f4235013"),
    ("heapbuf_dyn", "2dcdf13305dac3636d14710580e272648faae223b3cd401a13155a7cc7ac207f"),
    ("hint", "c7269c0a692ee499ca2afedb1b13a03c09cb179d99023decded43afe59dc4655"),
    ("identities", "d51dc227b94a4074b7950a4961ef31f834a2032adfa8fe62f3e85292193f2ea3"),
    ("match", "7e271cc69737625428f9152b46effa4e3972cf936c8725b75e729ec6c727da9f"),
    ("match_arms", "bcbf2e2d320f77aa27c53d80bdcaa7b1547b029a9db0575ec59c2f73f89bdaec"),
    ("nested", "fd9b17b056722d4264316d8d3050d27ceaa9eb9ca9d06410e37c4c0216aa1efb"),
    ("runtime_loop", "03576f38fbd593af5a5e47c062235434a2ab1c94ac1be3d6a3c59e7d31515491"),
    ("scoping", "39f01bbf25caeb910cccfdda6dcaa108bb3e51f120762621ddea7488d5a6ad9a"),
    ("unroll", "4572616c299f71da744df342fdd5f178709e0145036acec199cd2ae6e425aee4"),
    ("wots_walk", "61c7a3f038ae92f2fa0beb415ae08a68e4ad1883728ee42b9e2cec4fdb9bd09c"),
];

fn digest(p: &Program) -> String {
    primitives::hash::hash(format!("{:?}", p.prog).as_bytes())
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Every program in `tests/programs/`, compiled twice.
#[test]
fn bytecode_is_reproducible() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut paths: Vec<_> = fs::read_dir(dir)
        .expect("tests/programs")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no .py programs found");

    let mut actual: Vec<(String, String)> = Vec::new();
    for path in &paths {
        let name = path.file_stem().expect("file stem").to_string_lossy().into_owned();
        let src = fs::read_to_string(path).unwrap_or_else(|e| panic!("{name}: read: {e}"));
        let one = compile(&parse(&src).unwrap_or_else(|e| panic!("{name}: parse: {e}")));
        let two = compile(&parse(&src).unwrap_or_else(|e| panic!("{name}: parse: {e}")));
        assert_eq!(
            digest(&one),
            digest(&two),
            "{name}: two compilations of one source produced different bytecode, \
             so the compiler is reading a hash seed"
        );
        actual.push((name, digest(&one)));
    }

    let want: BTreeMap<&str, &str> = GOLDEN.iter().copied().collect();
    let moved: Vec<&str> = actual
        .iter()
        .filter(|(n, d)| want.get(n.as_str()) != Some(&d.as_str()))
        .map(|(n, _)| n.as_str())
        .collect();
    let dropped: Vec<&str> = want
        .keys()
        .copied()
        .filter(|n| !actual.iter().any(|(a, _)| a == n))
        .collect();
    assert!(
        dropped.is_empty(),
        "GOLDEN names a program that no longer exists: {dropped:?}"
    );
    if !moved.is_empty() {
        let table: String = actual
            .iter()
            .map(|(n, d)| format!("    (\"{n}\", \"{d}\"),\n"))
            .collect();
        panic!("bytecode changed for {moved:?}\n\nif that was intended, GOLDEN is now:\n{table}");
    }
}
