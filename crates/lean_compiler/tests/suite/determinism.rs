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
    ("conditionals", "b3637fcc6515be64b21ae1c9ab06a4cab1bcc8595e2aaa3b63fc8706f32dfd50"),
    ("const_params", "494a3e891f6e5b53b8946845f98990f36b0f1e01479db2c26f2fa27cfb9e7f00"),
    ("fibonacci", "68558b18c6c0facbc6b9496aa0a85036e1360922b23631f3d4ca7f82223ed2d8"),
    ("hash_heap_chain", "c0ba2a3f1a68d43f0ddeebfebf3918b489c1fef0c0d5ee45cd713c5cfbb17427"),
    ("hash_slices", "5278a0c0d77e06f45a767c8c0fc6d6c93d3486a085ac8aaee526516325237495"),
    ("heapbuf_dyn", "dc306f7cac8a664d85555fc746b0d54796dc654a87b9a63ea353d12597a25174"),
    ("hint", "b0fb2bce402a611a072382c85bf64ecbc95becebb33824c13853ed51ad3deeac"),
    ("identities", "d51dc227b94a4074b7950a4961ef31f834a2032adfa8fe62f3e85292193f2ea3"),
    ("match", "6fbdc1514e0cfdef54838b0189113bdb388665d481043e8a190ca6fff9faf6d9"),
    ("match_arms", "810e351e89177b21b4de098b241ab3b99c075ea3f0ce8d06c8c25bc368f9c868"),
    ("nested", "ce0cf100f249b274e7da65f8365d1807eb37edf8fdbbbfc4866235fa3ce251b5"),
    ("runtime_loop", "03576f38fbd593af5a5e47c062235434a2ab1c94ac1be3d6a3c59e7d31515491"),
    ("scoping", "39f01bbf25caeb910cccfdda6dcaa108bb3e51f120762621ddea7488d5a6ad9a"),
    ("unroll", "fe6371bf9a02f8dd1c91a151e86b0795206f2d9352f67fdae3095fb156ea1e2f"),
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
