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
    ("conditionals", "30f6eb0dcc39085175bf53d5efc9f869e79d531610b99f924b698ddadded3637"),
    ("const_params", "e50886d2faa9365656fc5977fc9b49ea5f8f1c30232973b5c56375e93e0b85f0"),
    ("fibonacci", "9a568118cfea45f6aa9e1c908ccee8e4aa9e7e28e0e4c7c96e0e01d6ee45f20b"),
    ("hash_heap_chain", "eadd436549dc46e50c38791104c5614c5797a29186ccff8702b7148f9b8d6076"),
    ("hash_slices", "2f9cda52507cc8a3208a2420a97f4ef6e9aff80bcc21e4fbaccd44e3454eab87"),
    ("heapbuf_dyn", "d799507f3a87f413e5ef4c18f33c9085d5b626037437d1e9fc6c82ffcb8f9757"),
    ("hint", "70356063d76c9e819fadb631d09ca23c71e72027e8b47857f3fc4d5169aad3c1"),
    ("identities", "f641a195fc9bc003287f2a2c4150dc5c5e66e8b14fc3a0cbe3e5aa242b5e4e44"),
    ("match", "c07aaa250c710bdf9de9afe81c8be055f1d0804c4b295ad39e116188ea9c8d40"),
    ("match_arms", "6644f87a66801882c865cec36f7c6744dfce0fe46deeaa31919a95fd03b199cb"),
    ("nested", "cb6957e3a7df346a3b666c04bae68a636404de923d399060d93395a0ae0e6daa"),
    ("runtime_loop", "5d5a9b396ed48f31e845a9322186e5bfd01216f05e3dbbe209c7fd073d631e7f"),
    ("scoping", "84ef6a1225c59b0c27da4f8da82d08ad992b0700cad6c8a75a6cadbd3dc552e1"),
    ("unroll", "ac984121bad68319f9832c937800e91dacc73d6363f02ab3ad291b1d4c72b0e4"),
    ("wots_walk", "465eaddf8fe7dd559c03bfc72c836dea13055174306e29caace823f015fd8d38"),
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
