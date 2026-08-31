//! One source compiles to one program, always.
//!
//! The bytecode digest leads the Fiat--Shamir transcript, so two builds of one
//! source that disagree are two incompatible proof systems, and the symptom is a
//! proof that stops verifying rather than a crash. The compiler walks several
//! `HashMap`s; one `sort_unstable` in `lower::scoped` is what currently keeps
//! their iteration order out of the bytecode, and nothing tested it.
//!
//! Two properties, both covered here:
//!
//! * *Within a process.* `RandomState` bumps its seed once per map, so the
//!   second compilation hashes with different keys than the first. Compiling
//!   twice is a real perturbation, not a repeat.
//! * *Across processes.* The digests below were produced by an earlier process,
//!   under a different global seed. Matching them today is the check.
//!
//! A digest moves only when the compiler's output moves. That is a deliberate
//! act: update `GOLDEN` in the same commit, and say in the message what changed.

use std::collections::BTreeMap;
use std::fs;

use lean_compiler::{compile, parse};
use lean_vm::cpu::Program;

/// `tests/programs/<name>.py` against the digest of the bytecode it compiles to.
/// The list is closed: a new program must be added here, so one cannot be added
/// without a digest.
#[rustfmt::skip]
const GOLDEN: &[(&str, &str)] = &[
    ("conditionals", "c94c4c1fbe7f9aa0f373af7ec86123f0ba760ae11a39f7560682129f9566d4f4"),
    ("const_params", "494a3e891f6e5b53b8946845f98990f36b0f1e01479db2c26f2fa27cfb9e7f00"),
    ("fibonacci", "68558b18c6c0facbc6b9496aa0a85036e1360922b23631f3d4ca7f82223ed2d8"),
    ("hash_heap_chain", "c0ba2a3f1a68d43f0ddeebfebf3918b489c1fef0c0d5ee45cd713c5cfbb17427"),
    ("hash_slices", "7146009faff5ace9a0c8446b63fd90de89aa82417709ddeee47dcc945848d85b"),
    ("heapbuf_dyn", "dc306f7cac8a664d85555fc746b0d54796dc654a87b9a63ea353d12597a25174"),
    ("hint", "b0fb2bce402a611a072382c85bf64ecbc95becebb33824c13853ed51ad3deeac"),
    ("identities", "d51dc227b94a4074b7950a4961ef31f834a2032adfa8fe62f3e85292193f2ea3"),
    ("match", "be0be17b8c84c39d36f25a34e276bd497c72cfe2d000a056f51e2589aaeac378"),
    ("match_range", "bbdb9183f56349cea48b268fccda310ec7bed631260a5ccdbfdca056724d853a"),
    ("nested", "49d116d596c1e3190a553a693aac676f7b4fff6e7287d389ce795f9082624de1"),
    ("runtime_loop", "03576f38fbd593af5a5e47c062235434a2ab1c94ac1be3d6a3c59e7d31515491"),
    ("scoping", "cb9612c923ca5f7b17aa7c399dae97ca54353ec63ebe9ff5c6e49f895b1a6a13"),
    ("unroll", "94f7066b2e850330fa6288a7ffd4b75dff4bbf8079cab82fca4ebec3438260f8"),
    ("wots_walk", "c04c1922e456e91fb577c948821fae37cba922b4f4d992bbcb41b8661a7a19cc"),
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
