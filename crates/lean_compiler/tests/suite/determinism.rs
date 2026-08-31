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
const GOLDEN: &[(&str, &str)] = &[
    ("conditionals", "924339ba2db7e6f063c62ea5ac80034f9cdf9490426973ba316b38e87c2b0b51"),
    ("const_params", "608e54cfeaf5eb13f7d423a1f251079a5528e753448a31fb5ee4e12c9ab1ca2c"),
    ("fibonacci", "929519de50dcef8aa919c523458f88ad67da4abfc3974c00acf8fd4a5996b7b2"),
    ("hash_heap_chain", "b704c994f1972e9f1610625b5877c75be4ed70b7a1cc71dee3feebefe2da78af"),
    ("hash_slices", "7146009faff5ace9a0c8446b63fd90de89aa82417709ddeee47dcc945848d85b"),
    ("heapbuf_dyn", "dc306f7cac8a664d85555fc746b0d54796dc654a87b9a63ea353d12597a25174"),
    ("hint", "b0fb2bce402a611a072382c85bf64ecbc95becebb33824c13853ed51ad3deeac"),
    ("identities", "d51dc227b94a4074b7950a4961ef31f834a2032adfa8fe62f3e85292193f2ea3"),
    ("match", "ee000b896f39eac651de4c4da05b1af7bdf5ea805954ddb3c5cd45f4e56fcd67"),
    ("match_range", "bbdb9183f56349cea48b268fccda310ec7bed631260a5ccdbfdca056724d853a"),
    ("nested", "bb03a048954a7162b63498cd6dee8dae7802b474a98b1d3e23b070eb3fb256b2"),
    ("runtime_loop", "55a2ca8dc9d75980c6d5eec96245967cabb2e0fb7f41b11d504cb398cb109667"),
    ("scoping", "cb9612c923ca5f7b17aa7c399dae97ca54353ec63ebe9ff5c6e49f895b1a6a13"),
    ("unroll", "02ea947eee32d5d42f83eb294acbf93e31836eb08ae205ca95b69f6b8a177a8d"),
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
    assert!(dropped.is_empty(), "GOLDEN names a program that no longer exists: {dropped:?}");
    if !moved.is_empty() {
        let table: String = actual
            .iter()
            .map(|(n, d)| format!("    (\"{n}\", \"{d}\"),\n"))
            .collect();
        panic!("bytecode changed for {moved:?}\n\nif that was intended, GOLDEN is now:\n{table}");
    }
}
