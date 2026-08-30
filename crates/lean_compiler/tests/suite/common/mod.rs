//! Helpers shared by the integration tests, reached as `crate::common::…`.
#![allow(dead_code)]

use lean_compiler::{compile_without_filler, parse};
use primitives::field::F192;

/// The program's own instruction mix: a build without the fill blocks, executed but not
/// proven. Proving needs them, since a table's height has to be a power of two with no
/// padding rows, but their dummy rows would drown out exactly what these counts are
/// measuring.
pub fn mix(src: &str, pi: [F192; 2]) -> [usize; lean_vm::cpu::Stats::TABLES.len()] {
    compile_without_filler(&parse(src).expect("parse"))
        .execute(pi)
        .base_counts
}

/// An AST's shape with source lines stripped. Two spellings of the same program
/// (a constant against its substituted value, a placeholder against the filled
/// text) are the same program but rarely occupy the same lines, so comparing
/// them by `Debug` has to ignore that field.
pub fn without_lines(ast: &lean_compiler::Ast) -> String {
    let d = format!("{ast:?}");
    let (mut out, mut rest) = (String::with_capacity(d.len()), d.as_str());
    while let Some(i) = rest.find("line: ") {
        out.push_str(&rest[..i]);
        let after = &rest[i + "line: ".len()..];
        rest = &after[after.find(", ").expect("`line` is followed by another field") + 2..];
    }
    out.push_str(rest);
    out
}
