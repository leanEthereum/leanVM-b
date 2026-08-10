//! Helpers shared by the integration tests. Each test file is its own crate and
//! compiles this module separately, so a helper it does not call is dead there.
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
