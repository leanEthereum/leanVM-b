//! Compiler-soundness harness: does the emitted bytecode still carry every
//! constraint the source asked for?
//!
//! A dropped constraint is invisible to ordinary tests. The happy path passes
//! either way, the compiler emits no diagnostic, and the symptom only appears as
//! a proof that accepts something it should not. So the three checks below all
//! attack the *absence* of a constraint rather than the presence of a value.
//!
//! 1. [`check_case`], **perturbation**: one valid trial that must run, and a
//!    table of single-cell pokes at the public input or a witness stream, each of
//!    which must make the run fail. A dropped assertion shows up as a poke that
//!    is accepted. (This is the shape of `leanVM`'s own soundness suite.)
//! 2. [`check_pair`], **equivalence**: two spellings the language documents as
//!    interchangeable must accept exactly the same trials. Every dropped-constraint
//!    bug found so far is an *asymmetry*: an assertion that survives one spelling
//!    and vanishes in the other, so comparing the two finds it without anyone
//!    having to guess which side is wrong.
//! 3. [`Execution::unconstrained_reads`], **unconstrained reads**, asserted on
//!    every accepting run of both layers above. A cell an instruction read that
//!    nothing ever wrote is a live value from outside the constraint system.
//!
//! The three are complementary, and a fix should land with whichever one catches
//! it. Layer 3 sees a dropped store whose cell is then *read* (the value came from
//! nowhere); layer 2 sees a dropped store whose cell is then *ignored* (the value
//! came from the alias instead, and the physical write is orphaned), and layer 3 is
//! blind to that one, because nothing reads the orphan. Layer 1 needs a program
//! whose assertion the poke can violate, and in exchange it needs no second
//! spelling to compare against.

#![allow(dead_code)]

use lean_compiler::{compile_without_filler, parse};
use lean_vm::cpu::Program;
use primitives::field::{F64, F192, g_pow};

mod cases;
mod pairs;

/// `g^k` as a machine word, the way every index, address and counter is written.
pub fn g(k: usize) -> F192 {
    F192::from(g_pow(k))
}

/// A K-valued literal in the low lane.
pub fn k(x: u64) -> F192 {
    F192::from(F64(x))
}

/// One `hint_witness` stream: the name, then one entry per call naming it.
pub type Stream = (&'static str, Vec<Vec<F192>>);

/// Everything a run consumes: the public statement and the prover's advice.
#[derive(Clone)]
pub struct Trial {
    pub pi: [F192; 2],
    pub streams: Vec<Stream>,
}

impl Trial {
    pub fn new(pi: [F192; 2]) -> Self {
        Self {
            pi,
            streams: Vec::new(),
        }
    }

    /// Add a stream whose every call takes one entry of `cells`.
    pub fn stream(mut self, name: &'static str, entries: Vec<Vec<F192>>) -> Self {
        self.streams.push((name, entries));
        self
    }

    fn poke(&self, p: &Poke) -> Self {
        let mut t = self.clone();
        match *p {
            Poke::Pi { slot, to } => t.pi[slot] = to,
            Poke::Wit { name, entry, cell, to } => {
                let s = t
                    .streams
                    .iter_mut()
                    .find(|(n, _)| *n == name)
                    .unwrap_or_else(|| panic!("no stream `{name}` in this trial"));
                s.1[entry][cell] = to;
            }
        }
        t
    }
}

/// A single-cell mutation of a trial. One cell, so a poke that is accepted names
/// exactly the constraint that is missing.
#[derive(Clone, Copy)]
pub enum Poke {
    /// Public-input word 0 or 1.
    Pi { slot: usize, to: F192 },
    /// Cell `cell` of entry `entry` of witness stream `name`.
    Wit {
        name: &'static str,
        entry: usize,
        cell: usize,
        to: F192,
    },
}

impl Poke {
    fn label(&self) -> String {
        match self {
            Poke::Pi { slot, to } => format!("pi[{slot}] := {:x}:{:x}:{:x}", to.c2, to.c1, to.c0),
            Poke::Wit { name, entry, cell, to } => {
                format!("{name}[{entry}][{cell}] := {:x}:{:x}:{:x}", to.c2, to.c1, to.c0)
            }
        }
    }
}

/// Poke a public-input word.
pub fn pi(slot: usize, to: F192) -> Poke {
    Poke::Pi { slot, to }
}

/// Poke cell `cell` of the first entry of stream `name`.
pub fn wit(name: &'static str, cell: usize, to: F192) -> Poke {
    Poke::Wit {
        name,
        entry: 0,
        cell,
        to,
    }
}

/// Poke cell `cell` of entry `entry` of stream `name`.
pub fn wit_at(name: &'static str, entry: usize, cell: usize, to: F192) -> Poke {
    Poke::Wit { name, entry, cell, to }
}

/// What an honest run of the emitted bytecode did.
pub enum Ran {
    /// It completed. Carries the cells it read that nothing ever wrote, which
    /// must be empty for the program to mean what its source says.
    Ok { unconstrained: Vec<u32> },
    /// It aborted: a write-once conflict (which is how every `assert` fails), a
    /// wild dereference, or any other interpreter panic.
    Rejected,
}

impl Ran {
    pub fn accepted(&self) -> bool {
        matches!(self, Ran::Ok { .. })
    }
    fn verb(&self) -> &'static str {
        if self.accepted() { "ACCEPTED" } else { "rejected" }
    }
}

/// Compile once. Kept out of [`run`] so a compiler panic is a loud test failure
/// rather than a silent "rejected".
pub fn build(src: &str) -> Program {
    compile_without_filler(&parse(src).expect("parse"))
}

/// Run `program` on `t`. The fill blocks are irrelevant to what the program
/// asserts, so this executes the unfilled build.
pub fn run(program: &Program, t: &Trial) -> Ran {
    let mut p = program.clone();
    for (name, entries) in &t.streams {
        p.set_witness(*name, entries.clone());
    }
    let pi = t.pi;
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| p.execute(pi))) {
        Ok(exec) => Ran::Ok {
            unconstrained: exec.unconstrained_reads,
        },
        Err(_) => Ran::Rejected,
    }
}

// ---------------------------------------------------------------------------
// Layer 1: perturbation
// ---------------------------------------------------------------------------

/// One program, one valid trial, and the pokes that must break it.
pub struct Case {
    pub name: &'static str,
    pub src: &'static str,
    pub valid: Trial,
    pub pokes: Vec<Poke>,
}

pub fn check_case(c: &Case) {
    let program = build(c.src);
    match run(&program, &c.valid) {
        Ran::Ok { unconstrained } => assert!(
            unconstrained.is_empty(),
            "{}: the valid trial reads cells nothing writes: {unconstrained:?}. \
             A live value came from outside the constraint system, so the lowering \
             dropped a store the source asked for.",
            c.name
        ),
        Ran::Rejected => panic!("{}: the valid trial must run, and did not", c.name),
    }
    assert!(!c.pokes.is_empty(), "{}: a case with no pokes checks nothing", c.name);
    for p in &c.pokes {
        assert!(
            !run(&program, &c.valid.poke(p)).accepted(),
            "{}: poke `{}` was ACCEPTED. The constraint that should have caught it \
             is not in the emitted bytecode.",
            c.name,
            p.label()
        );
    }
}

// ---------------------------------------------------------------------------
// Layer 2: equivalence
// ---------------------------------------------------------------------------

/// Two spellings the language documents as interchangeable, and the trials that
/// have to agree. `why` names the guarantee, so a failure reads as a broken
/// promise rather than as a diff.
pub struct Pair<'a> {
    pub name: &'static str,
    pub why: &'static str,
    pub a: &'a str,
    pub b: &'a str,
    pub trials: Vec<Trial>,
}

pub fn check_pair(p: &Pair<'_>) {
    let (pa, pb) = (build(p.a), build(p.b));
    assert!(!p.trials.is_empty(), "{}: a pair with no trials checks nothing", p.name);
    let mut agreed_reject = false;
    for (i, t) in p.trials.iter().enumerate() {
        let (ra, rb) = (run(&pa, t), run(&pb, t));
        assert_eq!(
            ra.accepted(),
            rb.accepted(),
            "{}: trial {i}: spelling A {} but spelling B {}.\n  {}\n\
             One of the two dropped a constraint; the more permissive side is the buggy one.",
            p.name,
            ra.verb(),
            rb.verb(),
            p.why
        );
        for (which, r) in [("A", &ra), ("B", &rb)] {
            if let Ran::Ok { unconstrained } = r {
                assert!(
                    unconstrained.is_empty(),
                    "{}: trial {i}: spelling {which} reads cells nothing writes: {unconstrained:?}",
                    p.name
                );
            }
        }
        agreed_reject |= !ra.accepted();
    }
    // A pair whose every trial is accepted by both would also pass if both
    // spellings dropped everything, so require at least one rejection.
    assert!(
        agreed_reject,
        "{}: every trial was accepted by both spellings, so this pair would pass even \
         if both sides dropped the constraint. Add a trial that must be rejected.",
        p.name
    );
}
