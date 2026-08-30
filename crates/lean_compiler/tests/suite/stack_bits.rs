//! Computed-advice bit buffers in the frame: `hint_decompose_bits` into a
//! `StackBuf`, and `addr()` naming the run so it can still be indexed through a
//! pointer (at a runtime index, or from a callee).

use lean_compiler::{compile, parse};
use lean_vm::cpu::{Stats, prove, verify};
use primitives::field::{F64, F192, g_pow};

const V: u64 = 0b1011_0110;

fn deref_index() -> usize {
    Stats::TABLES.iter().position(|&t| t == "DEREF").expect("a DEREF table")
}

/// The same eight-bit decomposition, once through a `HeapBuf` and once through a
/// `StackBuf`. Every index is compile-time, so the frame run needs no `DEREF` at
/// all where the heap one needs two per bit (the read and the booleanity pin).
#[test]
fn a_frame_bit_buffer_costs_no_deref() {
    let src = |decl: &str, idx: &str| {
        format!(
            "\
def main():
    bits = {decl}
    hint_decompose_bits(bits, {V}, 8)
    acc = 0
    for i in unroll(0, 8):
        b = bits[{idx}]
        bits[{idx}] = b * b
        acc += b * (2 ** i)
    assert acc == {V}
    p = 1
    p[1] = acc
    p[GEN] = 1
    return
"
        )
    };
    let want = [F192::from(F64(V)), F192::from(F64::ONE)];
    let deref = |s: &str| crate::common::mix(s, want)[deref_index()];
    assert_eq!(
        deref(&src("HeapBuf(GEN ** 8)", "GEN ** i")) - deref(&src("StackBuf(8)", "i")),
        16,
        "a frame bit buffer must drop both DEREFs per bit"
    );
}

/// A stack bit run is addressed by CONTIGUITY, so no cell of one may be rewritten
/// to a CSE canonical elsewhere: `hint_log2_ceil` reads `fp+base+k` whatever the
/// substitution says, so a folded-away store would leave it holding nothing. The
/// duplicate `MUL` here comes FIRST, which is the order that would make the store
/// the one dropped.
#[test]
fn a_stack_bit_run_survives_cse() {
    let src = "\
def main():
    src = StackBuf(4)
    hint_witness(src, \"bits\")
    bits = StackBuf(4)
    for i in unroll(0, 4):
        dup = src[i] * src[i]
        bits[i] = src[i] * src[i]
        assert dup == bits[i]
    g_mu = hint_log2_ceil(bits, 4, 0)
    p = 1
    p[1] = g_mu
    p[GEN] = 1
    return
";
    // bits 1011 = 11, whose ceil-log is 4. Executing is enough: a folded-away
    // store leaves its cell unwritten, and the advice then computed off the hole
    // collides with the published public input.
    let mut program = compile(&parse(src).expect("parse"));
    let bits: Vec<F192> = [1u64, 1, 0, 1].iter().map(|&b| F192::from(F64(b))).collect();
    program.set_witness("bits", vec![bits]);
    let want = [F192::from(primitives::field::g_pow(4)), F192::from(F64::ONE)];
    let exec = program.execute(want);
    assert!(
        exec.unconstrained_reads.is_empty(),
        "every cell of the run must still be written"
    );
}

/// `addr(sb)` in a non-`main` function, where naming `fp` costs the two-`DEREF`
/// bounce: the pointer reads the very cells the direct indices wrote, at a
/// compile-time offset and at a runtime one.
#[test]
fn addr_names_the_frame_run() {
    let src = "\
def main():
    w = StackBuf(1)
    hint_witness(w, \"v\")
    out = probe(w[0])
    p = 1
    p[1] = out
    p[GEN] = 1
    return

def probe(v):
    bits = StackBuf(8)
    hint_decompose_bits(bits, v, 8)
    ptr = addr(bits)
    acc = 0
    for i in unroll(0, 8):
        b = bits[i]
        bits[i] = b * b
        acc += b * (2 ** i)
    assert acc == v
    total = 0
    for i in unroll(0, 8):
        total += ptr[GEN ** i] * (2 ** i)
    assert total == v
    for x in mul_range(1, GEN ** 8):
        chk = ptr[x]
        assert chk * chk == chk
    assert addr(bits) == ptr
    return total
";
    let mut program = compile(&parse(src).expect("parse"));
    program.set_witness("v", vec![vec![F192::from(F64(V))]]);
    let want = [F192::from(F64(V)), F192::from(F64::ONE)];
    let (proof, _) = prove(&program, want, lean_vm::pcs::LOG_INV_RATE);
    verify(&program, &want, &proof).expect("the pointer reads the frame run");
    let bad = [F192::from(F64(V + 1)), F192::from(F64::ONE)];
    assert!(verify(&program, &bad, &proof).is_err(), "a wrong value is rejected");
}

/// A store into a cell the program has ALREADY written through an `addr()`
/// pointer is the write-once equality assertion of `zkDSL.md` §Memory, not an
/// assembly copy. `addr()` hands out an ordinary `GAddr`, so a write through it
/// is a `DEREF` whose only `phys`-recorded cell is its source; the run's own
/// cells looked untouched, the store deferred as an alias and emitted nothing,
/// and the program went on to "prove" that one cell held two different values.
#[test]
#[should_panic(expected = "write-once conflict")]
fn a_store_after_a_write_through_addr_still_asserts() {
    let src = "\
def main():
    b = StackBuf(1)
    p = addr(b)
    v = GEN ** 7
    p[1] = v
    b[0] = GEN ** 9
    return
";
    compile(&parse(src).expect("parse")).execute([F192::ZERO; 2]);
}

/// A pointed-at frame run is opaque to CSE: a write through the pointer is a
/// `DEREF` naming no frame cell the pass can see, so a store into one of its
/// cells must not be folded into a canonical elsewhere. Folding it left the cell
/// unwritten, hence prover-chosen, and `unconstrained_reads` could not see it
/// either (the `DEREF` had both sides unwritten, so the deferred fixup marked
/// both written first).
///
/// The two programs differ only in whether the run is pointed at. Without
/// `addr()` the duplicate store is genuinely dead, so it folds; with `addr()` it
/// has to survive.
#[test]
fn a_pointed_at_frame_run_is_opaque_to_cse() {
    let mul = Stats::TABLES.iter().position(|&t| t == "MUL").expect("a MUL table");
    let src = |read: &str| {
        format!(
            "\
def stash(x, y):
    b = StackBuf(1)
    t = x * y
    b[0] = x * y
    {read}
    return t, q

def main():
    hb = HeapBuf(2)
    hb[1] = GEN ** 3
    hb[GEN] = GEN ** 5
    t, q = stash(hb[1], hb[GEN])
    p = 1
    p[1] = t
    p[GEN] = q
    return
"
        )
    };
    let want = [F192::from(g_pow(8)); 2];
    let counts = |s: &str| crate::common::mix(s, want)[mul];
    assert_eq!(
        counts(&src("p = addr(b)\n    q = p[1]")) - counts(&src("q = b[0]")),
        1,
        "the store into a pointed-at run must survive CSE"
    );
}

/// A frame pointer carries the same compile-time bound a `HeapBuf` pointer gets.
/// `check_heap_bound` keys `heap_sizes` by the pointer's own cell, but every
/// `addr()` in a function shares the `fp` cell as its base, so the run has to
/// come from the address's own provenance instead.
#[test]
#[should_panic(expected = "out of bounds")]
fn addr_pointers_are_bounds_checked() {
    let src = "\
def main():
    b = StackBuf(2)
    p = addr(b)
    p[GEN ** 40] = GEN ** 3
    return
";
    compile(&parse(src).expect("parse"));
}

/// The pointer `addr()` hands out addresses the WHOLE frame, not the run it was
/// taken from, so sealing only that run leaves the next `StackBuf` transparent:
/// one off-by-one in a callee writes it, and its later store then defers as an
/// alias and drops the write-once assertion, exactly as before the fix. An
/// escaped frame address therefore seals every run in the function.
#[test]
#[should_panic(expected = "write-once conflict")]
fn an_escaped_frame_address_seals_every_run() {
    let src = "\
def poke(q):
    q[GEN ** 2] = GEN ** 7
    return 0

def main():
    a = StackBuf(2)
    b = StackBuf(1)
    z = poke(addr(a))
    b[0] = GEN ** 9
    assert b[0] == GEN ** 9
    return
";
    compile(&parse(src).expect("parse")).execute([F192::ZERO; 2]);
}
