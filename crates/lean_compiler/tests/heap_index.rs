//! A compile-time heap index that folds to a non-g-power field constant
//! (`buf[0]`, `buf[2]`, an integer loop var leaking in from a StackBuf
//! conversion) can never name a heap cell (cell k lives at `buf · g^k`) and
//! used to survive to proving time as a wild-pointer DEREF. It must be a
//! compile-time error.

use lean_compiler::{compile, parse};

#[test]
#[should_panic(expected = "not a g-power")]
fn integer_heap_index_is_rejected() {
    let src = "\
def main():
    b = HeapBuf(4)
    b[1] = 3
    b[GEN] = 5
    x = 0
    for k in unroll(0, 2):
        p = 1
        p[GEN ** k] = b[k]
    return
";
    compile(&parse(src).expect("parse"));
}
