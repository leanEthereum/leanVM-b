use lean_compiler::{compile, parse};
use primitives::field::F192;

#[test]
fn transcript_helpers_are_ordinary_nested_inline_zkdsl() {
    let src = r#"
from snark_lib import *

Y = f192(0, 1, 0)

@inline
def challenge_from_state(state):
    lo = StackBuf(2)
    hi = StackBuf(2)
    hint_f192_limbs(lo, state[0])
    hint_f192_limbs(hi, state[1])
    pack64x2_into(lo[0], lo[1], state[0])
    pack64x2_into(hi[0], hi[1], state[1])
    return lo[0] + lo[1] * Y + hi[0] * Y * Y

@inline
def sponge_compress(state, scalar, tail, out):
    limbs = StackBuf(3)
    hint_f192_limbs(limbs, scalar)
    block = StackBuf(2)
    pack64x2_into(limbs[0], limbs[1], block[0])
    pack64x2_into(limbs[2], tail, block[1])
    assert scalar == limbs[0] + limbs[1] * Y + limbs[2] * Y * Y
    blake3(state, block, out)
    return

@inline
def observe(state, scalar):
    out = StackBuf(2)
    sponge_compress(state, scalar, 13, out)
    return out

def main():
    state = StackBuf(2)
    state[0] = f192(1, 2, 0)
    state[1] = f192(3, 4, 0)
    out = observe(state, f192(5, 6, 7))
    challenge = challenge_from_state(out)
    assert challenge == challenge
    return
"#;
    let program = compile(&parse(src).expect("parse transcript helpers"));
    program.execute([F192::ZERO; 2]);
}
