use lean_compiler::{compile, parse};
use primitives::field::F64;

#[test]
fn transcript_helpers_are_ordinary_nested_inline_zkdsl() {
    let src = r#"
from snark_lib import *

@inline
def challenge_from_state(state):
    out = [state[0], state[1], state[2]]
    return out

@inline
def sponge_compress(state, scalar, tail, out):
    block = [scalar[0], scalar[1], scalar[2], tail]
    blake3(state, block, out)
    return

@inline
def observe(state, scalar):
    out = StackBuf(4)
    sponge_compress(state, scalar, 13, out)
    return out

def main():
    state = [1, 2, 3, 4]
    scalar = [5, 6, 7]
    out = observe(state, scalar)
    challenge = challenge_from_state(out)
    doubled = StackBuf(3)
    add_ext(challenge, challenge, doubled)
    assert doubled[0] == 0
    assert doubled[1] == 0
    assert doubled[2] == 0
    return
"#;
    let program = compile(&parse(src).expect("parse transcript helpers"));
    program.execute([F64::ZERO; 4]);
}
