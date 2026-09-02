//! leanVM aggregates XMSS and SPHINCS signatures into one proof.
//!
//! Release only: the zkDSL compiler [`setup_verifier`] runs overflows the debug stack.
//!
//! End to end in [`tests/api.rs`](https://github.com/leanEthereum/leanVM-b/blob/main/tests/api.rs).

pub use rec_aggregation::{
    AggregateSignature, AggregateVerifyError, AggregationError, MAX_CHILDREN, MAX_EPOCHS, MAX_KEYS, aggregate,
};

pub use lean_vm::{
    cpu::CpuError,
    pcs::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE},
};

pub mod xmss {
    pub use ::xmss::{
        Digest, Epoch, LOG_LIFETIME, MESSAGE_LEN, Message, PUB_KEY_SIZE, PublicParam, SIG_SIZE, WotsSignature,
        XmssKeyGenError, XmssPublicKey, XmssSecretKey, XmssSignError, XmssSignature, XmssVerifyError, key_gen, sign,
        verify,
    };
}

pub mod sphincs {
    pub use ::sphincs::{
        Digest, FtsOpening, MESSAGE_LEN, Message, PUB_KEY_SIZE, PublicParam, SECRET_KEY_SIZE, SIG_SIZE,
        SphincsPublicKey, SphincsSecretKey, SphincsSignError, SphincsSignature, SphincsVerifyError, key_gen,
        key_gen_from, sign, verify,
    };
}

pub use rand;

/// Call once before verifying an aggregate signature. Idempotent, and
/// [`setup_prover`] does it for you.
pub fn setup_verifier() {
    lean_vm::init_prover_pool();
    rec_aggregation::warm_up();
}

/// Call once before [`aggregate`].
///
/// There is one arena per process, so only one [`aggregate`] call may run at a
/// time in a process: to aggregate in parallel, use separate processes.
///
/// For machine with small RAM, where arena allocation does not fit, set the environment
/// variable `LEANVM_NO_ARENA` to 1, at the cost of slower proving.
pub fn setup_prover() {
    setup_verifier();
    lean_vm::init_prover();
}
