//! Per-block R1CS encoders (vendored BLAKE3 subset). Upstream also has keccak /
//! keccak3 / sha2 and the chain glue; only `blake3` + the shared `common`
//! bit-packing/matrix utilities are vendored here.

pub mod blake3;
pub mod common;
