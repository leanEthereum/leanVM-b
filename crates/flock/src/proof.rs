// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The evaluation-claim type shared by the zerocheck/lincheck reduction and
//! the PCS.

use crate::lincheck::QuirkyPoint;
use primitives::field::F192;

/// A claim of the form `ẑ(point) = value` for the witness `z`. Tower-valued:
/// the flock verifier and the downstream PCS run over `F192`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZClaim {
    pub point: QuirkyPoint,
    pub value: F192,
}
