// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! The evaluation-claim type shared by the zerocheck/lincheck reduction and
//! the PCS.

use primitives::field::F128T;
use crate::lincheck::QuirkyPoint;

/// A claim of the form `ẑ(point) = value` for the witness `z`. Tower-valued:
/// the flock verifier and the downstream PCS run over `F128T`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZClaim {
    pub point: QuirkyPoint,
    pub value: F128T,
}
