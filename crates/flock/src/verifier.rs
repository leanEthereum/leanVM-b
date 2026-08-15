// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Errors of the R1CS reduction (zerocheck + lincheck + PCS opening).

use crate::lincheck;

use crate::zerocheck;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    Zerocheck(zerocheck::VerifyError),
    Lincheck(lincheck::VerifyError),
    /// The stream ran out while reading the `c` family's bit slices.
    CSlicesTruncated,
    /// Those slices do not combine to the zerocheck's `c_eval` under the φ8
    /// Lagrange weights at `z`.
    CSlicesMismatch,
}
