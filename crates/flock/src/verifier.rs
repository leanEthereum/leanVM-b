// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Errors of the R1CS reduction (zerocheck + lincheck + PCS opening).

use crate::lincheck;

use crate::zerocheck;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    Zerocheck(zerocheck::VerifyError),
    Lincheck(lincheck::VerifyError),
    PcsAb(::pcs::VerifyError),
}
