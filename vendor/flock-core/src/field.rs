// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Binary field arithmetic.
//!
//! - [`F8`]   — GF(2^8) with AES polynomial x^8 + x^4 + x^3 + x + 1
//! - [`F128`] — GF(2^128) in GHASH form, polynomial x^128 + x^7 + x^2 + x + 1
//! - [`F256Unreduced`] — 256-bit unreduced GHASH products, for deferred reduction
//! - [`F192`] — GF((2^64)^3): degree-3 tower over GF(2^64), for >128-bit security
//! - [`F192Unreduced`] — its deferred-reduction accumulator

pub mod gf2_64;
pub mod iso_f128;
pub mod gf2_128;
pub mod gf2_64x3;
pub mod gf2_8;
pub mod phi8;
pub mod tower_f128;

pub use gf2_8::F8;
pub use gf2_64::F64;
pub use iso_f128::{ghash_to_tower, tower_to_ghash};
pub use gf2_64x3::{F192, F192Unreduced};
pub use gf2_128::{F128, F256Unreduced, mul_by_x};
pub use phi8::{PHI_8_TABLE, phi8};
pub use tower_f128::F128T;
