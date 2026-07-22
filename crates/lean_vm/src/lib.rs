//! leanVM-b — arithmetization of a minimal zkVM (see `doc.tex` and
//! `misc/transition-to-64-bits.tex`).
//!
//! Machine words are `c0 + c1*y ∈ E = K[y]/(y^2 + x*y + 1)`.
//! Addresses, pc/fp, read counters, and logical indices live in
//! `K = GF(2^64)`; indices are powers of a fixed generator `g`, so incrementing
//! one is a multiplication by `g`, a free virtual operation. Every physical
//! witness column is K-valued (an E-valued word is two K-lane columns) and is
//! committed directly by a dense multilinear PCS. Challenges and transcript
//! scalars live in E, so interactive error terms keep their `c/2^128` form.
//!
//! - [`transcript`] — the shared Fiat–Shamir transcript (re-exported from `fiat_shamir`).
//! - [`pcs`] — `K`-committed witness, `E`-opened, via the stacked Ligerito-K (§3).
//! - [`witness`] — `K`-valued columns stacked into one committed witness.
//! - [`gkr`] — the grand product via GKR (§4.3), balancing the bus.
//! - [`leaf`] — the shared bus: grand-product balance, decomposed to per-column claims (§4.2–§4.4, §5).
//! - [`constraints`] — the per-table degree-2 field zerocheck (§4.1).
//! - [`tables`] — the instruction tables (columns, flushes, constraints).
//! - [`cpu`] — whole-program assembly, control flow, and the prove/verify entry points.
//! - [`blake3_flock`] — the `BLAKE3` glue: flock's R1CS validity proof over the same commitment.
//! - [`vmhash`]: VM-native hashing (one-block compression and standard BLAKE3 slice hashing).

pub mod blake3_flock;
pub mod constraints;
pub mod cpu;
pub mod gkr;
pub mod leaf;
pub mod pcs;
pub mod tables;
pub mod transcript;
pub mod vmhash;
pub mod witness;

/// Build rayon's global thread pool with every worker pinned to a **performance
/// core** (macOS QoS `USER_INTERACTIVE`), so the prover's fork-join stages are not
/// dragged by efficiency-core stragglers at their barriers. The thread *count*
/// still follows `RAYON_NUM_THREADS` (or rayon's default); this only fixes which
/// cores the workers are scheduled on.
///
/// Idempotent and best-effort: call it **once at program/test start, before any
/// other rayon use** (rayon's global pool is built on first use — once built, this
/// is a no-op and the QoS hint does not apply). On non-macOS it is a plain pool.
pub fn init_prover_pool() {
    use std::sync::Once;
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        let builder = rayon::ThreadPoolBuilder::new().spawn_handler(|thread| {
            std::thread::Builder::new().spawn(move || {
                #[cfg(target_os = "macos")]
                set_qos_user_interactive();
                thread.run();
            })?;
            Ok(())
        });
        // Fails only if the global pool is already built — then we silently keep it.
        let _ = builder.build_global();
    });
}

/// Pin the calling thread to a performance core by requesting the
/// `USER_INTERACTIVE` QoS class (macOS): the scheduler keeps `USER_INTERACTIVE`
/// work off the efficiency cores. `QOS_CLASS_USER_INTERACTIVE = 0x21`.
#[cfg(target_os = "macos")]
fn set_qos_user_interactive() {
    const QOS_CLASS_USER_INTERACTIVE: u32 = 0x21;
    unsafe extern "C" {
        fn pthread_set_qos_class_self_np(qos_class: u32, relative_priority: i32) -> i32;
    }
    // SAFETY: a libSystem call that only adjusts this thread's scheduling class.
    unsafe {
        pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
    }
}

/// Target soundness of the whole proof, in bits. Every round is designed to clear
/// this: the PCS runs the Ligerito `Secure` profile ([`pcs::PROFILE`], 120-bit),
/// and the bus grand product grinds up to it before its multiset challenge
/// ([`leaf`]). Raising it means bumping BOTH (a stronger profile and more grinding).
pub const SECURITY_BITS: u32 = 120;

/// Below this many parallelizable items a pass runs serially: rayon's fan-out
/// overhead is not worth it for small inputs. Shared by [`constraints`], [`gkr`], [`leaf`].
pub(crate) const PAR_THRESHOLD: usize = 1 << 11;

pub(crate) use primitives::{log2_ceil_usize, log2_strict_usize};
