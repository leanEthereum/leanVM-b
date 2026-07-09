//! leanVM-b — arithmetization of a minimal binary-field zkVM (see `doc.tex` and
//! `misc/transition-to-64-bits.tex`).
//!
//! Every machine value is an element of `K = GF(2^64)`, and logical indices are
//! powers of a fixed generator `g`, so incrementing an index is a multiplication
//! by `g` — a free virtual operation needing no addition gadget. The witness is
//! `K`-valued and committed directly by a dense multilinear PCS (no
//! bit-decomposition); every challenge and transcript scalar lives in the
//! degree-2 tower `E = GF(2^128) = K[y]`, so all interactive error terms keep
//! their `c/2^128` form.
//!
//! - [`compiler`] — Python-like zkDSL front end: parse → lower to the ISA → [`cpu::Program`].
//! - [`field`] — `K`/`E` re-exports, the generator `g`, and g-power helpers.
//! - [`transcript`] — Fiat–Shamir transcript (observe-and-fold in one op).
//! - [`multilinear`] — eq polynomial, folding, MLE and Lagrange evaluation (mixed `K`×`E`).
//! - [`pcs`] — `K`-committed witness, `E`-opened, via flock's Ligerito-K (§3).
//! - [`witness`] — `K`-valued columns stacked into one committed witness.
//! - [`gkr`] — the grand product via GKR (§4.3), balancing the bus.
//! - [`leaf`] — the shared bus: grand-product balance, decomposed to per-column claims (§4.2–§4.4, §5).
//! - [`constraints`] — the per-table degree-2 field zerocheck (§4.1).
//! - [`tables`] — the six instruction tables (columns, flushes, constraints).
//! - [`cpu`] — whole-program assembly, control flow, and the prove/verify entry points.
//! - [`blake3_flock`] — the `BLAKE3` glue: flock's R1CS validity proof over the same commitment.

pub mod blake3_flock;
pub mod compiler;
pub mod constraints;
pub mod cpu;
pub mod field;
pub mod gkr;
pub mod leaf;
pub mod multilinear;
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

/// `log2(n)` for a power-of-two `n`; panics otherwise.
pub(crate) fn log2_strict_usize(n: usize) -> usize {
    assert!(n.is_power_of_two(), "not a power of two: {n}");
    n.trailing_zeros() as usize
}

/// `ceil(log2(n))`.
pub(crate) const fn log2_ceil_usize(n: usize) -> usize {
    (usize::BITS - n.saturating_sub(1).leading_zeros()) as usize
}
