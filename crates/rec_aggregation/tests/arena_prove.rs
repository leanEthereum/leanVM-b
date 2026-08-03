//! Proving with the arena engaged, across several phases in one process.
//!
//! This is the test that would catch the arena's one real failure mode: a buffer
//! that outlives the phase that allocated it. A phase reset does not clear or
//! unmap anything, so a stale `ArenaVec` keeps reading plausible-looking bytes —
//! the previous proof's — and the symptom is a proof that no longer verifies
//! rather than a crash. Every assertion below is therefore an end-to-end
//! verification, not a memory check.
//!
//! It lives in its own integration-test binary on purpose: phases are
//! process-global and refuse to nest, so a test that opens one must not share a
//! process with another that does.

use primitives::bench::Plan;

/// Prove the XMSS aggregation three times over (one warmup plus two measured
/// passes) with the arena on. Each pass verifies its own proof and checks that a
/// tampered public input is rejected, so a buffer surviving into the next phase
/// shows up as a verification failure here.
#[test]
fn repeated_proofs_survive_phase_resets() {
    lean_vm::init_prover();
    assert!(
        zk_alloc::is_enabled(),
        "this test is meaningless unless the arena is engaged"
    );

    rec_aggregation::run_xmss_aggregation(3, lean_vm::pcs::LOG_INV_RATE, Plan::new(2, 0));

    let stats = zk_alloc::stats();
    assert!(stats.phases >= 3, "expected one phase per proof, got {stats:?}");
    assert!(
        stats.arena_bytes > 0,
        "no buffer reached the arena, so nothing was actually exercised: {stats:?}"
    );
    assert_eq!(
        stats.overflow, 0,
        "a slab overflowed into the system allocator, so SLAB_SIZE is undersized: {stats:?}"
    );
}
