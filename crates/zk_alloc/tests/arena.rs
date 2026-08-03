//! The arena is driven explicitly: the process keeps its own allocator, and only
//! [`ArenaVec`] buffers live in a slab. Everything else must be untouched by a
//! phase reset — that is the property that lets a library use the arena without
//! imposing it on its consumers.

use std::sync::{Mutex, MutexGuard};

use zk_alloc::{ArenaVec, arena_vec, begin_phase, enable_arena, end_phase, enter_phase, stats};

const N: usize = 4096;

/// Phases are process-global and refuse to nest, so the tests in this binary
/// must not overlap. Opting the arena in here too keeps each test standalone.
fn exclusive() -> MutexGuard<'static, ()> {
    static LOCK: Mutex<()> = Mutex::new(());
    enable_arena();
    LOCK.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

#[test]
fn phase_reset_recycles_the_slab_and_spares_the_system_heap() {
    let _serial = exclusive();

    // One arena allocation on this thread claims its slab at the base.
    begin_phase();
    let mut first: ArenaVec<u64> = ArenaVec::with_capacity(N);
    first.resize(N, 0xABCD); // fits the reservation, so the pointer stays put
    let p1 = first.as_ptr() as usize;
    end_phase();

    // Allocated with the arena closed: goes to the system allocator and must
    // survive the next reset.
    let canary = vec![0xAB_u8; 8192];

    // The slab resets, so an identically shaped buffer lands at the same address.
    begin_phase();
    let mut second: ArenaVec<u64> = ArenaVec::with_capacity(N);
    second.resize(N, 0x1234);
    let p2 = second.as_ptr() as usize;
    end_phase();

    assert_eq!(p1, p2, "a phase reset must recycle the slab");
    assert!(
        canary.iter().all(|&b| b == 0xAB),
        "the reset corrupted a system allocation"
    );
    assert!(second.iter().all(|&x| x == 0x1234));

    // With no phase open, ArenaVec is an ordinary system-allocated vector.
    let mut outside: ArenaVec<u64> = ArenaVec::new();
    outside.extend(0..1000);
    assert_eq!(outside.iter().sum::<u64>(), (0..1000).sum());
}

#[test]
fn guard_closes_the_phase_on_unwind() {
    let _serial = exclusive();
    let panicked = std::panic::catch_unwind(|| {
        let _phase = enter_phase();
        let _v: ArenaVec<u8> = ArenaVec::filled(7, 32);
        panic!("boom");
    });
    assert!(panicked.is_err());
    // If the guard had leaked the open phase, this would trip the nesting assert.
    let _phase = enter_phase();
}

#[test]
fn growth_preserves_contents_across_reallocation() {
    let _serial = exclusive();
    let _phase = enter_phase();
    let mut v: ArenaVec<usize> = ArenaVec::new();
    for i in 0..10_000 {
        v.push(i);
    }
    assert_eq!(v.len(), 10_000);
    assert!(v.iter().copied().eq(0..10_000));
}

#[test]
fn zeroed_clears_a_recycled_slab() {
    let _serial = exclusive();
    {
        let _phase = enter_phase();
        let mut dirty: ArenaVec<u64> = ArenaVec::filled(!0, N);
        dirty[0] = 1; // keep the buffer live and written
    }
    {
        // Same shape, same slab bytes: `zeroed` must not inherit them.
        let _phase = enter_phase();
        // SAFETY: all-zero is a valid u64.
        let fresh: ArenaVec<u64> = unsafe { ArenaVec::zeroed(N) };
        assert!(fresh.iter().all(|&x| x == 0), "zeroed must overwrite stale slab bytes");
    }
}

#[test]
fn drop_runs_for_elements_that_need_it() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static DROPS: AtomicUsize = AtomicUsize::new(0);

    struct Noisy(#[allow(dead_code)] usize);
    impl Drop for Noisy {
        fn drop(&mut self) {
            DROPS.fetch_add(1, Ordering::Relaxed);
        }
    }

    let _serial = exclusive();
    let _phase = enter_phase();
    {
        let mut v: ArenaVec<Noisy> = ArenaVec::new();
        for i in 0..100 {
            v.push(Noisy(i));
        }
        v.truncate(40);
        assert_eq!(DROPS.load(Ordering::Relaxed), 60, "truncate drops the tail");
    }
    assert_eq!(DROPS.load(Ordering::Relaxed), 100, "drop releases the rest");
}

#[test]
fn zero_sized_elements_never_allocate() {
    let _serial = exclusive();
    let _phase = enter_phase();
    let mut v: ArenaVec<()> = ArenaVec::new();
    for _ in 0..1000 {
        v.push(());
    }
    assert_eq!(v.len(), 1000);
    assert_eq!(v.capacity(), usize::MAX);
}

#[test]
fn macro_matches_vec() {
    let _serial = exclusive();
    let _phase = enter_phase();
    let empty: ArenaVec<u8> = arena_vec![];
    assert!(empty.is_empty());
    assert_eq!(*arena_vec![9u8; 3], [9, 9, 9]);
    assert_eq!(*arena_vec![1u8, 2, 3], [1, 2, 3]);
}

#[test]
fn stats_report_a_bounded_slab() {
    let _serial = exclusive();
    {
        let _phase = enter_phase();
        let _v: ArenaVec<u64> = ArenaVec::with_capacity(1 << 16);
    }
    // The high-water mark is recorded when a thread resets, so take a second phase.
    let _phase = enter_phase();
    let _v: ArenaVec<u64> = ArenaVec::with_capacity(8);
    let s = stats();
    assert!(s.threads >= 1);
    assert!(s.high_water <= s.slab_size, "high water must fit the slab");
    assert_eq!(s.overflow, 0, "this test allocates far too little to overflow");
}
