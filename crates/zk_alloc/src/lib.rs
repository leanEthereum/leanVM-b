//! Bump-and-reset arena for the prover's transient buffers.
//!
//! One proof allocates tens of gigabytes of short-lived buffers (codewords,
//! folded halves, packed witnesses, Merkle levels) and frees them all before
//! returning. The system allocator hands the big ones out as fresh mappings and
//! returns them on free, so every proof re-pays a soft page fault per page on
//! first touch plus a single-threaded unmap on drop. Measured at the
//! 820-signature XMSS workload, recycling those blocks instead is worth 16% of
//! proving time on an M4 Max and 29% on a Zen 4 host.
//!
//! This arena buys that back. It is **not** a `#[global_allocator]`: only
//! [`ArenaVec`] allocates from it, so a library using it does not impose it on
//! the rest of the process. One reservation is split into per-thread slabs;
//! allocation bumps a thread-local cursor, freeing is a no-op, and
//! [`enter_phase`] resets every slab at once.
//!
//! # Lifetime rule
//!
//! An `ArenaVec` allocated during a phase is **invalidated by the next
//! [`enter_phase`]**. Anything that must outlive a phase (a proof, a cache, a
//! precomputed table) must use the system allocator: a plain `Vec`, or an
//! `ArenaVec` built while no phase is active (which transparently falls back to
//! the system allocator, so `ArenaVec` is safe to use anywhere).
//!
//! Phases must not nest, and only one proof may be in flight per process;
//! [`enter_phase`] asserts both.
//!
//! # Usage
//!
//! ```no_run
//! zk_alloc::enable_arena(); // once, at startup
//! let _phase = zk_alloc::enter_phase(); // bind before the phase's buffers
//! let buf: zk_alloc::ArenaVec<u64> = zk_alloc::ArenaVec::with_capacity(1 << 20);
//! ```

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

mod arena_vec;
mod syscall;

pub use arena_vec::{ArenaVec, alloc_uninit, assume_init};

/// Address space reserved per thread. Apart from the LIFO pop in
/// [`raw_dealloc`], a phase does not reuse a slab byte, so this caps one thread's
/// *cumulative* allocation within one phase rather than its live set, hence the
/// generous size. Address space is free; only touched pages are ever backed, and
/// overflow is not an error (it falls back to the system allocator, and [`stats`]
/// reports how much did).
const SLAB_SIZE: usize = 64 << 30;

/// Slabs beyond the detected parallelism, for threads that are not pool workers
/// (the caller, a helper pool, a tracing thread) but do allocate in a phase.
const SLACK: usize = 8;

/// Minimum alignment for anything at least this large. Keeps every sizeable
/// buffer off a split cache line, which the system allocator gives for free at
/// these sizes and a byte-exact bump pointer would not.
const CACHE_LINE: usize = 64;

/// The alignment a `size`-byte request is actually served at. [`raw_alloc`] and
/// [`raw_dealloc`] must agree on it, or a system buffer would be freed under a
/// layout it was not allocated with.
const fn effective_align(size: usize, align: usize) -> usize {
    if size >= CACHE_LINE && align < CACHE_LINE {
        CACHE_LINE
    } else {
        align
    }
}

/// Round `addr` up to `align`, always a power of two here, so the mask beats the
/// divide `next_multiple_of` would emit on the allocation hot path.
#[inline(always)]
const fn align_up(addr: usize, align: usize) -> usize {
    (addr + align - 1) & !(align - 1)
}

fn max_threads() -> usize {
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| std::thread::available_parallelism().map_or(1, |n| n.get()) + SLACK)
}

fn region_size() -> usize {
    SLAB_SIZE * max_threads()
}

/// Bumped by [`begin_phase`]; a thread resets its slab when its cached
/// `ARENA_GEN` lags, so one store resets every thread without a lock.
static GENERATION: AtomicUsize = AtomicUsize::new(0);
/// Whether a phase is open: allocations route to the arena rather than System.
static ARENA_ACTIVE: AtomicBool = AtomicBool::new(false);
/// Process-wide opt-in. Until [`enable_arena`], phases are inert and `ArenaVec`
/// is a plain system-allocated vector, so a stray [`begin_phase`] in a process
/// that never opted in cannot invalidate anything.
static ARENA_ENGAGED: AtomicBool = AtomicBool::new(false);
/// Base of the reservation, mapped once. Also the arena-vs-system discriminator
/// in [`raw_dealloc`].
static REGION: OnceLock<usize> = OnceLock::new();
/// Slab indices handed out one per thread; `idx >= max_threads()` gets none.
static NEXT_SLAB: AtomicUsize = AtomicUsize::new(0);

/// High-water mark of any single thread's slab use, in bytes.
static HIGH_WATER: AtomicUsize = AtomicUsize::new(0);
/// Bytes that overflowed a slab mid-phase and went to the system allocator.
static OVERFLOW_BYTES: AtomicUsize = AtomicUsize::new(0);
/// Bytes bump-allocated across all threads and phases, accumulated one atomic per
/// thread per phase (at reset), so the hot path stays free of shared writes.
static ARENA_BYTES: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    /// This thread's next allocation address.
    static PTR: Cell<usize> = const { Cell::new(0) };
    /// One past this thread's slab.
    static END: Cell<usize> = const { Cell::new(0) };
    /// This thread's slab base (`0` while unclaimed); the reset target.
    static BASE: Cell<usize> = const { Cell::new(0) };
    /// Last [`GENERATION`] seen; a mismatch means this thread must reset.
    static GEN: Cell<usize> = const { Cell::new(0) };
    /// This thread asked for a slab and there were none left: always use System.
    static NO_SLAB: Cell<bool> = const { Cell::new(false) };
}

fn region() -> usize {
    *REGION.get_or_init(|| {
        let size = region_size();
        // SAFETY: `reserve` returns a page-aligned pointer or null.
        let ptr = unsafe { syscall::reserve(size) };
        assert!(
            !ptr.is_null(),
            "zk_alloc could not reserve {} GiB of address space",
            size >> 30
        );
        // SAFETY: the mapping we just made is live and exactly `size` bytes.
        unsafe { syscall::disable_huge_pages(ptr, size) };
        ptr as usize
    })
}

/// Opt into the arena. Call once at startup, before any proving.
///
/// Until this is called, phases are inert and [`ArenaVec`] is a plain
/// system-allocated vector, which is the right configuration for a
/// memory-constrained host, at the cost of the page-fault churn described in the
/// module docs.
pub fn enable_arena() {
    syscall::retain_system_heap();
    ARENA_ENGAGED.store(true, Ordering::Release);
}

/// Whether [`enable_arena`] has been called.
#[must_use]
pub fn is_enabled() -> bool {
    ARENA_ENGAGED.load(Ordering::Acquire)
}

/// Open a phase: route [`ArenaVec`] allocations to the arena and abandon every
/// slab's contents from the previous phase. No-op until [`enable_arena`].
///
/// # Panics
/// If a phase is already open, whether nested on this thread or opened by
/// another, since only one proof may be in flight per process.
pub(crate) fn begin_phase() {
    if !is_enabled() {
        return;
    }
    let already_open = ARENA_ACTIVE.swap(true, Ordering::Release);
    assert!(
        !already_open,
        "an arena phase is already open: phases must not nest, and only one proof \
         may be in flight per process"
    );
    GENERATION.fetch_add(1, Ordering::Release);
}

/// Close the phase. Pointers into the arena stay valid until the next
/// [`begin_phase`], which is what makes an early return or a panic safe.
pub(crate) fn end_phase() {
    if !is_enabled() {
        return;
    }
    ARENA_ACTIVE.store(false, Ordering::Release);
}

/// Closes the phase on drop, including on an early return or a panic.
#[derive(Debug)]
pub struct PhaseGuard(());

impl Drop for PhaseGuard {
    fn drop(&mut self) {
        end_phase();
    }
}

/// Open a phase and close it on drop. Bind the guard *before* the phase's
/// buffers so it is dropped after them.
///
/// # Panics
/// If a phase is already open: only one proof may be in flight per process.
#[must_use = "the phase ends as soon as the guard is dropped"]
pub fn enter_phase() -> PhaseGuard {
    begin_phase();
    PhaseGuard(())
}

/// What the arena did, for sizing `SLAB_SIZE` and checking that the buffers
/// meant to be arena-backed actually are.
#[derive(Clone, Copy, Debug)]
pub struct Stats {
    /// Phases opened so far.
    pub phases: usize,
    /// Slabs handed out so far, i.e. threads that have allocated in a phase.
    pub threads: usize,
    /// Bytes served from a slab, over all threads and phases. Divided by
    /// [`Stats::phases`] this is the allocation traffic the arena absorbed per
    /// proof; compare it against the workload's total to see what is still
    /// going to the system allocator.
    pub arena_bytes: usize,
    /// Largest single-thread slab use seen at a phase boundary, in bytes.
    /// Compare against [`Stats::slab_size`].
    pub high_water: usize,
    /// Bytes that overflowed a slab mid-phase and fell back to the system
    /// allocator. Nonzero means `SLAB_SIZE` is too small for this workload.
    pub overflow: usize,
    /// The per-thread slab size this build was compiled with.
    pub slab_size: usize,
}

/// Snapshot the arena's accounting. Both `arena_bytes` and `high_water` are
/// updated when a thread resets its slab, so read them after at least one
/// [`enter_phase`] has followed the phase of interest.
#[must_use]
pub fn stats() -> Stats {
    Stats {
        phases: GENERATION.load(Ordering::Relaxed),
        threads: NEXT_SLAB.load(Ordering::Relaxed).min(max_threads()),
        arena_bytes: ARENA_BYTES.load(Ordering::Relaxed),
        high_water: HIGH_WATER.load(Ordering::Relaxed),
        overflow: OVERFLOW_BYTES.load(Ordering::Relaxed),
        slab_size: SLAB_SIZE,
    }
}

impl std::fmt::Display for Stats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let gib = |b: usize| b as f64 / (1u64 << 30) as f64;
        let per_phase = if self.phases == 0 {
            0.0
        } else {
            gib(self.arena_bytes) / self.phases as f64
        };
        write!(
            f,
            "arena: {:.2} GiB/phase over {} phase(s) on {} thread(s); \
             high water {:.2} of {} GiB per slab; overflow {:.2} GiB",
            per_phase,
            self.phases,
            self.threads,
            gib(self.high_water),
            self.slab_size >> 30,
            gib(self.overflow),
        )
    }
}

/// The allocation slow path: this thread's cursor is stale (a new phase, or a
/// first-ever allocation), or its slab is full.
#[cold]
#[inline(never)]
unsafe fn alloc_slow(size: usize, align: usize) -> *mut u8 {
    let generation = GENERATION.load(Ordering::Relaxed);
    if !NO_SLAB.get() && GEN.get() != generation {
        let mut base = BASE.get();
        if base == 0 {
            let idx = NEXT_SLAB.fetch_add(1, Ordering::Relaxed);
            if idx >= max_threads() {
                // More allocating threads than slabs: this one uses System forever.
                NO_SLAB.set(true);
                return unsafe { system_alloc(size, align) };
            }
            base = region() + idx * SLAB_SIZE;
            BASE.set(base);
            END.set(base + SLAB_SIZE);
        } else {
            // Reset: account for what the finished phase used before abandoning it.
            let used = PTR.get() - base;
            HIGH_WATER.fetch_max(used, Ordering::Relaxed);
            ARENA_BYTES.fetch_add(used, Ordering::Relaxed);
        }
        PTR.set(base);
        GEN.set(generation);
        let aligned = align_up(base, align);
        let bumped = aligned + size;
        if bumped <= END.get() {
            PTR.set(bumped);
            return aligned as *mut u8;
        }
    }
    // Slab exhausted (or none owned): fall back, and record it so `stats()` can
    // report that SLAB_SIZE is undersized for this workload.
    OVERFLOW_BYTES.fetch_add(size, Ordering::Relaxed);
    unsafe { system_alloc(size, align) }
}

#[inline]
unsafe fn system_alloc(size: usize, align: usize) -> *mut u8 {
    // SAFETY: `align` is a power of two and `size` is nonzero (callers check).
    unsafe { System.alloc(Layout::from_size_align_unchecked(size, align)) }
}

/// [`ArenaVec`]'s allocator: bump this thread's slab inside a phase, else use
/// the system allocator.
///
/// The cursor is thread-local, so the relaxed loads cannot race: a stale
/// `GENERATION` read only sends this call down [`alloc_slow`].
///
/// # Safety
/// `align` must be a power of two and `size` nonzero. The result is valid for
/// `size` bytes (or null, if the system allocator failed) until the next
/// [`begin_phase`].
#[inline(always)]
pub(crate) unsafe fn raw_alloc(size: usize, align: usize) -> *mut u8 {
    let align = effective_align(size, align);
    if ARENA_ACTIVE.load(Ordering::Relaxed) {
        if GEN.get() == GENERATION.load(Ordering::Relaxed) {
            let aligned = align_up(PTR.get(), align);
            let bumped = aligned + size;
            if bumped <= END.get() {
                PTR.set(bumped);
                return aligned as *mut u8;
            }
        }
        return unsafe { alloc_slow(size, align) };
    }
    unsafe { system_alloc(size, align) }
}

/// The matching free: for an arena pointer, pop the cursor if this was the most
/// recent allocation on this thread and otherwise do nothing (the slab is
/// reclaimed wholesale by the next [`begin_phase`]); for a system pointer, a
/// system free.
///
/// Which one applies is decided by address range, not by a flag stored beside
/// the buffer, which is what lets [`ArenaVec`] carry no allocator parameter and
/// stay a single type whether or not a phase was open when it was built.
///
/// The LIFO pop matters more than it looks. A bump cursor's high-water mark is a
/// phase's *cumulative* allocation, not its live set, so a loop that allocates a
/// temporary and drops it each iteration would otherwise grow the resident set
/// without bound. Popping the top makes that shape cost one buffer. It cannot
/// reclaim an alloc-new-then-free-old rotation, where the freed buffer is not on
/// top.
///
/// # Safety
/// `ptr` came from [`raw_alloc`] with this `size` and `align`.
#[inline(always)]
pub(crate) unsafe fn raw_dealloc(ptr: *mut u8, size: usize, align: usize) {
    let addr = ptr as usize;
    if REGION
        .get()
        .is_some_and(|&base| addr >= base && addr - base < region_size())
    {
        // Pop only within this thread's own slab and only in the phase that
        // allocated it: the cursor is thread-local, so another thread's pointer
        // (or a pointer from a previous phase) must not move it.
        if addr >= BASE.get() && addr + size == PTR.get() && GEN.get() == GENERATION.load(Ordering::Relaxed) {
            PTR.set(addr);
        }
        return;
    }
    let align = effective_align(size, align);
    // SAFETY: the caller guarantees this pointer/layout pair came from
    // `raw_alloc`, and the range check above ruled out the arena.
    unsafe { System.dealloc(ptr, Layout::from_size_align_unchecked(size, align)) };
}
