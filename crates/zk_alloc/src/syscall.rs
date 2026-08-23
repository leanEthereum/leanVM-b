//! Operating system support for the proving arena.

use std::ptr;

/// Reserve `size` bytes of anonymous address space, lazily backed by physical
/// pages. Returns null on failure.
///
/// # Safety
/// Always safe to call. The caller owns the resulting mapping, which is never
/// unmapped (the arena lives for the process).
pub unsafe fn reserve(size: usize) -> *mut u8 {
    let flags = libc::MAP_PRIVATE | libc::MAP_ANON;
    // MAP_NORESERVE keeps Linux from charging the whole sparse reservation
    // against the commit limit; macOS backs anonymous maps lazily regardless.
    #[cfg(target_os = "linux")]
    let flags = flags | libc::MAP_NORESERVE;
    // SAFETY: a null `addr` lets the kernel choose placement; `fd` is -1 for an
    // anonymous mapping.
    let ret = unsafe { libc::mmap(ptr::null_mut(), size, libc::PROT_READ | libc::PROT_WRITE, flags, -1, 0) };
    if ret == libc::MAP_FAILED {
        ptr::null_mut()
    } else {
        ret.cast::<u8>()
    }
}

/// Ask the kernel not to use transparent huge pages for `[ptr, ptr + size)`.
///
/// # Safety
/// `ptr`/`size` must describe a live mapping from [`reserve`].
pub unsafe fn disable_huge_pages(ptr: *mut u8, size: usize) {
    #[cfg(target_os = "linux")]
    // SAFETY: the caller guarantees `[ptr, ptr + size)` is a live mapping.
    unsafe {
        libc::madvise(ptr.cast::<libc::c_void>(), size, libc::MADV_NOHUGEPAGE);
    }
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (ptr, size);
    }
}

/// Stop glibc from returning freed memory to the kernel.
///
/// No-op outside Linux.
pub fn retain_system_heap() {
    #[cfg(target_os = "linux")]
    // SAFETY: `mallopt` only adjusts allocator tuning parameters.
    unsafe {
        libc::mallopt(libc::M_TRIM_THRESHOLD, -1);
        libc::mallopt(libc::M_MMAP_MAX, 0);
    }
}
