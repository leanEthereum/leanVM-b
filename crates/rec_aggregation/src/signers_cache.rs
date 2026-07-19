//! Disk cache for the XMSS signatures the aggregation benchmark consumes.
//!
//! Generating a signer (a full `xmss_key_gen` over slots `0..=15` plus one
//! grinding `xmss_sign`, ~2^14 encode attempts) is the untimed setup cost of
//! [`crate::run_xmss_aggregation`]; for large batches it dwarfs the proving we
//! actually want to measure. Every signer is a pure function of its index and
//! the fixed parameters below, so we generate each one once, store the whole
//! batch to disk, and reload it on subsequent runs.
//!
//! The on-disk file is a growing *pool*: a request for `n` signers reuses (and
//! extends) whatever is already cached, so bumping `LEANVM_XMSS_N` never
//! regenerates the signers a smaller run already produced. The pool is also
//! memoized in-process, so repeated calls within one run touch the disk once.
//!
//! Cache location: `<workspace>/target/signers-cache/` (already git-ignored).
//! The filename carries a footprint of everything that determines the signers —
//! not just the declared parameters but a known-answer of the hash construction
//! itself (see [`hash_fingerprint`]), so a branch that changes the digests
//! (e.g. a different field width in the Merkle-Damgard IV) without touching a
//! single constant still lands in a fresh file rather than mis-loading the
//! other branch's signers. Bump [`SCHEMA_VERSION`] to force regeneration by hand.

use std::collections::hash_map::DefaultHasher;
use std::fs;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::path::PathBuf;
use std::sync::Mutex;
use std::time::Instant;

use primitives::pretty_integer;
use rand::SeedableRng;
use rand::rngs::StdRng;
use xmss::*;

/// A cached signer: its public key and one signature over [`message`] at [`SLOT`].
type CachedSignature = (XmssPublicKey, XmssSignature);

/// Bump to invalidate every existing cache file by hand.
const SCHEMA_VERSION: u32 = 1;

/// The slot every benchmark signature is produced (and verified) at.
pub const SLOT: u32 = 7;
/// Key validity range passed to `xmss_key_gen` (inclusive).
const KEY_START: u32 = 0;
const KEY_END: u32 = 15;

/// The single message every signer signs.
pub fn message() -> Message {
    std::array::from_fn(|i| (i * 5 + 1) as u8)
}

/// Deterministically generate signer `index`. Identical to the inline loop the
/// benchmark used before caching, so cached and freshly-generated runs are
/// indistinguishable.
fn compute_signer(index: usize) -> CachedSignature {
    let seed = [10 + index as u8; 32];
    let (sk, pk) = xmss_key_gen(seed, KEY_START, KEY_END).expect("keygen");
    let sig = xmss_sign(&mut StdRng::seed_from_u64(index as u64), &sk, &message(), SLOT).expect("sign");
    (pk, sig)
}

/// A known-answer fingerprint of the *hash construction* the signers are built
/// from. The declared constants below can stay fixed while the digests change
/// underneath: switching the Merkle-Damgard IV's size field on another branch
/// Changing the field encoding leaves V, W, DIGEST_LEN, ... untouched yet makes
/// every signer incompatible. Folding a fixed test vector of the real primitives
/// into [`footprint`] lands such a change in a *different* cache file, so a run
/// on one branch never loads (and then panics on) another branch's signers — the
/// two caches simply coexist. Two BLAKE3 compressions; negligible next to
/// generating even one signer.
fn hash_fingerprint() -> [Digest; 2] {
    let pp = [0xA5u8; PUBLIC_PARAM_LEN];
    [
        // Single-block path (chain steps, Merkle nodes).
        tweak_hash(&pp, TWEAK_TYPE_CHAIN, 1, 2, &[0x5Au8; DIGEST_LEN]),
        // Multi-block path, whose IV carries the absorbed size in the exponent
        // of the VM field's generator — precisely the piece that differs across
        // the field-width branches.
        md_tweak_hash(&pp, TWEAK_TYPE_ENCODING, 3, 4, &[0x3Cu8; 2 * STATE_LEN]),
    ]
}

/// 64-bit fingerprint of everything that determines the signers. Any change
/// (slot, key range, message, the XMSS structural constants, or the hash
/// construction itself via [`hash_fingerprint`]) yields a new filename, so stale
/// caches are silently bypassed rather than mis-loaded.
fn footprint() -> u64 {
    let mut h = DefaultHasher::new();
    SCHEMA_VERSION.hash(&mut h);
    SLOT.hash(&mut h);
    KEY_START.hash(&mut h);
    KEY_END.hash(&mut h);
    message().hash(&mut h);
    (V, W, CHAIN_LENGTH, LOG_LIFETIME, TARGET_SUM, RANDOMNESS_LEN).hash(&mut h);
    hash_fingerprint().hash(&mut h);
    h.finish()
}

fn cache_dir() -> PathBuf {
    // CARGO_MANIFEST_DIR is <workspace>/crates/rec_aggregation.
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../target/signers-cache")
}

fn cache_path() -> PathBuf {
    cache_dir().join(format!("xmss_signers_{:016x}.bin", footprint()))
}

/// Load the pool from disk, treating any failure (missing file, read error,
/// decode error, schema mismatch) as an empty cache.
fn try_load_cache() -> Option<Vec<CachedSignature>> {
    let bytes = fs::read(cache_path()).ok()?;
    let (version, signers): (u32, Vec<CachedSignature>) = bincode::deserialize(&bytes).ok()?;
    (version == SCHEMA_VERSION).then_some(signers)
}

fn save_cache(signers: &[CachedSignature]) {
    let path = cache_path();
    if let Some(parent) = path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    let bytes = bincode::serialize(&(SCHEMA_VERSION, signers)).expect("serialize signers cache");
    if let Err(e) = fs::write(&path, &bytes) {
        eprintln!("warning: could not write signers cache to {}: {e}", path.display());
    }
}

/// Generate signers for indices `start..end`, printing one-time progress.
fn generate_range(start: usize, end: usize) -> Vec<CachedSignature> {
    let total = end - start;
    let t = Instant::now();
    let mut out = Vec::with_capacity(total);
    for (done, index) in (start..end).enumerate() {
        out.push(compute_signer(index));
        print!(
            "\r  generating XMSS signers (one-time, then cached): {}/{}",
            pretty_integer(done + 1),
            pretty_integer(total)
        );
        let _ = std::io::stdout().flush();
    }
    println!(
        "\r  generated {} XMSS in {:.2}s (cached to disk)                ",
        pretty_integer(total),
        t.elapsed().as_secs_f32()
    );
    out
}

static POOL: Mutex<Vec<CachedSignature>> = Mutex::new(Vec::new());

/// The `n` benchmark signers, each `(public key, signature over [`message`] at
/// [`SLOT`])`. Served from the in-process pool, then disk, generating (and
/// caching) only the signers not already available.
pub fn get_signers(n: usize) -> Vec<CachedSignature> {
    let mut pool = POOL.lock().unwrap();
    if pool.len() < n {
        // The disk pool may already hold a superset of what we have in memory.
        if let Some(disk) = try_load_cache()
            && disk.len() > pool.len()
        {
            *pool = disk;
        }
        // Extend past whatever the disk gave us, then persist the larger pool.
        if pool.len() < n {
            let mut fresh = generate_range(pool.len(), n);
            pool.append(&mut fresh);
            save_cache(&pool);
        }
    }
    pool[..n].to_vec()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cached_signers_verify_and_are_deterministic() {
        // A small request, then a larger one that must reuse the first as a
        // prefix (the pool grows; earlier signers are never regenerated).
        let small = get_signers(2);
        let large = get_signers(5);
        assert_eq!(large[..small.len()], small[..]);

        let msg = message();
        for (i, (pk, sig)) in large.iter().enumerate() {
            xmss_verify(pk, &msg, sig, SLOT).unwrap_or_else(|e| panic!("cached signer {i} failed to verify: {e:?}"));
        }
    }
}
