//! Persistent cache for deterministic XMSS benchmark signatures.
//!
//! The cache grows as needed and is memoized in-process. Its filename binds the
//! parameters, hash construction, and encoding predicate. Loaded signatures are
//! also verified, so stale entries are regenerated from the first invalid one.

use std::collections::hash_map::DefaultHasher;
use std::fs;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::path::PathBuf;
use std::sync::Mutex;
use std::time::Instant;

use primitives::{pretty_f64, pretty_integer};
use rand::SeedableRng;
use rand::rngs::StdRng;
use xmss::*;

type CachedSignature = (XmssPublicKey, XmssSignature);

const SCHEMA_VERSION: u32 = 2;

pub const EPOCH: u32 = 7;
const KEY_START: u32 = 0;
const KEY_END: u32 = 15;

pub fn message() -> Message {
    std::array::from_fn(|i| (i * 5 + 1) as u8)
}

fn compute_signer(index: usize) -> CachedSignature {
    // The index over its full width: a one-byte seed repeats every 256 signers,
    // and a repeated signer is invisible until something deduplicates the set,
    // at which point a batch of 900 quietly becomes one of 256.
    let mut seed = [10u8; 32];
    seed[..8].copy_from_slice(&(index as u64).to_le_bytes());
    let (sk, pk) = xmss_key_gen(seed, KEY_START, KEY_END).expect("keygen");
    let sig = xmss_sign(&mut StdRng::seed_from_u64(index as u64), &sk, &message(), EPOCH).expect("sign");
    (pk, sig)
}

fn hash_fingerprint() -> [Digest; 2] {
    let pp = [0xA5u8; PUBLIC_PARAM_LEN];
    [
        tweak_hash(&pp, TWEAK_TYPE_CHAIN, 1, 2, &[0x5Au8; DIGEST_LEN]),
        tweak_hash(&pp, TWEAK_TYPE_ENCODING, 3, 4, &[0x3Cu8; 2 * STATE_LEN]),
    ]
}

fn encoding_fingerprint() -> (u64, [u8; V]) {
    let pp = [0xA5u8; PUBLIC_PARAM_LEN];
    let msg = message();
    for counter in 0u64.. {
        let mut randomness = [0u8; RANDOMNESS_LEN];
        randomness[..8].copy_from_slice(&counter.to_le_bytes());
        if let Some(digits) = wots_encode(&msg, EPOCH, &pp, &randomness) {
            return (counter, digits);
        }
    }
    unreachable!("some counter randomness encodes")
}

fn footprint() -> u64 {
    let mut hasher = DefaultHasher::new();
    SCHEMA_VERSION.hash(&mut hasher);
    EPOCH.hash(&mut hasher);
    KEY_START.hash(&mut hasher);
    KEY_END.hash(&mut hasher);
    message().hash(&mut hasher);
    (V, W, CHAIN_LENGTH, LOG_LIFETIME, TARGET_SUM, RANDOMNESS_LEN).hash(&mut hasher);
    hash_fingerprint().hash(&mut hasher);
    encoding_fingerprint().hash(&mut hasher);
    hasher.finish()
}

fn cache_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../target/signers-cache")
}

fn cache_path() -> PathBuf {
    cache_dir().join(format!("xmss_signers_{:016x}.bin", footprint()))
}

fn try_load_cache() -> Option<Vec<CachedSignature>> {
    let bytes = fs::read(cache_path()).ok()?;
    let (version, mut signers): (u32, Vec<CachedSignature>) = bincode::deserialize(&bytes).ok()?;
    if version != SCHEMA_VERSION {
        return None;
    }
    let msg = message();
    let valid = signers
        .iter()
        .take_while(|(pk, sig)| xmss_verify(pk, &msg, sig, EPOCH).is_ok())
        .count();
    if valid < signers.len() {
        eprintln!(
            "warning: signers cache {} is stale (signer {valid} of {} no longer verifies); regenerating from there",
            cache_path().display(),
            signers.len()
        );
        signers.truncate(valid);
    }
    Some(signers)
}

fn save_cache(signers: &[CachedSignature]) {
    let path = cache_path();
    if let Some(parent) = path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    let bytes = bincode::serialize(&(SCHEMA_VERSION, signers)).expect("serialize signers cache");
    if let Err(error) = fs::write(&path, &bytes) {
        eprintln!("warning: could not write signers cache to {}: {error}", path.display());
    }
}

fn generate_range(start: usize, end: usize) -> Vec<CachedSignature> {
    let total = end - start;
    let started = Instant::now();
    let mut signers = Vec::with_capacity(total);
    for (done, index) in (start..end).enumerate() {
        signers.push(compute_signer(index));
        print!(
            "\r  generating XMSS signers (one-time, then cached): {}/{}",
            pretty_integer(done + 1),
            pretty_integer(total)
        );
        let _ = std::io::stdout().flush();
    }
    println!(
        "\r  generated {} XMSS in {} s (cached to disk)                ",
        pretty_integer(total),
        pretty_f64(started.elapsed().as_secs_f64())
    );
    signers
}

static POOL: Mutex<Vec<CachedSignature>> = Mutex::new(Vec::new());

pub fn get_signers(n: usize) -> Vec<CachedSignature> {
    let mut pool = POOL.lock().unwrap();
    if pool.len() < n {
        if let Some(disk) = try_load_cache()
            && disk.len() > pool.len()
        {
            *pool = disk;
        }
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
    fn signer_seed_uses_more_than_one_byte() {
        assert_ne!(compute_signer(0).0, compute_signer(256).0);
    }
}
