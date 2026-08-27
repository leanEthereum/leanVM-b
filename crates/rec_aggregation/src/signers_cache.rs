//! Persistent cache for deterministic benchmark signatures, one file per
//! scheme.
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

/// The epoch every cached XMSS signature was made at. SPHINCS has none.
pub const XMSS_EPOCH: u32 = 3_000_000_007;
const KEY_START: u32 = 3_000_000_000;
const KEY_END: u32 = 3_000_000_015;

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
    let sig = xmss_sign(&mut StdRng::seed_from_u64(index as u64), &sk, &message(), XMSS_EPOCH).expect("sign");
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
        if let Some(digits) = wots_encode(&msg, XMSS_EPOCH, &pp, &randomness) {
            return (counter, digits);
        }
    }
    unreachable!("some counter randomness encodes")
}

fn footprint() -> u64 {
    let mut hasher = DefaultHasher::new();
    SCHEMA_VERSION.hash(&mut hasher);
    XMSS_EPOCH.hash(&mut hasher);
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
        .take_while(|(pk, sig)| xmss_verify(pk, &msg, sig, XMSS_EPOCH).is_ok())
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

/// A SPHINCS signer, generated the same way, with the message it signed: each
/// SPHINCS signer carries its own, where the XMSS ones share one. Signing is
/// stateless, so unlike XMSS there is no epoch and no key range: one key
/// answers for every index.
type CachedSphincsSignature = (sphincs::PublicKey, sphincs::Message, sphincs::Signature);

/// Signer `index`'s own message, distinct from every other's and from the shared
/// XMSS [`message`], so a test that mixed them up would fail rather than pass.
pub fn sphincs_message(index: usize) -> sphincs::Message {
    let mut msg = [0u8; sphincs::MESSAGE_LEN];
    msg[..8].copy_from_slice(&(index as u64).to_le_bytes());
    msg[8..].copy_from_slice(&[0xC5; sphincs::MESSAGE_LEN - 8]);
    msg
}

/// One cached SPHINCS signer, as fixed-size bytes: the scheme's own
/// serializations, so nothing here has to agree with a derived one.
const SPHINCS_RECORD: usize = sphincs::PUB_KEY_SIZE + sphincs::MESSAGE_LEN + sphincs::SIG_SIZE;

fn compute_sphincs_signer(index: usize) -> CachedSphincsSignature {
    let mut rng = StdRng::seed_from_u64(0x5F1A_C500 ^ index as u64);
    let (secret_key, public_key) = sphincs::key_gen(&mut rng);
    let message = sphincs_message(index);
    let signature = sphincs::sign(&mut rng, &secret_key, &message).expect("sign");
    (public_key, message, signature)
}

fn sphincs_footprint() -> u64 {
    let mut hasher = DefaultHasher::new();
    SCHEMA_VERSION.hash(&mut hasher);
    // The record layout and the per-signer messages, so a change to either
    // invalidates the file rather than being read back as another scheme's.
    SPHINCS_RECORD.hash(&mut hasher);
    sphincs_message(0).hash(&mut hasher);
    sphincs_message(1).hash(&mut hasher);
    (
        sphincs::V,
        sphincs::W,
        sphincs::TARGET_SUM,
        sphincs::D,
        sphincs::HEIGHTS,
        sphincs::A,
        sphincs::K,
    )
        .hash(&mut hasher);
    // The tweakable hash itself, so a change to it invalidates the file.
    sphincs::th(
        &[0xA5; sphincs::PUBLIC_PARAM_LEN],
        &sphincs::tweak(1, 2, 3, 4, 5),
        &[0x3C; 16],
    )
    .hash(&mut hasher);
    hasher.finish()
}

fn sphincs_cache_path() -> PathBuf {
    cache_dir().join(format!("sphincs_signers_{:016x}.bin", sphincs_footprint()))
}

fn try_load_sphincs_cache() -> Option<Vec<CachedSphincsSignature>> {
    let bytes = fs::read(sphincs_cache_path()).ok()?;
    let mut signers = Vec::with_capacity(bytes.len() / SPHINCS_RECORD);
    for record in bytes.as_chunks::<SPHINCS_RECORD>().0 {
        let (key_bytes, rest) = record.split_at(sphincs::PUB_KEY_SIZE);
        let (message_bytes, signature_bytes) = rest.split_at(sphincs::MESSAGE_LEN);
        let public_key = sphincs::PublicKey::from_bytes(key_bytes.try_into().unwrap());
        let message: sphincs::Message = message_bytes.try_into().unwrap();
        let signature = sphincs::Signature::from_bytes(signature_bytes.try_into().unwrap());
        if sphincs::verify(&public_key, &message, &signature).is_err() {
            eprintln!(
                "warning: signers cache {} is stale (signer {} no longer verifies); regenerating from there",
                sphincs_cache_path().display(),
                signers.len()
            );
            break;
        }
        signers.push((public_key, message, signature));
    }
    Some(signers)
}

fn save_sphincs_cache(signers: &[CachedSphincsSignature]) {
    let path = sphincs_cache_path();
    if let Some(parent) = path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    let mut bytes = Vec::with_capacity(signers.len() * SPHINCS_RECORD);
    for (public_key, message, signature) in signers {
        bytes.extend_from_slice(&public_key.flatten());
        bytes.extend_from_slice(message);
        bytes.extend_from_slice(&signature.to_bytes());
    }
    if let Err(error) = fs::write(&path, &bytes) {
        eprintln!("warning: could not write signers cache to {}: {error}", path.display());
    }
}

static SPHINCS_POOL: Mutex<Vec<CachedSphincsSignature>> = Mutex::new(Vec::new());

pub fn get_sphincs_signers(n: usize) -> Vec<CachedSphincsSignature> {
    let mut pool = SPHINCS_POOL.lock().unwrap();
    if pool.len() < n {
        if let Some(disk) = try_load_sphincs_cache()
            && disk.len() > pool.len()
        {
            *pool = disk;
        }
        // Key generation is one whole 2^12-leaf tree, which is the expensive
        // part; it fans out internally, so this loop stays sequential.
        let started = Instant::now();
        let missing = n.saturating_sub(pool.len());
        for index in pool.len()..n {
            pool.push(compute_sphincs_signer(index));
            print!(
                "\r  generating SPHINCS signers (one-time, then cached): {}/{}",
                pretty_integer(index + 1 - (n - missing)),
                pretty_integer(missing)
            );
            let _ = std::io::stdout().flush();
        }
        if missing > 0 {
            println!(
                "\r  generated {} SPHINCS in {} s (cached to disk)              ",
                pretty_integer(missing),
                pretty_f64(started.elapsed().as_secs_f64())
            );
            save_sphincs_cache(&pool);
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
