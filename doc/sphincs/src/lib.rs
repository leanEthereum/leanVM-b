//! SPHINCS+ parameters: security, signature size, hash counts, and a search.
//!
//! Covers the WOTS-based / FORS-based schemes of "Hash-based Signature Schemes
//! for Bitcoin" (Kudinov, Nick, Blockstream Research, rev. 2025-12-05) and its
//! scripts at github.com/BlockstreamResearch/SPHINCS-Parameters:
//!
//! | scheme    | what it is                                              |
//! | --------- | ------------------------------------------------------- |
//! | `SPX`     | plain SPHINCS+ (SLH-DSA): WOTS-TW + FORS                 |
//! | `W+C`     | WOTS+C (fixed digit sum, no checksum chains) + FORS      |
//! | `W+C_F+C` | WOTS+C + FORS+C (last FORS tree removed by grinding)     |
//!
//! PORS+FP is deliberately not implemented.
//!
//! WOTS+C shortens its signature by dropping chains, and this does that the way
//! `doc/xmss/main.tex` does: it pins the top bits of the digest to zero instead
//! of forcing whole digits, so the digest is always a whole number of base-w
//! chunks (see [`cost::Encoding`]). The default pins the minimum that makes the
//! cut integral; dropping further chains pins `log2(w)` more bits each, every
//! pinned bit doubling the expected grinding.
//!
//! For one parameter set [`params::costs`] reports the signature size and the
//! keygen, signing and verification cost, and [`security::security_bits`] the
//! classical security. Signing comes in two flavours: vanilla, and with the top
//! XMSS tree's "half top" cached, meaning its nodes at depth `ceil(h'/2)` kept
//! as signer state, which is `sqrt(2^h')` of storage for a `sqrt(2^h')` top-tree
//! cost per signature.
//!
//! Every cost comes in two units, matching the report's tables: `hashes` counts
//! tweakable-hash and PRF invocations, `compressions` counts SHA-256 compression
//! calls under the FIPS 205 SHA-2 layout with the PK.seed midstate cached.
//!
//! [`search::search`] inverts the question: given a lifetime and a budget for
//! keygen, signing (both flavours) and size, it enumerates the space and returns
//! what verifies cheapest at 128-bit classical security.
//!
//! `tests/goldens.rs` pins all of it against the upstream sage scripts' frozen
//! fixtures, against the report's own tables, and, for the search, against a
//! naive oracle that skips nothing.

pub mod cost;
pub mod params;
pub mod report;
pub mod search;
pub mod security;
