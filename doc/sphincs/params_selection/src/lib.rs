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
//! The hypertree's height is split per layer, not `h/d` on every layer: the top
//! tree gets `h_top` and the rest divide what is left as evenly as it goes, so
//! `d` need not divide `h`, and [`params::Hypertree`] can hold any heights at
//! all though only that shape is ever searched. That matters because the
//! signature carries `h`
//! authentication nodes and the verifier walks them however the layers divide
//! `h`: size and verification depend only on `(h, d)`, while only the top tree
//! is cacheable. A taller top layer is therefore free on both, costs keygen and
//! vanilla signing, and cuts cached signing, which at `h = 40, d = 5` is 2x for
//! `h_top = 15` against the uniform 8.
//!
//! A [`params::Layer`] also carries its own WOTS instance, so `w`, the target
//! sum and the dropped chains need not agree across layers either, and
//! [`params::Layer`] says what varying them buys and when. A search tries two
//! instances, one for the top layer and one for the rest, which
//! [`params::Hypertree::two_group`] argues is all it needs.
//!
//! For one parameter set [`params::costs`] reports the signature size and the
//! keygen, signing and verification cost, and [`security::security_bits`] the
//! classical security. Signing means signing with the top XMSS tree's "half
//! top" in state, its nodes at depth `ceil(h_top/2)`, which is `sqrt(2^h_top)`
//! of storage for a `sqrt(2^h_top)` top-tree cost per signature and the cost a
//! signer keeping that cache actually pays. What a signer holding nothing pays
//! is [`params::Costs::sign_cold`], computed but not reported.
//!
//! Everything is counted in compression calls, one per 64 bytes of hash input:
//! a Merkle node or a WOTS chain step is one, the message digest two, and
//! compressing `m` hash values `ceil((2n + mn) / 64)`. See [`cost::Blocks`],
//! which also notes that this is the same function as the report's SHA-2 layout
//! with the PK.seed midstate cached, so its published counts still pin it.
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
