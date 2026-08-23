#!/usr/bin/env python3
"""SPHINCS+ parameter calculator: security, signature size, and hash counts.

Covers the WOTS-based / FORS-based schemes of "Hash-based Signature Schemes for
Bitcoin" (Kudinov, Nick, Blockstream Research, rev. 2025-12-05) and its scripts
at github.com/BlockstreamResearch/SPHINCS-Parameters:

    SPX      plain SPHINCS+ (SLH-DSA): WOTS-TW + FORS
    W+C      WOTS+C (fixed digit sum, no checksum chains) + FORS
    W+C_F+C  WOTS+C + FORS+C (last FORS tree removed by grinding)

PORS+FP is deliberately not implemented.

WOTS+C shortens its signature by dropping chains, and this script does that the
way doc/xmss/main.tex does: it pins the top bits of the digest to zero instead
of forcing whole digits, so the digest is always a whole number of base-w chunks
(see the Encoding class). The default pins the minimum that makes the cut
integral; --drop-chains buys further chains at log2(w) pinned bits each, every
pinned bit doubling the expected grinding.

For a parameter set it reports:

    * classical security in bits (FORS subset-forgery vs. preimage bound)
    * signature size in bytes
    * hashes at key generation
    * expected hashes at signing
    * hashes at verification
    * expected hashes at signing with the top tree's "half top" cached, i.e.
      keeping the nodes of the top XMSS tree at depth ceil(h'/2) as signer
      state: sqrt(2^h') storage buys a sqrt(2^h') top-tree cost per signature

Two units are reported for every cost, matching the report's tables:

    hashes        tweakable-hash / PRF invocations (the report's "hash" columns)
    compressions  SHA-256 compression calls (the report's Compr. columns)

The compression counts follow the FIPS 205 SHA-2 layout with the PK.seed
midstate cached; pass --uncached to charge every call for its full input.

Numbers reproduce costs.sage / security.sage exactly; run --selftest to check
against the golden values frozen in that repo's tests/fixtures.json.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from decimal import Decimal, getcontext
from math import ceil, floor, log2

getcontext().prec = 120

SCHEMES = ("SPX", "W+C", "W+C_F+C")

COUNTER_BYTES = 4  # WOTS+C grinding counter carried per hypertree layer


# ---------------------------------------------------------------------------
# Hash-cost conventions
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Convention:
    """Compression calls charged to each kind of hash invocation."""

    cached_midstate: bool = True

    @property
    def th1(self) -> int:
        return 1  # PK.seed + ADRS + one n-byte value

    @property
    def th1c(self) -> int:
        return 1  # ... + the 4-byte WOTS+C counter

    @property
    def th2(self) -> int:
        return 1 if self.cached_midstate else 2  # two n-byte children

    @property
    def hmsg(self) -> int:
        return 2  # PK.seed + PK.root + R + message digest

    @property
    def prfmsg(self) -> int:
        return 2  # SK.prf + opt + message

    @property
    def prf(self) -> int:
        return 1  # PK.seed + SK.seed + ADRS

    def th(self, m: int, n: int) -> int:
        """Compressions for a tweakable hash over m n-byte values."""
        prefix = 22 * 8 if self.cached_midstate else 8 * (n + 12)
        return ceil((prefix + 8 * n * m + 65) / 512)


# ---------------------------------------------------------------------------
# WOTS
# ---------------------------------------------------------------------------


def wots_len1(w: int, n: int) -> int:
    """Message chains: enough base-w digits to carry an n-byte digest."""
    return ceil(8 * n / log2(w))


def wots_len2(w: int, n: int) -> int:
    """Checksum chains of WOTS-TW (FIPS 205 form)."""
    l1 = wots_len1(w, n)
    return floor(log2(l1 * (w - 1)) / log2(w)) + 1


@dataclass(frozen=True)
class Encoding:
    """How a WOTS+C digest is cut into base-w chain positions.

    The report drops chains by forcing their digits to zero (its parameter z).
    This script instead uses the bit-pinning variant the report offers as an
    alternative in "Complexity Analysis of WOTS+C" (its z_b), which is what
    doc/xmss/main.tex does, because it keeps the digest a whole number of
    chunks and needs no partial-digit handling anywhere:

        chain_bits = log2(w)                    bits one chain carries
        pinned     = (8n) mod chain_bits         + chain_bits * dropped_chains
        chains     = (8n - pinned) / chain_bits  = floor(8n/chain_bits) - dropped

    The signer grinds the counter until the digest has its `pinned` top bits
    zero AND its `chains` digits summing to S_wn, so out of the 2^(8n) digests
    exactly nu = |{tuples summing to S_wn}| are admissible.

    Pinning is not free: every pinned bit halves the admissible fraction, so
    `pinned` bits multiply the expected grinding by 2^pinned. It buys chains
    cheaply though. The default is the minimum that leaves 8n - pinned a
    multiple of chain_bits, and what it saves is the extra, only partly used
    chain that ceil(8n / chain_bits) would need: n bytes of signature for a
    factor 2^(8n mod chain_bits), which at chain_bits = 3 is 16 bytes for 4x
    on a per-layer grind of a few hundred hashes. Each further dropped chain
    then saves another n bytes for a factor of about w.

    doc/xmss/main.tex is the (n=128, chain_bits=3) instance: 128 mod 3 = 2 bits
    pinned, v = 42 chains, T = 195. Dropping one more chain there would pin
    2 + 3 = 5 bits and leave 41 chains. For every w the report itself uses
    (16 and 256) chain_bits divides 128, so nothing is pinned and this
    reproduces its numbers exactly.
    """

    w: int
    n: int
    dropped_chains: int = 0

    @property
    def chain_bits(self) -> int:
        return int(log2(self.w))

    @property
    def pinned_bits(self) -> int:
        return 8 * self.n % self.chain_bits + self.chain_bits * self.dropped_chains

    @property
    def chains(self) -> int:
        chains = (8 * self.n - self.pinned_bits) // self.chain_bits
        if chains < 1:
            raise ValueError(f"dropped_chains={self.dropped_chains} leaves no chain to sign")
        return chains

    @property
    def default_swn(self) -> int:
        """Mean digit sum, where the admissible digests are densest."""
        return self.chains * (self.w - 1) // 2

    def admissible(self, swn: int) -> int:
        """nu: digests with the pinned bits zero and digits summing to swn."""
        return wots_c_encodings(self.chains, swn, self.w)

    def expected_trials(self, swn: int) -> int:
        """Counter values tried per layer, 2^(8n) / nu by the geometric law."""
        return -(-(1 << (8 * self.n)) // self.admissible(swn))


def wots_chains(scheme: str, w: int, n: int, dropped_chains: int = 0) -> int:
    """Chains actually signed: l1 + l2 for WOTS-TW, the encoding's for WOTS+C."""
    if scheme == "SPX":
        return wots_len1(w, n) + wots_len2(w, n)
    return Encoding(w, n, dropped_chains).chains


def wots_c_encodings(l: int, swn: int, w: int) -> int:
    """nu: number of l-tuples over [0, w-1] summing to exactly swn."""
    from math import comb

    nu = 0
    for j in range(l + 1):
        top = (swn + l) - j * w - 1
        nu += (-1) ** j * comb(l, j) * (comb(top, l - 1) if top >= l - 1 else 0)
    if nu <= 0:
        raise ValueError(f"no encoding of {l} base-{w} digits sums to S_wn={swn}")
    return nu


def wots_tw_worst_steps(w: int, n: int) -> int:
    """Verifier chain steps for WOTS-TW when every message digit is zero."""
    l1, l2 = wots_len1(w, n), wots_len2(w, n)
    c, ds = l1 * (w - 1), 0
    rem = c
    while rem:
        ds += rem % w
        rem //= w
    return l1 * (w - 1) + l2 * (w - 1) - ds


# ---------------------------------------------------------------------------
# Classical security
# ---------------------------------------------------------------------------


def fors_forgery_exponent(q_s_log2: int, h: int, k: int, a: int, r_cap: int = 1 << 18) -> float:
    """-log2 P(FORS subset forgery) after q_s = 2^q_s_log2 signatures.

    An adversary that finds a hypertree leaf reused r times, and a message whose
    k FORS indices all point at leaves those r signatures already opened, forges
    without inverting anything:

        P = sum_r  C(q_s, r) p^r (1-p)^(q_s-r) * (1 - (1 - 1/t)^r)^k

    with p = 2^-h the chance one signature lands on a given leaf and t = 2^a.
    The binomial term is carried by its recurrence rather than built from
    C(q_s, r) directly, so q_s = 2^64 costs the same as q_s = 2^20.
    """
    q_s = Decimal(2) ** q_s_log2
    p = Decimal(2) ** -h
    t = Decimal(2) ** a
    one_minus_p = 1 - p
    ratio = p / one_minus_p
    miss = 1 - 1 / t  # P(one signature misses a given leaf of one FORS tree)

    lam = 2.0 ** (q_s_log2 - h)  # expected times one FORS instance is reused
    if lam > 4096:
        raise ValueError(
            f"q_s = 2^{q_s_log2} over 2^{h} hypertree leaves reuses every FORS instance ~2^{q_s_log2 - h} times: no security is left to quantify"
        )
    r_max = min(r_cap, max(1000, int(lam + 40 * (lam + 1) ** 0.5) + 40))
    floor_prob = Decimal(2) ** -1250
    relative_floor = Decimal(2) ** -80

    term = one_minus_p**q_s  # C(q_s,0) p^0 (1-p)^q_s
    miss_r = Decimal(1)
    sigma = Decimal(0)
    r = 0
    while r < r_max:
        r += 1
        term *= (q_s - r + 1) / Decimal(r) * ratio
        miss_r *= miss
        contribution = term * (1 - miss_r) ** k
        sigma += contribution
        if r > lam and (contribution < floor_prob or contribution < sigma * relative_floor):
            break
    else:
        raise ValueError(f"security sum did not converge within r <= {r_max}; parameters are far below any usable level")

    if sigma <= 0:
        return float("inf")
    return float(-sigma.ln() / Decimal(2).ln())


def security_bits(q_s_log2: int, h: int, k: int, a: int, n: int) -> float:
    """Classical bit security: forgery exponent capped by the preimage bound.

    A query aimed at a FORS forgery cannot double as a preimage query for a tree
    node or a WOTS chain (different tweaks), so the two attacks are independent
    strategies and the adversary simply takes the better one.
    """
    return min(8 * n, fors_forgery_exponent(q_s_log2, h, k, a))


# ---------------------------------------------------------------------------
# Costs
# ---------------------------------------------------------------------------


@dataclass
class Cost:
    """A cost in both units."""

    hashes: int
    compressions: int

    def __add__(self, other: Cost) -> Cost:
        return Cost(self.hashes + other.hashes, self.compressions + other.compressions)

    def __sub__(self, other: Cost) -> Cost:
        return Cost(self.hashes - other.hashes, self.compressions - other.compressions)

    def __mul__(self, m: int) -> Cost:
        return Cost(self.hashes * m, self.compressions * m)

    __rmul__ = __mul__


def _wots_leaf(l: int, w: int, n: int, cv: Convention) -> Cost:
    """One WOTS key pair plus the compression of its l chain ends into a leaf."""
    return Cost(l + l * (w - 1) + 1, l * cv.prf + l * (w - 1) * cv.th1 + cv.th(l, n))


def _xmss_tree(leaves: int, l: int, w: int, n: int, cv: Convention) -> Cost:
    """Build a Merkle tree over `leaves` WOTS key pairs, from the seed up."""
    return leaves * _wots_leaf(l, w, n, cv) + Cost(leaves - 1, (leaves - 1) * cv.th2)


def _msg_hash(cv: Convention) -> Cost:
    """R = PRF_msg(...) and the randomized message digest H_msg(...)."""
    return Cost(2, cv.hmsg + cv.prfmsg)


def _fors_build(trees: int, a: int, n: int, cv: Convention) -> Cost:
    """Grow `trees` FORS trees of 2^a secret leaves and compress their roots."""
    t = 1 << a
    return Cost(
        trees * t + trees * t + trees * (t - 1) + 1,
        trees * t * cv.prf + trees * t * cv.th1 + trees * (t - 1) * cv.th2 + cv.th(trees, n),
    )


def _fors_verify(trees: int, a: int, n: int, cv: Convention) -> Cost:
    """Hash `trees` opened leaves up their auth paths and compress the roots."""
    return Cost(
        trees + trees * a + 1,
        trees * cv.th1 + trees * a * cv.th2 + cv.th(trees, n),
    )


# ---------------------------------------------------------------------------
# Top level
# ---------------------------------------------------------------------------


@dataclass
class Result:
    scheme: str
    q_s_log2: int
    n: int
    h: int
    d: int
    h_prime: int
    a: int
    k: int
    w: int
    l: int
    chain_bits: int
    pinned_bits: int
    dropped_chains: int
    swn: int | None

    security_bits: float
    fors_forgery_bits: float
    sig_bytes: int

    keygen_hashes: int
    keygen_compressions: int

    sign_hashes: int
    sign_compressions: int
    sign_grinding_hashes: int
    wots_c_grinding_hashes: int
    fors_c_grinding_hashes: int

    verify_hashes: int
    verify_compressions: int
    verify_hashes_worst: int
    verify_compressions_worst: int

    cache_depth: int
    cache_bytes: int
    sign_cached_hashes: int
    sign_cached_compressions: int


def evaluate(
    h: int,
    d: int,
    a: int,
    k: int,
    w: int,
    q_s_log2: int,
    scheme: str = "W+C_F+C",
    swn: int | None = None,
    n: int = 16,
    dropped_chains: int = 0,
    cache_height: int | None = None,
    cache_level_only: bool = False,
    convention: Convention | None = None,
) -> Result:
    """Evaluate one SPHINCS+ parameter set.

    h, d      hypertree height and number of layers (h' = h/d per XMSS tree)
    a, k      FORS trees of 2^a leaves, k of them
    w         Winternitz parameter
    q_s_log2  log2 of the signatures allowed under one public key
    scheme    "SPX", "W+C", or "W+C_F+C"
    swn       WOTS+C target digit sum S_{w,n}; defaults to the mean l*(w-1)/2
    dropped_chains  chains dropped on top of the digest bits that have to be
                    pinned anyway, each one pinning log2(w) more bits: see
                    Encoding
    cache_height  height above the leaves of the cached top-tree level; the
                  default h'//2 is the "half top" (cached level at depth
                  ceil(h'/2), so the cheaper half of the tree is rebuilt)
    cache_level_only  store just that one level instead of it and everything
                      above, paying 2^ceil(h'/2)-1 hashes to rebuild the top
    """
    if scheme not in SCHEMES:
        raise ValueError(f"scheme must be one of {SCHEMES} (PORS+FP is out of scope)")
    if h % d:
        raise ValueError("d must divide h")
    if log2(w) != int(log2(w)):
        raise ValueError("w must be a power of two")
    if scheme == "SPX" and dropped_chains:
        raise ValueError("dropped_chains applies to WOTS+C only")

    cv = convention or Convention()
    wots_c = scheme != "SPX"
    fors_c = scheme == "W+C_F+C"
    hp = h // d
    enc = Encoding(w, n, dropped_chains)
    l = wots_chains(scheme, w, n, dropped_chains)
    swn_c = 0 if not wots_c else (enc.default_swn if swn is None else swn)
    trees = k - 1 if fors_c else k  # FORS+C grinds the last tree away

    # ---- size ----------------------------------------------------------
    layer = hp * n + l * n + (COUNTER_BYTES if wots_c else 0)
    sig_bytes = n + d * layer + trees * n + trees * a * n

    # ---- hypertree, shared by keygen and signing -----------------------
    tree = _xmss_tree(1 << hp, l, w, n, cv)
    trials = enc.expected_trials(swn_c) if wots_c else 0
    grinding = d * trials
    hyper = d * tree + Cost(grinding, grinding * cv.th1c)

    # ---- keygen: the top tree only, to get PK.root ---------------------
    keygen = tree

    # ---- signing -------------------------------------------------------
    fors = _fors_build(trees, a, n, cv)
    if fors_c:
        # grind the digest until its last a bits vanish, so the last FORS tree
        # always opens leaf 0 and needs no authentication path
        fors_grind = (1 << a) * _msg_hash(cv)
    else:
        fors_grind = _msg_hash(cv)
    sign = hyper + fors + fors_grind

    # ---- verification --------------------------------------------------
    if wots_c:
        # the digits sum to S_wn, so the remaining chain steps are fixed
        wots_v = Cost((w - 1) * l - swn_c + 2, ((w - 1) * l - swn_c) * cv.th1 + cv.th1c + cv.th(l, n))
        wots_v_worst = wots_v
    else:
        wots_v = Cost((w - 1) * l // 2 + 1, (w - 1) * l // 2 * cv.th1 + cv.th(l, n))
        steps = wots_tw_worst_steps(w, n)
        wots_v_worst = Cost(steps + 1, steps * cv.th1 + cv.th(l, n))
    fts_v = _fors_verify(trees, a, n, cv)
    auth = Cost(h, h * cv.th2)
    verify = Cost(1, cv.hmsg) + fts_v + d * wots_v + auth
    verify_worst = Cost(1, cv.hmsg) + fts_v + d * wots_v_worst + auth

    # ---- signing with the top tree's half top cached -------------------
    # Only the top tree is worth caching: it is the same for every signature,
    # while the trees below it are picked by the (pseudorandom) index. Its auth
    # path splits at the cached level: below, rebuild the 2^c-leaf subtree the
    # signing leaf sits in; above, the nodes are already in state. Rebuilt
    # leaves are charged a full WOTS public key, as everywhere else here.
    #
    # A BDS-style traversal would amortize a tree to h' leaves per signature
    # with O(h') state, but it only works walking the leaves in order. SPHINCS+
    # picks its index by hashing the message, so consecutive signatures land on
    # unrelated leaves and nothing amortizes; an index-independent cache like
    # this one is what is left, hence sqrt rather than h'.
    c = hp // 2 if cache_height is None else cache_height
    if not 0 <= c <= hp:
        raise ValueError("cache_height must be in [0, h/d]")
    stored_level = 1 << (hp - c)
    cached_tree = _xmss_tree(1 << c, l, w, n, cv)
    if cache_level_only:
        cached_tree += Cost(stored_level - 1, (stored_level - 1) * cv.th2)
        cache_bytes = stored_level * n
    else:
        cache_bytes = (2 * stored_level - 1) * n
    sign_cached = sign - tree + cached_tree

    forgery = fors_forgery_exponent(q_s_log2, h, k, a)
    return Result(
        scheme=scheme,
        q_s_log2=q_s_log2,
        n=n,
        h=h,
        d=d,
        h_prime=hp,
        a=a,
        k=k,
        w=w,
        l=l,
        chain_bits=enc.chain_bits,
        pinned_bits=enc.pinned_bits if wots_c else 0,
        dropped_chains=dropped_chains,
        swn=swn_c if wots_c else None,
        security_bits=min(8 * n, forgery),
        fors_forgery_bits=forgery,
        sig_bytes=sig_bytes,
        keygen_hashes=keygen.hashes,
        keygen_compressions=keygen.compressions,
        sign_hashes=sign.hashes,
        sign_compressions=sign.compressions,
        sign_grinding_hashes=grinding + fors_grind.hashes - (0 if fors_c else 2),
        wots_c_grinding_hashes=grinding,
        fors_c_grinding_hashes=fors_grind.hashes if fors_c else 0,
        verify_hashes=verify.hashes,
        verify_compressions=verify.compressions,
        verify_hashes_worst=verify_worst.hashes,
        verify_compressions_worst=verify_worst.compressions,
        cache_depth=hp - c,
        cache_bytes=cache_bytes,
        sign_cached_hashes=sign_cached.hashes,
        sign_cached_compressions=sign_cached.compressions,
    )


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------


def _si(x: float) -> str:
    for unit, div in (("G", 1e9), ("M", 1e6), ("K", 1e3)):
        if x >= div:
            return f"{x / div:.2f}{unit}"
    return str(int(x))


def encoding_line(r: Result) -> str:
    """One line spelling out the WOTS+C digest-to-chains cut."""
    if r.swn is None:
        return f"encoding        WOTS-TW: {r.l} chains, {r.l - wots_len2(r.w, r.n)} for the digest + {wots_len2(r.w, r.n)} checksum"
    dropped = f", {r.dropped_chains} chain(s) dropped" if r.dropped_chains else ""
    return (
        f"encoding        {r.chain_bits} bits/chain, {r.pinned_bits} of {8 * r.n} digest bits pinned to zero"
        f"{dropped}, S_wn = {r.swn} of {r.l * (r.w - 1)}"
    )


def report(r: Result) -> str:
    speedup = r.sign_hashes / r.sign_cached_hashes

    def row(label: str, hashes: int, compressions: int, note: str = "") -> str:
        return f"{label:<24}{_si(hashes):>12}{_si(compressions):>16}{note}"

    lines = [
        f"scheme          {r.scheme}   q_s = 2^{r.q_s_log2}   n = {8 * r.n} bits",
        f"(h, d, h')      ({r.h}, {r.d}, {r.h_prime})",
        f"(a, k)          ({r.a}, {r.k})" + (f"   [FORS+C signs {r.k - 1} trees]" if r.scheme == "W+C_F+C" else ""),
        f"(w, l)          ({r.w}, {r.l})",
        encoding_line(r),
        "",
        f"security        {r.security_bits:.1f} bits classical"
        + (f"   (FORS forgery {r.fors_forgery_bits:.1f}, preimage {8 * r.n})" if r.fors_forgery_bits < 1e6 else ""),
        f"signature       {r.sig_bytes} bytes",
        "",
        f"{'':24}{'hashes':>12}{'compressions':>16}",
        row("keygen", r.keygen_hashes, r.keygen_compressions),
        row("sign (avg)", r.sign_hashes, r.sign_compressions),
        row(
            "sign (half-top cached)",
            r.sign_cached_hashes,
            r.sign_cached_compressions,
            f"   ({speedup:.2f}x, {r.cache_bytes} B of state at depth {r.cache_depth})",
        ),
        row("verify", r.verify_hashes, r.verify_compressions),
    ]
    if r.verify_hashes_worst != r.verify_hashes:
        lines.append(row("verify (worst)", r.verify_hashes_worst, r.verify_compressions_worst))
    lines += [
        "",
        (
            f"of signing, grinding accounts for {_si(r.sign_grinding_hashes)} hashes:"
            f" {_si(r.wots_c_grinding_hashes)} for the WOTS+C counters,"
            f" {_si(r.fors_c_grinding_hashes)} for the FORS+C digest"
        ),
    ]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Self-test against the golden values of BlockstreamResearch/SPHINCS-Parameters
# ---------------------------------------------------------------------------

# tests/fixtures.json, "cached" hash convention: scheme|h,d,k,a,w,swn -> costs.sage
GOLDEN = {
    ("SPX", 63, 7, 14, 12, 16, None): {"size": 7856, "kg": 292351, "sg": 2218483, "sv": 2155, "sv_worst": 3891},
    ("W+C", 44, 4, 8, 16, 16, 240): {"size": 4960, "kg": 1069055, "sg": 5849347, "sv": 1185, "sv_worst": 1185},
    ("W+C", 40, 5, 11, 14, 256, 2040): {"size": 4596, "kg": 1050111, "sg": 5794969, "sv": 10441, "sv_worst": 10441},
    ("W+C", 40, 5, 11, 14, 256, 2840): {"size": 4596, "kg": 1050111, "sg": 5941944, "sv": 6441, "sv_worst": 6441},
    ("W+C_F+C", 44, 4, 8, 16, 16, 240): {"size": 4688, "kg": 1069055, "sg": 5914880, "sv": 1168, "sv_worst": 1168},
    ("W+C_F+C", 40, 5, 11, 14, 256, 2040): {"size": 4356, "kg": 1050111, "sg": 5811349, "sv": 10425, "sv_worst": 10425},
    ("W+C_F+C", 20, 2, 10, 15, 256, 2040): {"size": 3160, "kg": 4200447, "sg": 9418194, "sv": 4261, "sv_worst": 4261},
}
GOLDEN_UNCACHED = {
    ("SPX", 63, 7, 14, 12, 16, None): {"size": 7856, "kg": 292862, "sg": 2279391, "sv": 2387, "sv_worst": 4123},
    ("W+C", 44, 4, 8, 16, 16, 240): {"size": 4960, "kg": 1071102, "sg": 6381815, "sv": 1357, "sv_worst": 1357},
}
# The report's Tables 1 and 2, WOTS/FORS rows only: the "SigVer (hash)",
# "SigTime (hash)" (as a multiple of 10^4, 3 significant figures) and
# "Exp. Search (hash)" columns, keyed by (scheme, h, d, a, k, w, S_wn).
# The tables' "Sig (B)" column is 16 bytes above what costs.sage now computes
# (it predates the report; the repo's own fixtures agree with this script).
REPORT_TABLE = {
    ("SPX", 63, 7, 12, 14, 16, None): (2088, 219, 0),
    ("W+C", 44, 4, 16, 8, 16, 240): (1150, 578, 264),
    ("W+C", 44, 4, 16, 8, 16, 304): (894, 579, 5344),
    ("W+C", 44, 4, 16, 8, 256, 2040): (8350, 3515, 2996),
    ("W+C", 40, 5, 14, 11, 256, 2040): (10417, 579, 3745),
    ("W+C", 40, 5, 14, 11, 256, 2840): (6417, 594, None),
    ("W+C_F+C", 44, 4, 16, 8, 16, 240): (1133, 572, None),
    ("W+C_F+C", 40, 5, 14, 11, 256, 2040): (10402, 577, 36513),
    ("W+C", 36, 3, 14, 9, 16, 240): (899, 676, 198),
    ("W+C", 33, 3, 15, 9, 16, 304): (713, 405, 4008),
    ("W+C", 32, 4, 14, 10, 256, 2840): (5152, 481, None),
    ("W+C_F+C", 33, 3, 15, 9, 16, 240): (889, 401, 65734),
    ("W+C_F+C", 32, 4, 14, 10, 256, 2040): (8337, 467, 35764),
    ("W+C", 24, 2, 16, 8, 16, 240): (646, 578, None),
    ("W+C", 24, 2, 16, 8, 256, 2040): (4246, 3515, None),
    ("W+C_F+C", 24, 2, 16, 8, 16, 240): (629, 572, None),
    ("W+C", 20, 2, 15, 10, 256, 2040): (4266, 938, None),
    ("W+C_F+C", 20, 2, 15, 10, 256, 2040): (4250, 934, None),
}
# (w, n, dropped_chains) -> (chain_bits, pinned_bits, chains, default S_wn)
GOLDEN_ENCODINGS = {
    (8, 16, 0): (3, 2, 42, 147),  # doc/xmss/main.tex
    (8, 16, 1): (3, 5, 41, 143),
    (8, 16, 2): (3, 8, 40, 140),
    (16, 16, 0): (4, 0, 32, 240),  # the report's w = 16: nothing to pin
    (16, 16, 1): (4, 4, 31, 232),
    (32, 16, 0): (5, 3, 25, 387),  # 128 = 5*25 + 3
    (256, 16, 0): (8, 0, 16, 2040),
    (8, 32, 0): (3, 1, 85, 297),  # 256 = 3*85 + 1
}
# security.sage / site/stateless.html, for (q_s_log2, h, k, a)
GOLDEN_SECURITY = {
    (64, 63, 14, 12): 128.0,  # SLH-DSA-128s/f: preimage bound dominates
    (40, 44, 8, 16): 128.0,
    (40, 40, 11, 14): 128.0,
    (30, 32, 10, 14): 128.0,
    (20, 24, 8, 16): 128.0,
}


def selftest() -> int:
    fails = 0

    def check(name, got, want, tol=0.05):
        nonlocal fails
        ok = got == want if isinstance(want, int) else abs(got - want) < tol
        fails += not ok
        if not ok:
            print(f"FAIL {name}: got {got}, want {want}")

    for cv, table in ((Convention(True), GOLDEN), (Convention(False), GOLDEN_UNCACHED)):
        tag = "cached" if cv.cached_midstate else "uncached"
        for (scheme, h, d, k, a, w, swn), want in table.items():
            # the cost model does not depend on q_s; security is checked separately
            r = evaluate(h, d, a, k, w, min(40, h), scheme=scheme, swn=swn, convention=cv)
            fields = (
                ("sig_bytes", "size"),
                ("keygen_compressions", "kg"),
                ("sign_compressions", "sg"),
                ("verify_compressions", "sv"),
                ("verify_compressions_worst", "sv_worst"),
            )
            for field, key in fields:
                check(f"{tag} {scheme} h={h} d={d} k={k} a={a} w={w} {key}", getattr(r, field), want[key])

    for (scheme, h, d, a, k, w, swn), (sv, sg_e4, search) in REPORT_TABLE.items():
        r = evaluate(h, d, a, k, w, min(40, h), scheme=scheme, swn=swn)
        tag = f"report {scheme} h={h} d={d} a={a} k={k} w={w} S={swn}"
        check(f"{tag} SigVer", r.verify_hashes, sv)
        check(f"{tag} SigTime", r.sign_hashes / 1e4, float(sg_e4), tol=0.55)  # table rounds to 3 figures
        if search is not None:
            check(f"{tag} Exp.Search", r.sign_grinding_hashes, search)

    for (q, h, k, a), want in GOLDEN_SECURITY.items():
        check(f"security q_s=2^{q} h={h} k={k} a={a}", security_bits(q, h, k, a, 16), want)

    # Encoding geometry: doc/xmss/main.tex is the (n=128, chain_bits=3) instance,
    # with 2 bits pinned, v = 42 chains and T = 195.
    for (w, n, drop), (bits, pinned, chains, mean) in GOLDEN_ENCODINGS.items():
        e = Encoding(w, n, drop)
        tag = f"encoding w={w} n={n} drop={drop}"
        check(f"{tag} chain_bits", e.chain_bits, bits)
        check(f"{tag} pinned_bits", e.pinned_bits, pinned)
        check(f"{tag} chains", e.chains, chains)
        check(f"{tag} default_swn", e.default_swn, mean)
    check("doc/xmss T=195 trials", Encoding(8, 16).expected_trials(195), 29490)
    check("one dropped chain costs about w", Encoding(8, 16, 1).expected_trials(143) // Encoding(8, 16).expected_trials(147), 7)

    # h'=0 leaves nothing to cache; h'=h/d with c=0 rebuilds one leaf only
    r = evaluate(40, 5, 14, 11, 256, 40, scheme="W+C_F+C")
    check("cache is a strict saving", r.sign_cached_hashes < r.sign_hashes, True)
    check("cache_height=h' is the full tree", evaluate(40, 5, 14, 11, 256, 40, cache_height=8).sign_cached_hashes, r.sign_hashes)

    print("selftest: " + ("all checks passed" if not fails else f"{fails} failures"))
    return fails


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main() -> int:
    p = argparse.ArgumentParser(description=(__doc__ or "").splitlines()[0], formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--scheme", default="W+C_F+C", choices=SCHEMES)
    p.add_argument("--qs", type=int, default=40, metavar="LOG2", help="log2 of signatures per public key (default 40)")
    p.add_argument("--height", type=int, default=40, metavar="h", help="hypertree height (default 40)")
    p.add_argument("--layers", type=int, default=5, metavar="d", help="hypertree layers (default 5)")
    p.add_argument("-a", type=int, default=14, help="log2 leaves per FORS tree (default 14)")
    p.add_argument("-k", type=int, default=11, help="FORS trees (default 11)")
    p.add_argument("-w", type=int, default=256, help="Winternitz parameter (default 256)")
    p.add_argument("--swn", type=int, default=None, help="WOTS+C target digit sum S_wn (default: the mean, l*(w-1)/2)")
    p.add_argument("-n", type=int, default=16, help="hash output in bytes (default 16)")
    p.add_argument("--chain-bits", type=int, default=None, metavar="B", help="log2(w), an alternative way to give w (3 means 8 hashes per chain)")
    p.add_argument(
        "--drop-chains",
        type=int,
        default=0,
        metavar="C",
        help="WOTS+C chains dropped beyond the minimal bit pinning; each pins log2(w) more digest bits (default 0)",
    )
    p.add_argument("--cache-height", type=int, default=None, metavar="c", help="height of the cached top-tree level above the leaves (default h'//2)")
    p.add_argument("--cache-level-only", action="store_true", help="cache that one level, not it and everything above")
    p.add_argument("--uncached", action="store_true", help="charge every hash for its full input instead of caching the PK.seed midstate")
    p.add_argument("--json", action="store_true")
    p.add_argument("--selftest", action="store_true")
    args = p.parse_args()

    if args.selftest:
        return 1 if selftest() else 0

    if args.chain_bits is not None:
        args.w = 1 << args.chain_bits

    r = evaluate(
        args.height,
        args.layers,
        args.a,
        args.k,
        args.w,
        args.qs,
        scheme=args.scheme,
        swn=args.swn,
        n=args.n,
        dropped_chains=args.drop_chains,
        cache_height=args.cache_height,
        cache_level_only=args.cache_level_only,
        convention=Convention(not args.uncached),
    )
    if args.json:
        import json

        print(json.dumps(asdict(r), indent=2))
    else:
        print(report(r))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
