#!/usr/bin/env python3
"""Search the SPHINCS+ parameter space for the cheapest verification.

Given a lifetime and a budget for each of the other four costs:

    --lifetime          log2 of the signatures allowed under one public key
    --max-keygen        hashes at key generation
    --max-sign          hashes at signing, vanilla
    --max-sign-cached   hashes at signing with the top tree's half top cached
    --max-size          signature bytes

this enumerates the parameter space and reports the sets that minimize
verification cost subject to NIST level 1 security (128-bit classical, the
SLH-DSA level 1 target), computed the same way as in the report: the FORS
subset-forgery sum of security.sage, which must reach 128 bits at the given
lifetime, capped by the 2^-n preimage bound.

The cost model is sphincs_params.py; this file only searches. Schemes are that
module's SPX / W+C / W+C_F+C, and the WOTS+C digest cut is its bit-pinning
Encoding, so --chain-bits and --drop-chains span the same axes here.

Two facts keep the space small enough to brute force in Python:

  * k is not searched. For a fixed (h, a) the forgery exponent is increasing in
    k while size, signing and verification all grow with it, so the only k worth
    considering is the smallest one that reaches the security target. That turns
    a 2-D (a, k) sweep into a 1-D one plus a cached binary search on k.

  * S_wn is not searched either. Verification is strictly decreasing in it and
    the grinding is increasing in it above the mean, so the best S_wn is simply
    the largest one whose grinding still fits the signing budgets: another
    binary search, not an axis.

What remains is (scheme, h, d | h, chain_bits, dropped_chains, a), pruned by
keygen before a is reached and by size and signing before S_wn is. Run with
--stats to see how big the space actually was; if a wider grid is wanted than
Python will sit through, this is the file to port, not the cost model.
"""

from __future__ import annotations

import argparse
import os
import sys
import time
from dataclasses import dataclass
from functools import lru_cache
from math import log2

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sphincs_params import SCHEMES, Convention, Costs, Encoding, costs, evaluate, fors_forgery_exponent, report

LEVEL1_BITS = 128  # NIST level 1, matching SLH-DSA's level 1 parameter sets


# ---------------------------------------------------------------------------
# Constraints and grid
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Budgets:
    lifetime: int  # log2 of the signatures per public key
    max_keygen: int
    max_sign: int
    max_sign_cached: int
    max_size: int
    security: float = LEVEL1_BITS
    unit: str = "hashes"  # "hashes" or "compressions", for the budgets and the objective

    def of(self, cost) -> int:
        return getattr(cost, self.unit)


@dataclass(frozen=True)
class Grid:
    schemes: tuple[str, ...] = SCHEMES
    n: int = 16
    h_min: int = 1
    h_max: int = 96
    a_min: int = 1
    a_max: int = 32
    k_max: int = 64
    chain_bits: tuple[int, ...] = (1, 2, 3, 4, 5, 6, 7, 8)
    max_dropped: int = 8
    cache_level_only: bool = False


@dataclass
class Candidate:
    scheme: str
    h: int
    d: int
    a: int
    k: int
    w: int
    dropped_chains: int
    c: Costs

    @property
    def swn(self) -> int | None:
        return self.c.swn


# ---------------------------------------------------------------------------
# Security: the smallest secure k for a given (h, a)
# ---------------------------------------------------------------------------


@lru_cache(maxsize=1 << 16)
def min_secure_k(lifetime: int, h: int, a: int, target: float, k_max: int) -> int | None:
    """Smallest k reaching `target` bits, or None if no k <= k_max does.

    The forgery exponent is increasing in k: each extra FORS tree is one more
    tree whose required leaf the adversary needs already opened. So the feasible
    k form an up-set and a binary search finds its floor.
    """
    try:
        if fors_forgery_exponent(lifetime, h, k_max, a) < target:
            return None
    except ValueError:
        return None  # q_s so far past 2^h that the sum does not converge
    lo, hi = 1, k_max  # invariant: hi secure
    while lo < hi:
        mid = (lo + hi) // 2
        if fors_forgery_exponent(lifetime, h, mid, a) >= target:
            hi = mid
        else:
            lo = mid + 1
    return lo


# ---------------------------------------------------------------------------
# Search
# ---------------------------------------------------------------------------


@dataclass
class Stats:
    grid: int = 0  # (scheme, h, d, chain_bits, dropped) tuples visited
    keygen_pruned: int = 0
    insecure: int = 0  # a-loop iterations, not distinct (h, a) pairs
    size_pruned: int = 0
    sign_pruned: int = 0
    evaluated: int = 0  # candidates that got an S_wn search
    costs_calls: int = 0
    seconds: float = 0.0

    def __str__(self) -> str:
        return (
            f"grid {self.grid} (scheme, h, d, chain_bits, dropped) tuples, "
            f"{self.keygen_pruned} over keygen budget; then, over the a loop, {self.insecure} with no secure k, "
            f"{self.size_pruned} over size, {self.sign_pruned} over signing, "
            f"{self.evaluated} costed with an S_wn search ({self.costs_calls} cost-model calls) in {self.seconds:.1f}s"
        )


def _divisors(h: int) -> list[int]:
    return [d for d in range(1, h + 1) if h % d == 0]


def search(b: Budgets, g: Grid | None = None, stats: Stats | None = None) -> list[Candidate]:
    """Every feasible parameter set, ordered by verification cost."""
    g = g or Grid()
    st = stats if stats is not None else Stats()
    started = time.perf_counter()
    cv = Convention()
    found: list[Candidate] = []

    def cost(scheme, h, d, a, k, w, dropped, swn) -> Costs:
        st.costs_calls += 1
        return costs(h, d, a, k, w, scheme, swn, g.n, dropped, None, g.cache_level_only, cv)

    # Necessary conditions, used only to bound the grid. The signature carries
    # h authentication nodes, so h <= max_size/n; signing grows a FORS tree of
    # 2^a leaves, so 2^a <= max_sign. Anything outside cannot become feasible.
    h_max = min(g.h_max, b.max_size // g.n)
    a_max = min(g.a_max, int(log2(max(b.max_sign, 2))))

    for scheme in g.schemes:
        spx = scheme == "SPX"
        for h in range(g.h_min, h_max + 1):
            for d in _divisors(h):
                for bits in g.chain_bits:
                    w = 1 << bits
                    # WOTS-TW has no counter to grind, so it cannot drop chains,
                    # and WOTS+C has to keep at least one.
                    max_dropped = 0 if spx else min(g.max_dropped, Encoding(w, g.n).chains - 1)
                    for dropped in range(max_dropped + 1):
                        st.grid += 1
                        # keygen needs no a, k: one top tree of 2^(h/d) leaves
                        probe = cost(scheme, h, d, g.a_min, 2, w, dropped, None)
                        if b.of(probe.keygen) > b.max_keygen:
                            st.keygen_pruned += 1
                            continue
                        for a in range(g.a_min, a_max + 1):
                            k = min_secure_k(b.lifetime, h, a, b.security, g.k_max)
                            if k is None:
                                st.insecure += 1
                                continue
                            if scheme == "W+C_F+C":
                                k = max(k, 2)  # FORS+C signs k-1 of them
                            c = cost(scheme, h, d, a, k, w, dropped, None)
                            if c.sig_bytes > b.max_size:
                                st.size_pruned += 1
                                continue
                            if b.of(c.sign) > b.max_sign or b.of(c.sign_cached) > b.max_sign_cached:
                                st.sign_pruned += 1  # the mean S_wn grinds least, so no S_wn fits
                                continue
                            st.evaluated += 1
                            if not spx:
                                c = _push_swn(b, cost, scheme, h, d, a, k, w, dropped, c)
                            found.append(Candidate(scheme, h, d, a, k, w, dropped, c))

    st.seconds = time.perf_counter() - started
    found.sort(key=lambda cand: (b.of(cand.c.verify), cand.c.sig_bytes, b.of(cand.c.sign)))
    return found


def _push_swn(b: Budgets, cost, scheme, h, d, a, k, w, dropped, at_mean: Costs) -> Costs:
    """Raise S_wn as far as the signing budgets allow, which is where verification is cheapest.

    Verification walks (w-1)*l - S_wn chain steps, so it falls by d for every
    step S_wn gains, while the grinding rises monotonically above the mean.
    `at_mean` is feasible by construction, so this is a binary search on an
    up-set with a known floor.
    """
    lo = at_mean.swn or 0
    hi = at_mean.l * (w - 1)
    best = at_mean
    while lo < hi:
        mid = (lo + hi + 1) // 2
        c = cost(scheme, h, d, a, k, w, dropped, mid)
        if b.of(c.sign) <= b.max_sign and b.of(c.sign_cached) <= b.max_sign_cached:
            lo, best = mid, c
        else:
            hi = mid - 1
    return best


# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------


def _si(x: float) -> str:
    for unit, div in (("G", 1e9), ("M", 1e6), ("K", 1e3)):
        if x >= div:
            return f"{x / div:.2f}{unit}"
    return str(int(x))


COLUMNS = (
    ("verify", 9, lambda b, c: _si(b.of(c.c.verify))),
    ("scheme", 9, lambda b, c: c.scheme),
    ("h", 4, lambda b, c: str(c.h)),
    ("d", 3, lambda b, c: str(c.d)),
    ("h'", 4, lambda b, c: str(c.h // c.d)),
    ("a", 3, lambda b, c: str(c.a)),
    ("k", 3, lambda b, c: str(c.k)),
    ("cb", 3, lambda b, c: str(c.c.chain_bits)),
    ("drop", 5, lambda b, c: str(c.dropped_chains)),
    ("l", 4, lambda b, c: str(c.c.l)),
    ("S_wn", 6, lambda b, c: "-" if c.swn is None else str(c.swn)),
    ("size", 6, lambda b, c: str(c.c.sig_bytes)),
    ("keygen", 8, lambda b, c: _si(b.of(c.c.keygen))),
    ("sign", 8, lambda b, c: _si(b.of(c.c.sign))),
    ("sign$", 8, lambda b, c: _si(b.of(c.c.sign_cached))),
    ("state", 7, lambda b, c: str(c.c.cache_bytes)),
)


def table(b: Budgets, cands: list[Candidate]) -> str:
    lines = [" ".join(name.rjust(width) for name, width, _ in COLUMNS)]
    lines.append("-" * len(lines[0]))
    for c in cands:
        lines.append(" ".join(fmt(b, c).rjust(width) for _, width, fmt in COLUMNS))
    return "\n".join(lines)


def utilization(b: Budgets, c: Candidate) -> str:
    used = (
        ("keygen", b.of(c.c.keygen), b.max_keygen),
        ("sign", b.of(c.c.sign), b.max_sign),
        ("sign cached", b.of(c.c.sign_cached), b.max_sign_cached),
        ("size", c.c.sig_bytes, b.max_size),
    )
    return ", ".join(f"{name} {100 * v / lim:.0f}%" for name, v, lim in used if lim)


# ---------------------------------------------------------------------------
# Self-test: the two shortcuts above are exact, checked against exhaustion
# ---------------------------------------------------------------------------


def exhaustive(b: Budgets, g: Grid) -> list[Candidate]:
    """The same search with nothing pruned: every k, every S_wn.

    Only usable on a tiny grid, which is the point: it is what the pruned
    search is diffed against.
    """
    cv = Convention()
    found: list[Candidate] = []
    for scheme in g.schemes:
        spx = scheme == "SPX"
        for h in range(g.h_min, g.h_max + 1):
            for d in _divisors(h):
                for bits in g.chain_bits:
                    w = 1 << bits
                    for dropped in range(1 if spx else g.max_dropped + 1):
                        l = Encoding(w, g.n, dropped).chains
                        for a in range(g.a_min, g.a_max + 1):
                            for k in range(2 if scheme == "W+C_F+C" else 1, g.k_max + 1):
                                if fors_forgery_exponent(b.lifetime, h, k, a) < b.security:
                                    continue
                                for swn in [None] if spx else range(l * (w - 1) + 1):
                                    c = costs(h, d, a, k, w, scheme, swn, g.n, dropped, None, g.cache_level_only, cv)
                                    if c.sig_bytes > b.max_size or b.of(c.keygen) > b.max_keygen:
                                        continue
                                    if b.of(c.sign) > b.max_sign or b.of(c.sign_cached) > b.max_sign_cached:
                                        continue
                                    found.append(Candidate(scheme, h, d, a, k, w, dropped, c))
    found.sort(key=lambda cand: (b.of(cand.c.verify), cand.c.sig_bytes, b.of(cand.c.sign)))
    return found


def selftest() -> int:
    fails = 0

    def check(name, got, want):
        nonlocal fails
        ok = got == want
        fails += not ok
        if not ok:
            print(f"FAIL {name}: got {got}, want {want}")

    # 1. The digit-sum count is unimodal with its peak at the mean, so grinding
    #    only rises above the mean and the S_wn binary search cannot skip an
    #    admissible larger S_wn.
    for bits in (1, 2, 3, 4, 8):
        w = 1 << bits
        enc = Encoding(w, 16)
        mean, top = enc.default_swn, enc.chains * (w - 1)
        nus = [enc.admissible(s) for s in range(mean, min(top, mean + 60) + 1)]
        check(f"nu non-increasing above the mean (w={w})", nus == sorted(nus, reverse=True), True)
        check(f"nu peaks at the mean (w={w})", enc.admissible(mean) >= enc.admissible(mean - 1), True)

    # 2. min_secure_k is the floor of the secure k, by linear scan.
    for h, a in ((20, 10), (24, 12), (30, 14)):
        k = min_secure_k(20, h, a, LEVEL1_BITS, 32)
        scan = next((kk for kk in range(1, 33) if fors_forgery_exponent(20, h, kk, a) >= LEVEL1_BITS), None)
        check(f"min_secure_k(h={h}, a={a})", k, scan)

    # 3. On a grid small enough to exhaust, the pruned search finds the same
    #    optimum as the sweep over every k and every S_wn.
    b = Budgets(lifetime=20, max_keygen=3_000_000, max_sign=10_000_000, max_sign_cached=10_000_000, max_size=4_000)
    g = Grid(schemes=("W+C", "W+C_F+C"), h_min=20, h_max=20, a_min=14, a_max=16, k_max=14, chain_bits=(4,), max_dropped=1)
    pruned, full = search(b, g), exhaustive(b, g)
    check("exhaustive agrees on the optimum", b.of(pruned[0].c.verify), b.of(full[0].c.verify))
    check(
        "exhaustive agrees on the winner",
        (pruned[0].scheme, pruned[0].h, pruned[0].d, pruned[0].a, pruned[0].k, pruned[0].w, pruned[0].swn),
        (full[0].scheme, full[0].h, full[0].d, full[0].a, full[0].k, full[0].w, full[0].swn),
    )

    print("selftest: " + ("all checks passed" if not fails else f"{fails} failures"))
    return fails


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _budget(text: str) -> int:
    return int(float(text))


def main() -> int:
    p = argparse.ArgumentParser(
        description=(__doc__ or "").splitlines()[0],
        epilog="example: search.py --lifetime 30 --max-keygen 2e6 --max-sign 6e6 --max-sign-cached 4e6 --max-size 4000",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("--lifetime", type=int, default=None, metavar="LOG2", help="log2 of the signatures allowed per public key")
    p.add_argument("--max-keygen", type=_budget, default=None, metavar="N", help="budget for keygen")
    p.add_argument("--max-sign", type=_budget, default=None, metavar="N", help="budget for average signing")
    p.add_argument("--max-sign-cached", type=_budget, default=None, metavar="N", help="budget for average signing with the half top cached")
    p.add_argument("--max-size", type=_budget, default=None, metavar="B", help="budget for the signature, in bytes")
    p.add_argument(
        "--security", type=float, default=LEVEL1_BITS, metavar="BITS", help=f"classical security floor (default {LEVEL1_BITS}, NIST level 1)"
    )
    p.add_argument("--unit", choices=("hashes", "compressions"), default="hashes", help="unit of every budget and of the objective (default hashes)")
    p.add_argument("--scheme", action="append", choices=SCHEMES, help="restrict the schemes searched (repeatable, default all)")
    p.add_argument("-n", type=int, default=16, help="hash output in bytes (default 16)")
    p.add_argument("--top", type=int, default=15, help="rows to print (default 15)")
    p.add_argument("--h-max", type=int, default=Grid.h_max, help=f"largest hypertree height searched (default {Grid.h_max})")
    p.add_argument("--a-max", type=int, default=Grid.a_max, help=f"largest FORS a searched (default {Grid.a_max})")
    p.add_argument("--k-max", type=int, default=Grid.k_max, help=f"largest FORS k considered secure (default {Grid.k_max})")
    p.add_argument("--chain-bits", type=int, action="append", metavar="B", help="restrict log2(w) searched (repeatable, default 1..8)")
    p.add_argument("--max-dropped", type=int, default=Grid.max_dropped, help=f"most WOTS+C chains dropped (default {Grid.max_dropped})")
    p.add_argument("--cache-level-only", action="store_true", help="cache one top-tree level rather than it and everything above")
    p.add_argument("--stats", action="store_true", help="report how much of the space was visited")
    p.add_argument("--selftest", action="store_true", help="check the k and S_wn shortcuts against an exhaustive sweep")
    args = p.parse_args()

    if args.selftest:
        return 1 if selftest() else 0
    missing = [f for f in ("lifetime", "max_keygen", "max_sign", "max_sign_cached", "max_size") if getattr(args, f) is None]
    if missing:
        p.error("required unless --selftest: " + ", ".join("--" + f.replace("_", "-") for f in missing))

    b = Budgets(
        lifetime=args.lifetime,
        max_keygen=args.max_keygen,
        max_sign=args.max_sign,
        max_sign_cached=args.max_sign_cached,
        max_size=args.max_size,
        security=args.security,
        unit=args.unit,
    )
    g = Grid(
        schemes=tuple(args.scheme) if args.scheme else SCHEMES,
        n=args.n,
        h_max=args.h_max,
        a_max=args.a_max,
        k_max=args.k_max,
        chain_bits=tuple(sorted(set(args.chain_bits))) if args.chain_bits else Grid.chain_bits,
        max_dropped=args.max_dropped,
        cache_level_only=args.cache_level_only,
    )

    stats = Stats()
    found = search(b, g, stats)
    if args.stats:
        print(stats)
        print()
    if not found:
        print("no parameter set meets these budgets at " + f"{b.security:g}-bit security and q_s = 2^{b.lifetime}")
        print("the binding budget is usually size or keygen; --stats says which pruned everything")
        return 1

    print(f"{len(found)} feasible sets, best {min(args.top, len(found))} by verification {b.unit}:")
    print()
    print(table(b, found[: args.top]))
    print()

    best = found[0]
    print(f"budget use of the best: {utilization(b, best)}")
    print()
    r = evaluate(
        best.h,
        best.d,
        best.a,
        best.k,
        best.w,
        b.lifetime,
        scheme=best.scheme,
        swn=best.swn,
        n=g.n,
        dropped_chains=best.dropped_chains,
        cache_level_only=g.cache_level_only,
    )
    print(report(r))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
