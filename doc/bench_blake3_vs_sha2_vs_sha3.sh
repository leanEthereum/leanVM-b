#!/usr/bin/env bash
#
#   ./doc/bench_blake3_vs_sha2_vs_sha3.sh
#
# Compares the three candidate hashes on the branch that implements each:
# BLAKE2s (main), SHA-256 (sha2), Keccak (sha3). Every branch is fetched and
# fast-forwarded first, then measured four ways:
#
#   raw hashing, from `multithreaded_throughput`, which reports one 64-byte
#     input per compression (per permutation, for Keccak). Run HASH_RUNS times,
#     best kept: the test already medians its own passes, so a low run is the
#     machine being busy rather than the hash being slow. From it comes the
#     compression rate, and the time to generate one XMSS key over a
#     2^LOG_LIFETIME lifetime at COMPRESSIONS compressions per epoch. Comparing
#     the three rates, mind that a 64-byte hash is one compression for BLAKE2s
#     and one permutation for Keccak, but two compressions for SHA-256, whose
#     padding spills a 64-byte input into a second block.
#
#   proving that hashing, from flock's `hash_batch_prove_verify`, whose
#     throughput line counts compressions (permutations, for Keccak) proven per
#     second, with none of the VM around it.
#
#   XMSS aggregation, SPHINCS aggregation, and REC_N-to-1 recursion over leaves
#     of XMSS aggregates. None of the three counts is the same on every branch:
#     each is whatever fills a proof of the same proven size, so a costlier hash
#     fits fewer signatures, as does flock's batch, and the counts below are the
#     ones each branch's
#     README quotes. Comparing them means comparing signatures per second, not
#     proving times, the recursion rate counting every signature the node covers
#     (REC_N leaves of XMSS_PER_LEAF).
#
# Wrapped in braces so bash parses the whole file before running it: checking
# out a branch where this script does not exist would otherwise pull the rest of
# it out from under the interpreter.
{
set -euo pipefail

HASH_RUNS=5          # hash-throughput runs per branch, best kept
HASH_COOLDOWN=10     # seconds between them, to let the machine settle
LOG_LIFETIME=30      # XMSS lifetime, as log2 of the number of epochs
COMPRESSIONS=390     # compressions per epoch of an XMSS keygen

REPEAT=5             # measured proving passes per benchmark, after a warmup
COOLDOWN=5           # idle seconds before each of them
LOG_INV_RATE=1       # for the two aggregations
REC_LOG_INV_RATE=2   # for recursion
REC_N=2              # child aggregates per recursion node

BRANCHES=(main    sha2    sha3)
HASHES=(  BLAKE2s SHA-256 Keccak)
XMSS=(    900     450     205)   # signatures per leaf, per that branch's README
SPHINCS=( 245     122     55)    # likewise, a leaf of SPHINCS signatures
PER_LEAF=(900     900     450)   # likewise, the XMSS leaves a recursion node covers
FLOCK_LOG=(18     17      16)    # likewise, log2 of flock's batch of compressions

TEST=multithreaded_throughput
PACKAGE=primitives
BIN=hash_bench

cd "$(dirname "$0")/.."

if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
    echo "working tree has changes; commit or stash them first" >&2
    exit 1
fi
start=$(git symbolic-ref --quiet --short HEAD || git rev-parse HEAD)

# Two of these at once check out branches under each other, so the runs measure
# whatever branch the other one left in the tree. Take the lock before the first
# checkout, and before arming the trap that undoes it.
LOCK="$(git rev-parse --git-dir)/bench.lock"
if ! mkdir "$LOCK" 2>/dev/null; then
    echo "another ./doc/bench.sh is running; wait for it, or remove $LOCK" >&2
    exit 1
fi
trap 'rmdir "$LOCK"; git checkout --quiet "$start"' EXIT INT TERM

git fetch --quiet --all

# The number following $1 in $2, commas stripped.
num() {
    local line
    line=$(grep -m1 "$1" <<<"$2") || { echo "no \"$1\" line in the output" >&2; exit 1; }
    sed -E "s#.*$1[^0-9]*([0-9,]+(\.[0-9]+)?).*#\1#" <<<"$line" | tr -d ','
}

# Best of HASH_RUNS `multithreaded_throughput` runs, in Mhash/s.
hash_rate() {
    local r out line
    local results=()
    for ((r = 1; r <= HASH_RUNS; r++)); do
        out=$(cargo test --release -p "$PACKAGE" --test "$BIN" "$TEST" -- --exact --ignored --nocapture)
        line=$(grep -m1 'Mhash/s' <<<"$out") || { echo "no measurement in the output" >&2; exit 1; }
        results+=("$(sed -E 's#.*[^0-9.]([0-9]+(\.[0-9]+)?) Mhash/s.*#\1#' <<<"$line")")
        printf 'run %d/%d: %s\n' "$r" "$HASH_RUNS" "$line" >&2
        if ((r < HASH_RUNS)); then sleep "$HASH_COOLDOWN"; fi
    done
    printf 'samples: %s\n' "${results[*]}" >&2
    printf '%s\n' "${results[@]}" | sort -g | tail -1
}

# `aggregate` of $1 signatures of scheme $2, in signatures per second.
aggregate() {
    local out
    out=$(cargo run --release -- aggregate "--$2" "$1" --log-inv-rate "$LOG_INV_RATE" \
        --repeat "$REPEAT" --cooldown "$COOLDOWN")
    echo "$out" >&2
    num 'per signature' "$out"
}

# Flock's batch proving of 2^$1 compressions, in compressions per second.
flock_rate() {
    local out
    out=$(BENCH_REPEAT="$REPEAT" BENCH_COOLDOWN="$COOLDOWN" FLOCK_N_LOG="$1" \
        cargo test --release --package flock --test batch_proving_hashes -- \
        hash_batch_prove_verify --exact --nocapture --include-ignored)
    echo "$out" >&2
    num 'throughput' "$out"
}

# `recursion` over REC_N leaves of $1 XMSS signatures, in seconds.
recursion() {
    local out
    out=$(cargo run --release -- recursion --n "$REC_N" --xmss-per-leaf "$1" \
        --log-inv-rate "$REC_LOG_INV_RATE" --repeat "$REPEAT" --cooldown "$COOLDOWN")
    echo "$out" >&2
    num 'proving time' "$out"
}

rows=""
for i in "${!BRANCHES[@]}"; do
    b=${BRANCHES[$i]}
    git checkout --quiet "$b"
    git merge --quiet --ff-only "origin/$b"
    echo "=== $b ==="
    rows+=$(printf '%s\t%s\t%s\t%s\t%s\t%s\t%s %s\n' \
        "$b" "${HASHES[$i]}" "$(hash_rate)" "$(flock_rate "${FLOCK_LOG[$i]}")" \
        "$(aggregate "${XMSS[$i]}" xmss)" "$(aggregate "${SPHINCS[$i]}" sphincs)" \
        "${PER_LEAF[$i]}" "$(recursion "${PER_LEAF[$i]}")")$'\n'
    echo
done

awk -F'\t' -v l="$LOG_LIFETIME" -v c="$COMPRESSIONS" -v n="$REC_N" '
function dur(t) {
    if (t < 60)         return sprintf("%.1f s", t)
    else if (t < 3600)  return sprintf("%.1f min", t / 60)
    else if (t < 86400) return sprintf("%.1f h", t / 3600)
    else                return sprintf("%.1f days", t / 86400)
}
BEGIN { printf "%-6s %-8s %10s %10s %20s %9s %11s\n", "branch", "hash", "compr/s", "proven/s",
        sprintf("keygen (2^%d)", l), "XMSS/s", "SPHINCS/s" }
{
    split($7, r, " ")
    t = 2 ^ l * c / ($3 * 1e6)
    printf "%-6s %-8s %8.0f M %8.0f K %20s %9.0f %11.0f\n", $1, $2, $3, $4 / 1e3,
        sprintf("%.0f s (%s)", t, dur(t)), $5, $6
    recs = recs sprintf("%-6s %-8s %10d %9.3f s\n", $1, $2, r[1], r[2])
}
END { printf "\n%-6s %-8s %10s %11s\n%s", "branch", "hash", "XMSS/leaf", sprintf("%d->1", n), recs }
' <<<"${rows%$'\n'}"
}
