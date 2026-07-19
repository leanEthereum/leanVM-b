# A miniature WOTS-style chain walk bundling the DSL's moving parts: a
# runtime digit is range-checked (dispatch soundness), then match_range
# dispatches it to a Const-specialized walker whose BLAKE3 chain is unrolled
# over heap slices (a 256-bit BLAKE3 value occupies two canonical cells);
# the walker also builds g^{2n} at runtime (unrolled MULs) to read its final
# pair back through g-power indexing. The recomputation at the end lands on an
# already-written StackBuf pair, so write-once turns the hash into a digest
# assertion; the dead `if` branch holds an impossible assert that must never
# execute. Published: the two 128-bit digest cells of H^2(5, 7).
# public_input: 6435064747262329193, 5487635915178971307, 11033477629434050085, 10814665273705721660
from snark_lib import *


def main():
    buf = HeapBuf(16)
    buf[1] = 5
    buf[GEN] = 0
    buf[GEN ** 2] = 7
    buf[GEN ** 3] = 0
    d = GEN ** 2  # the runtime digit
    assert log(d) < 4  # bound the scrutinee before dispatching on it
    t0, t1, t2, t3 = match_range(log(d), range(0, 4), lambda i: walk(buf, i))
    if d != GEN ** 2:
        assert 1 == 0  # dead branch: never executes
    v = StackBuf(4)
    v[0] = t0
    v[1] = t1
    v[2] = t2
    v[3] = t3
    blake3(buf[4:8], buf[4:8], v)
    p = GEN ** 0
    p[1] = t0
    p[GEN] = t1
    p[GEN ** 2] = t2
    p[GEN ** 3] = t3
    return


def walk(buf, n: Const):
    p = 1
    for i in unroll(0, n):
        blake3(buf[i * 4:i * 4 + 4], buf[i * 4:i * 4 + 4], buf[i * 4 + 4:i * 4 + 8])
        p = p * GEN * GEN * GEN * GEN
    return buf[p], buf[p * GEN], buf[p * GEN ** 2], buf[p * GEN ** 3]
