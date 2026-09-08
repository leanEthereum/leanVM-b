from fractions import Fraction as F
from itertools import product
from collections import defaultdict

N = 3
target = 0
functions = list(product(range(N), repeat=N))
aggregates = defaultdict(lambda: [0, 0])
for f in functions:
    for g in functions:
        weight = sum(g[f[s]] == target for s in range(N))
        for mask_f in range(1 << N):
            partial_f = tuple(f[i] if mask_f >> i & 1 else None for i in range(N))
            for mask_g in range(1 << N):
                partial_g = tuple(g[i] if mask_g >> i & 1 else None for i in range(N))
                item = aggregates[(partial_f, partial_g)]
                item[0] += weight
                item[1] += 1


def statistics(f, g):
    a = sum(v is not None for v in f)
    b = sum(v is not None for v in g)
    targets = {i for i, v in enumerate(g) if v == target}
    k = len(targets)
    completed = sum(v in targets for v in f if v is not None)
    pending = sum(g[v] is None for v in f if v is not None)
    return a, b, k, completed, pending


def likelihood(f, g):
    a, b, k, completed, pending = statistics(f, g)
    return completed + F(pending, N) + (1 - F(a, N)) * (k + 1 - F(b, N))


transitions = 0
for (f, g), (weight, count) in aggregates.items():
    assert F(weight, count) == likelihood(f, g)
    a, b, k, completed, pending = statistics(f, g)
    if completed:
        continue
    for z in range(N):
        if g[z] is not None:
            continue
        m = sum(value == z for value in f)
        risk = F(0)
        for answer in range(N):
            next_g = list(g)
            next_g[z] = answer
            if statistics(f, next_g)[3]:
                risk += likelihood(f, next_g) / N
        if m:
            expected = F(m, N) + F(pending - m, N * N) + (1 - F(a, N)) * (k + 2 - F(b + 1, N)) / N
            assert risk == expected
            assert risk <= F(m + 2 + k, N)
        else:
            assert risk == 0
        transitions += 1
    for z in range(N):
        if f[z] is not None:
            continue
        risk = F(0)
        for answer in range(N):
            next_f = list(f)
            next_f[z] = answer
            if statistics(next_f, g)[3]:
                risk += likelihood(next_f, g) / N
        assert risk == F(k, N) * (1 + F(pending, N) + (1 - F(a + 1, N)) * (k + 1 - F(b, N)))
        assert risk <= F(k * (k + 2), N)
        transitions += 1

assert F(3, 2) + F(3, 2) * F(1, 8) + F(1, 3) * F(1, 8)**2 == F(325, 192)
assert F(325, 192) < F(7, 4)
print(f'Exact likelihood checks passed on {len(aggregates)} partial table pairs.')
print(f'Exact weighted-risk checks passed on {transitions} fresh-query transitions before success.')
print('The general proof is in two-hop-inversion.md; this check does not prove full SUF.')
