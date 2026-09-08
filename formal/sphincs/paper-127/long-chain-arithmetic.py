from collections import defaultdict
from fractions import Fraction as F
from itertools import product


def suffix_counts(tables, n, y):
    counts = [1]
    good = {y}
    for table in reversed(tables):
        good = {a for a, b in enumerate(table) if b in good}
        counts.append(len(good))
    return list(reversed(counts))


def posterior(tables, n, y):
    mass = [F(1)] * n
    for table in tables:
        following = [F(0)] * n
        for a, b in enumerate(table):
            if b < 0:
                for z in range(n):
                    following[z] += mass[a] / n
            else:
                following[b] += mass[a]
        mass = following
    return mass[y]


def paths_to(tables, stop, value):
    good = {value}
    total = 0
    for j in reversed(range(stop)):
        good = {a for a, b in enumerate(tables[j]) if b in good}
        total += len(good)
    return total


states_checked = transitions_checked = 0
for h in (2, 3, 4):
    n, y = 2, 0
    maps = list(product(range(n), repeat=n))
    aggregate = defaultdict(lambda: [0, 0])
    masks = list(product((False, True), repeat=n))
    for full in product(maps, repeat=h):
        w = suffix_counts(full, n, y)[0]
        for revealed in product(masks, repeat=h):
            partial = tuple(
                tuple(b if seen else -1 for b, seen in zip(table, mask))
                for table, mask in zip(full, revealed)
            )
            aggregate[partial][0] += w
            aggregate[partial][1] += 1
    for tables, (weight, count) in aggregate.items():
        w = posterior(tables, n, y)
        cs = suffix_counts(tables, n, y)
        assert w == F(weight, count)
        assert w <= sum(cs)
        states_checked += 1
        if cs[-3]:
            continue
        k = cs[-2]
        for j in (h - 2, h - 1):
            for a, known in enumerate(tables[j]):
                if known >= 0:
                    continue
                risk = F(0)
                for b in range(n):
                    after = [list(t) for t in tables]
                    after[j][a] = b
                    if suffix_counts(after, n, y)[-3]:
                        risk += posterior(after, n, y) / n
                if j == h - 1:
                    m = sum(b == a for b in tables[h - 2])
                    bound = F(2 + k + paths_to(tables, h - 1, a), n) if m else F(0)
                else:
                    bound = F(k * (k + 2 + paths_to(tables, h - 2, a)), n)
                assert risk <= bound
                transitions_checked += 1

assert F(3, 2) + F(5, 2) * F(1, 16) + F(1, 16) ** 2 / 3 == F(1273, 768)
assert F(1273, 768) < F(7, 4)
print(f"Exact posterior checks passed on {states_checked} partial chain tables.")
print(f"Exact first-success hazard bounds passed on {transitions_checked} transitions.")
print("These checks support the paper lemma for an isolated chain, not full SPHINCS security.")
