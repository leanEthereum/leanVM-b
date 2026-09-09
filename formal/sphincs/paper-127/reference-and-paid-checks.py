from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product


n, attempts = 3, 2
valid = {0, 1}
checked = 0
for table in product(range(n), repeat=n * attempts):
    for message in range(n):
        reference = table[message * attempts : (message + 1) * attempts]
        selected = next((j for j, word in enumerate(reference) if word in valid), None)
        for digit in valid:
            for counter in (0, 1, None):
                old = F(0)
                if selected == counter and (counter is None or reference[counter] == digit):
                    old = F(1, n ** len(table))
                    if counter is None:
                        old /= len(valid)
                chance_j = F(1, 3) ** attempts if counter is None else F(1, 3) ** counter * F(2, 3)
                new = chance_j / len(valid)
                for m in range(n):
                    for c in range(attempts):
                        word = table[m * attempts + c]
                        if m == message and (counter is None or c < counter):
                            new *= F(1 if word not in valid else 0, n - len(valid))
                        elif m == message and c == counter:
                            new *= int(word == digit)
                        else:
                            new /= n
                assert old == new
                checked += 1
print(f"Exact conditional reference-table laws agree on {checked} augmented outcomes.")

n = 3
values = tuple(range(n))
tables = tuple(product(values, repeat=n))
original = Counter((secret, first, second) for secret in values for first in tables for second in tables)
planted = Counter()
for secret, middle, endpoint in product(values, repeat=3):
    for off_rows in product(values, repeat=2 * (n - 1)):
        remaining = iter(off_rows)
        first = tuple(middle if z == secret else next(remaining) for z in values)
        second = tuple(endpoint if z == middle else next(remaining) for z in values)
        planted[secret, first, second] += 1
assert original == planted
print(f"Original and planted two-edge graph laws agree on {sum(original.values())} full states.")

actions = tuple(product(range(2), values)) + ((2, 0),)
posterior_groups = 0
for action_pair in product(actions, repeat=2):
    grouped = defaultdict(Counter)
    for secret, first, second in original:
        middle = first[secret]
        endpoint = second[middle]
        hidden = {0: set(values), 1: set(values)}
        observations = [endpoint]
        for domain, candidate in action_pair:
            if domain == 2:
                observations.append(middle)
                hidden.pop(1, None)
                continue
            child = (secret, middle)[domain]
            parent = (middle, endpoint)[domain]
            answer = (first, second)[domain][candidate]
            if (domain in hidden and candidate == child) or (candidate != child and answer == parent):
                break
            observations.append(answer)
            if domain in hidden:
                hidden[domain].discard(candidate)
            if domain == 0 and 1 in hidden:
                hidden[1].discard(answer)
        else:
            possible = tuple((coordinate, tuple(sorted(choices))) for coordinate, choices in sorted(hidden.items()))
            actual = tuple((secret, middle)[coordinate] for coordinate in sorted(hidden))
            grouped[tuple(observations), possible][actual] += 1
    for (_, possible), counts in grouped.items():
        expected_support = set(product(*(choices for _, choices in possible)))
        assert set(counts) == expected_support
        assert len(set(counts.values())) == 1
        posterior_groups += 1
print(f"Surviving graph posteriors factor in {posterior_groups} groups, including repeats and disclosure.")

states = 0
for n in range(2, 81):
    value = {}
    for k in range(n // 2 + 1):
        for r in range(n // 2 - k + 1):
            if k == 0:
                value[r, k] = F(0)
            else:
                hazard = 1 - F(n - r - 1, n - r) ** 2
                value[r, k] = max(F(3, 2 * n) + value[r, k - 1], hazard + (1 - hazard) * value[r + 1, k - 1])
            explicit = max(F(3 * a, 2 * n) + 1 - F(n - r - k + a, n - r) ** 2 for a in range(k + 1))
            assert value[r, k] == explicit < 1
            states += 1
            if r == 0:
                x = F(k, n)
                upper = 2 * x - x**2 + max(x - F(1, 4), F(0)) ** 2
                assert value[r, k] <= upper <= 2 * x - F(3, 4) * x**2
print(f"Exact probe-count DP agrees with its paid-prefix formula and bound in {states} reachable states.")

x = F(1, 2**15)
prefix = (F(3, 2) + 4 * x + 2 * x**2) / (1 - x) + 4 * x / (1 - x) ** 2 + 82 * x / (1 - x)
encoding = 1 + 3444 * x / (1 - x)
assert max(prefix, encoding, F(3, 2)) < F(131, 80)
assert 557 * x / (1 - x) + x / (2 * (1 - x) ** 2) < F(9, 80)
assert F(3, 4) * x - F(1, 2**16) == F(1, 2**17)
error_per_x = F(1, 2**94) + F(1, 2**109) + F(1, 2**572)
assert error_per_x < F(1, 2**17)
assert F(131, 80) + F(9, 80) + F(1, 2**16) + error_per_x < 2
print("Exact current split, OTS and FTS coefficient, and exceptional-allowance certificates passed.")
print("These checks support the paper arguments, not a completed Lean or SUF theorem.")
