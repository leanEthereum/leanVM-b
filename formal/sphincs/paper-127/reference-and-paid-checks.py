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

for n in (4, 6, 10, 20, 50):
    for q in range(1, n // 2 + 1):
        val = F(0)
        for t in reversed(range(q)):
            hazard = 1 - F(n - t - 1, n - t) ** 2
            val = max(F(3, 2 * n) + val, hazard + (1 - hazard) * val)
        explicit = max(F(3 * a, 2 * n) + 1 - F(n - q, n - a) ** 2 for a in range(q + 1))
        assert val == explicit
        x = F(q, n)
        assert val <= 2 * x - x * x / 8
print("Exact paid-probe DP agrees with the closed form and bound for every tested budget.")

r = F(23, 36)
minimum = 28 - 92 * r + 95 * r * r - 24 * r * r * r
assert minimum == F(6767, 3888) > 0
x = F(1, 4096)
prefix = (F(3, 2) + 4 * x + 2 * x * x) / (1 - x) + 4 * x / (1 - x) ** 2 + 82 * x / (1 - x)
encoding = 1 + 3444 * x / (1 - x)
assert prefix == F(52281827327, 34342963200) < F(15, 8)
assert encoding == F(359, 195) < F(15, 8)
x = 3 * F(1, 2**14)
prefix = (F(3, 2) + 4 * x + 2 * x * x) / (1 - x) + 4 * x / (1 - x) ** 2 + 82 * x / (1 - x)
encoding = 1 + 3444 * x / (1 - x)
assert prefix < F(7, 4) and encoding < F(7, 4)
assert x / 8 - F(1, 2**16) == F(1, 2**17)
print("Exact polynomial and small-budget OTS coefficient certificates passed.")
print("These checks support the paper arguments, not a completed Lean or SUF theorem.")
