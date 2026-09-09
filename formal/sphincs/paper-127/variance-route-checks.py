from fractions import Fraction as F


stirling = [[1]]
for degree in range(1, 29):
    previous = stirling[-1]
    stirling.append(
        [0]
        + [
            previous[order - 1] + (order * previous[order] if order < len(previous) else 0)
            for order in range(1, degree + 1)
        ]
    )

rate = F(19, 50)
indices = 2**26
signatures = 2**24
beta = F(1537, 1024)
proposal_slack = signatures // 128
terminal_length = beta * signatures + proposal_slack + 13
assert terminal_length == 25313293
assert terminal_length / indices < rate

moment_bounds = [sum(F(coefficient) * rate**order for order, coefficient in enumerate(row)) for row in stirling]
mean_bound = F(indices, 2**48) * moment_bounds[14]
variance_bound = F(indices, 2**96) * moment_bounds[28]
near_mean_bound = F(14 * indices, 2**38) * moment_bounds[13]
assert mean_bound < F(1, 5)
assert 0 < variance_bound < F(13, 25000)
assert near_mean_bound < 557

delta = F(1, 2**13)
excess_bound = variance_bound / (4 * (F(3, 2) - mean_bound))
assert F(13, 25000) / (4 * (F(3, 2) - F(1, 5))) == F(1, 10000)
assert excess_bound < F(1, 10000) < delta

x_split = F(3, 2**14)
assert x_split * 2**128 == 3 * 2**114
assert F(3, 4) * x_split - delta == F(1, 2**16)
error_per_x = F(1, 2**94) + F(1, 2**109) + F(1, 2**572)
assert error_per_x < F(1, 2**16)

prefix = (
    (F(3, 2) + 4 * x_split + 2 * x_split**2) / (1 - x_split)
    + 4 * x_split / (1 - x_split) ** 2
    + 82 * x_split / (1 - x_split)
)
encoding = 1 + 3444 * x_split / (1 - x_split)
extra_fts = 557 * x_split / (1 - x_split) + x_split / (2 * (1 - x_split) ** 2)
assert max(prefix, encoding, F(1), F(3, 2)) < F(131, 80)
assert extra_fts < F(9, 80)
assert F(131, 80) + F(9, 80) == F(7, 4)
assert F(7, 4) + delta + error_per_x < 2

print("Exact moment and closing inequalities passed.")
print("Full price mean upper bound:", float(mean_bound))
print("Full price variance upper bound:", float(variance_bound))
print("Positive-part upper bound from variance:", float(excess_bound))
print("Near price mean upper bound:", float(near_mean_bound))
print("These rational checks do not prove the probability identities or SUF security.")
