from fractions import Fraction as F
from math import comb, factorial


N, I, L, S = 2**128, 2**26, 1024, 2**24
q_max = N // 2
arrival = F(1, L * I)
rho = F(1025, 1024) * F(L, N)
beta = F(1537, 1024)
v_max = F(1, I) + rho * (arrival * q_max + 2**80 + S + 14)
assert 0 < v_max < 1
assert v_max / (1 - v_max) < beta / I
clock_mean = beta * F(S + S // 128, I)
assert clock_mean == F(198273, 524288) < F(19, 50)
clock_exponent = F(S, 2 * 128 * 127) - F(S, 128**2)
assert clock_exponent == -F(64512, 127) < -500
assert sum(F(500**j, factorial(j)) for j in range(1001)) > 2**700
assert 14 * sum(2 ** (h + 1) - 1 for h in range(10)) == 28504 > L

acceptance_floor = F(1, L) * (1 - F(2**93 + 2**32, N))
assert 1 / (N * acceptance_floor) < rho
cache_error_per_query = F(3 * q_max, 2**366) + F(1, 2**330)
deficit_error_per_query = F(4 * L**2 * (q_max - 1) + 3 * L**3, 2**372)
assert cache_error_per_query < F(1, 2**237)
assert deficit_error_per_query < F(1, 2**222)

stirling = [[1]]
for k in range(1, 15):
    previous = stirling[-1]
    row = [0] * (k + 1)
    for j in range(1, k + 1):
        row[j] = previous[j - 1] + (j * previous[j] if j < k else 0)
        assert row[j] <= comb(k, j) * k ** (k - j)
    stirling.append(row)

mu = F(19, 50)
exp_minus_mu_upper = sum((-mu) ** j / factorial(j) for j in range(17))


def poisson_weighted_series_upper(power, first):
    ratio = mu * F(81, 80) ** power / 81
    assert ratio < F(1, 100)
    return exp_minus_mu_upper * (
        sum(F(j**power) * mu**j / factorial(j) for j in range(first, 81))
        + F(81**power) * mu**81 / factorial(81) * F(100, 99)
    )


scale = 2**48
bulk = I * exp_minus_mu_upper * sum(F(j**14) * mu**j / factorial(j) for j in range(1, 11)) / scale
second = I * exp_minus_mu_upper * sum(F(j**28) * mu**j / factorial(j) for j in range(1, 11)) / scale**2
eleven = I * exp_minus_mu_upper * mu**11 / factorial(11)
tail = I * poisson_weighted_series_upper(14, 12) / scale
assert bulk < F(1, 5)
assert second < F(1, 2000)
assert eleven < F(3, 100000)
assert tail < F(5, 1000000)
assert F(10**14, scale) < F(3, 8)
assert F(11**14, scale) < F(3, 2)

exp6_upper = sum(F(6**j, factorial(j)) for j in range(61)) + F(6**61, factorial(61)) / (1 - F(6, 62))
assert exp6_upper < 405
assert -16 * (F(3, 2) - F(1, 5)) + F(1, 2000) / F(3, 8) ** 2 * (405 - 1 - 6) < -19
assert sum(F(19**j, factorial(j)) for j in range(81)) > 2**27
excess = F(5, 1000000) + F(3, 100000) * F(1, 5) + F(3, 4) * F(3, 100000) ** 2 + F(1, 2**31)
assert excess < F(1, 2**16)

near_mean = F(14 * I, 2**38) * poisson_weighted_series_upper(13, 1)
assert near_mean < 557

x = F(3, 2**14)
prefix = (F(3, 2) + 4 * x + 2 * x**2) / (1 - x) + 4 * x / (1 - x) ** 2 + 82 * x / (1 - x)
encoding = 1 + 3444 * x / (1 - x)
assert max(prefix, encoding, F(3, 2)) < F(131, 80)
fts = 557 * x / (1 - x) + x / (2 * (1 - x) ** 2)
assert fts < F(9, 80)
assert F(131, 80) + F(9, 80) == F(7, 4)
assert x / 8 - F(1, 2**16) == F(1, 2**17)
error_per_x = F(1, 2**94) + F(1, 2**109) + F(1, 2**572)
assert error_per_x < F(1, 2**17)
assert F(7, 4) + F(1, 2**16) + error_per_x < 2

print("Exact cache, deficit, Poisson domination, and closing constants passed.")
print("Degree-14 Poisson excess upper bound:", float(excess))
print("Degree-13 near-target mean upper bound:", float(near_mean))
print("These arithmetic checks do not verify the adaptive couplings or the SUF theorem.")
