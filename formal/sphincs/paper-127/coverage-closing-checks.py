from fractions import Fraction as F
from math import comb, factorial


N, I, L, S = 2**128, 2**26, 1024, 2**24
q_max = N // 2
arrival = F(1, L * I)
rho = F(1025, 1024) * F(L, N)
beta = F(1537, 1024)
v_max = F(1, I) + rho * (arrival * q_max + 2**80 + S + 14)
assert 0 < v_max < 1
assert I * v_max < beta
theta = F(1, 128)
proposal_slack = S // 128
minimum_proposals = beta * S + proposal_slack + 13
assert minimum_proposals == 25313293
proposal_mean = F(19, 50) * I
u = (beta - 1) * (theta + theta**2 / (2 * (1 - theta / 3)))
assert 0 < u < 1
log_geometric_mgf = -(beta - 1) * theta + u + u**2 / (2 * (1 - u))
assert log_geometric_mgf >= 0
proposal_prefix_exponent = -theta * proposal_slack + S * log_geometric_mgf
short_pool_exponent = -theta * (proposal_mean - minimum_proposals) + proposal_mean * theta**2 / 2
assert proposal_prefix_exponent < -500
assert short_pool_exponent < -500
exp_lower_argument = F(7, 10)
assert sum(exp_lower_argument**j / factorial(j) for j in range(4)) > 2
assert 701 * exp_lower_argument < 500
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
exp_minus_mu_upper = sum((-mu) ** j / factorial(j) for j in range(5))


def poisson_weighted_series_upper(power, first):
    ratio = mu * F(13, 12) ** power / 13
    assert ratio < F(1, 10)
    return exp_minus_mu_upper * (
        sum(F(j**power) * mu**j / factorial(j) for j in range(first, 12))
        + F(12**power) * mu**12 / factorial(12) * F(10, 9)
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

exp1_upper = sum(F(1, factorial(j)) for j in range(6)) + F(1, factorial(6)) / (1 - F(1, 7))
assert exp1_upper < F(68, 25)
assert F(68, 25) ** 6 < 405
assert -16 * (F(3, 2) - F(1, 5)) + F(1, 2000) / F(3, 8) ** 2 * (405 - 1 - 6) < -19
assert 27 * exp_lower_argument < 19
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

print("Exact cache, deficit, discrete proposal, and closing constants passed.")
print("Degree-14 Poisson excess upper bound:", float(excess))
print("Degree-13 near-target mean upper bound:", float(near_mean))
print("These arithmetic checks do not verify the adaptive couplings or the SUF theorem.")
