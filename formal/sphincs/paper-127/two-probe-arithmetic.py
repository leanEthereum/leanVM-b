from fractions import Fraction as F
from functools import lru_cache


def optimum_survival(N, q):
    @lru_cache(None)
    def solve(counts, remaining):
        if remaining == 0:
            return F(1)
        alternatives = []
        for i in range(len(counts)):
            for j in range(i + 1, len(counts)):
                next_counts = list(counts)
                next_counts[i] += 1
                next_counts[j] += 1
                miss = F(N - counts[i] - 1, N - counts[i]) * F(N - counts[j] - 1, N - counts[j])
                alternatives.append(miss * solve(tuple(sorted(next_counts)), remaining - 1))
        return min(alternatives)

    return solve((0,) * (2 * q), q)


for N in [7, 11, 17]:
    for q in range(1, min(5, N - 1) + 1):
        assert optimum_survival(N, q) == F(N - q, N) ** 2

print('Adaptive two-probe model: all 15 exact finite optimum checks passed.')
print('This script checks the abstract model; the full SUF theorem remains open.')
