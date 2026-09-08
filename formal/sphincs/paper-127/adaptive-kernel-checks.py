from collections import defaultdict
from fractions import Fraction as F
from itertools import product


leaf_states = 0
for n in (2, 3, 4):
    for target in range(n):
        for mask in range((1 << n) - 1):
            known = [z for z in range(n) if mask >> z & 1]
            remaining = [z for z in range(n) if not mask >> z & 1]
            u = len(remaining)
            for answers in product(range(n), repeat=len(known)):
                table = dict(zip(known, answers))
                mass = F(1, u * n ** (u - 1))
                transitions = defaultdict(F)
                for secret in remaining:
                    free = [z for z in remaining if z != secret]
                    for completion in product(range(n), repeat=len(free)):
                        full = table | dict(zip(free, completion)) | {secret: target}
                        for candidate in range(n):
                            transitions[(candidate, candidate == secret, full[candidate], secret)] += mass
                for candidate in range(n):
                    for hit, answer, secret in product((False, True), range(n), remaining):
                        if candidate in table:
                            expected = F(int(not hit and answer == table[candidate]), u)
                        elif hit:
                            expected = F(int(secret == candidate and answer == target), u)
                        else:
                            expected = F(int(secret != candidate), u * n)
                        assert transitions[(candidate, hit, answer, secret)] == expected
                leaf_states += 1
print(f"Exact planted-table and deferred-secret kernels agree on {leaf_states} partial states.")

n = 3
beta = F(3, 2)
distributions = (
    (F(1, 2), F(1, 3), F(1, 6)),
    (F(1, 2), F(1, 2), F(0)),
    (F(1, 3), F(1, 3), F(1, 3)),
)
bridge_paths = 0
for probabilities in distributions:
    assert sum(probabilities) == 1
    rejected = tuple((beta / n - p) / (beta - 1) for p in probabilities)
    assert min(rejected) >= 0 and sum(rejected) == 1
    total = F(0)
    for length in range(6):
        for word in product(range(n), repeat=length):
            bridge_prefix = (1 / beta) * (1 - 1 / beta) ** length
            proposal_prefix = F(1)
            for index in word:
                bridge_prefix *= rejected[index]
                proposal_prefix *= F(1, n) * (1 - n * probabilities[index] / beta)
            for index, bit in product(range(n), (0, 1)):
                conditional_record = F(index + 1, 4) if bit else 1 - F(index + 1, 4)
                record_mass = probabilities[index] * conditional_record
                bridge_mass = record_mass * bridge_prefix
                proposal_mass = proposal_prefix * F(1, n) * n * probabilities[index] / beta * conditional_record
                assert bridge_mass == proposal_mass
                total += bridge_mass
                bridge_paths += 1
    assert total == 1 - (1 - 1 / beta) ** 6
print(f"Macro-first and proposal-first rejection bridges agree on {bridge_paths} finite paths.")

states = {((), 0): F(1)}
for length in range(1, 6):
    next_states = defaultdict(F)
    for (word, state), mass in states.items():
        probabilities = distributions[state]
        for index in range(n):
            prefix_mass = mass / n
            acceptance = n * probabilities[index] / beta
            next_states[(word + (index,), state)] += prefix_mass * (1 - acceptance)
            for bit in (0, 1):
                conditional_record = F(index + 1, 4) if bit else 1 - F(index + 1, 4)
                next_state = (state + index + bit + 1) % len(distributions)
                next_states[(word + (index,), next_state)] += prefix_mass * acceptance * conditional_record
    states = next_states
    words = defaultdict(F)
    for (word, _), mass in states.items():
        words[word] += mass
    assert len(words) == n**length
    assert set(words.values()) == {F(1, n**length)}
print("Uniform proposal prefixes survive the tested adaptive changes of index distribution.")
print("These finite checks do not certify the full-game coupling or a Lean security theorem.")
