from collections import Counter
from fractions import Fraction as F
from itertools import product


n, budget = 3, 2
values = tuple(range(n))
tables = tuple(product(values, repeat=n))


identity = tuple(range(n))
assert sum(identity[identity[secret]] == 0 for secret in values) == 1
assert n * int(identity[identity[0]] == 0) != 1
for first, second, endpoint in product(tables, tables, values):
    full_densities = tuple(n * int(second[first[secret]] == endpoint) for secret in values)
    projected_density = sum(second[first[secret]] == endpoint for secret in values)
    assert F(sum(full_densities), n) == projected_density
print("The preimage density agrees only after marginalizing the hidden starting secret.")


def transcript(first, second, other, endpoint, other_endpoint, seed):
    auxiliary = (endpoint * other_endpoint + seed) % n
    private_cost = int(other_endpoint == 0)
    spent = private_cost
    rows = []
    domain = (endpoint + auxiliary) % 3
    candidate = other_endpoint
    if auxiliary:
        for _ in range(3):
            if spent == budget:
                break
            answer = (first, second, other)[domain][candidate]
            rows.append((domain, candidate, answer))
            spent += 1
            if answer == endpoint:
                break
            if answer != other_endpoint:
                domain, candidate = (domain + 1) % 3, answer
    assert spent <= budget
    return endpoint, other_endpoint, auxiliary, private_cost, tuple(rows)


real, ideal, weighted = Counter(), Counter(), Counter()
for first, second, other, other_secret, seed in product(tables, tables, tables, values, values):
    other_endpoint = other[other_secret]
    endpoints = tuple(second[first[s]] for s in values)
    multiplicity = Counter(endpoints)
    for endpoint in values:
        record = transcript(first, second, other, endpoint, other_endpoint, seed)
        ideal[record] += 1
        weighted[record] += multiplicity[endpoint]
    for secret in values:
        record = transcript(first, second, other, endpoints[secret], other_endpoint, seed)
        real[record] += 1
assert real == weighted
assert sum(real.values()) == sum(ideal.values())
real_cost, ideal_cost = 0, 0
for record, ideal_count in ideal.items():
    endpoint, _, _, _, queried = record
    known = [{}, {}]
    for domain, candidate, answer in queried:
        if domain < 2:
            known[domain][candidate] = answer

    def row_probability(domain, candidate, answer):
        if candidate in known[domain]:
            return F(int(known[domain][candidate] == answer))
        return F(1, n)

    likelihood = sum(
        row_probability(0, start, middle) * row_probability(1, middle, endpoint)
        for start, middle in product(values, repeat=2)
    )
    allocated = sum(map(len, known))
    assert likelihood >= 1 - F(allocated, n) >= 1 - F(budget, n)
    assert real[record] == ideal_count * likelihood
    real_cost += real[record] * allocated
    ideal_cost += ideal_count * allocated
assert ideal_cost <= real_cost / (1 - F(budget, n))
print(f"Endpoint-dependent auxiliary simulation and stopped density agree on {len(ideal)} transcripts.")
print(f"The graph comparison enumerated {sum(ideal.values())} full states in each law.")

public = (0, 1)


def replace_at(items, coordinate, value):
    return tuple(value if index == coordinate else item for index, item in enumerate(items))


def query_branches(possible, fixed, rows, coordinate, candidate, force):
    table = dict(rows[coordinate])
    choices = possible[coordinate]
    eligible = fixed[coordinate] is None and candidate in choices
    hazard = F(1, len(choices)) if eligible else F(0)
    branches = []
    if eligible:
        if force != "miss":
            table_hit = dict(table)
            table_hit[candidate] = public[coordinate]
            branches.append(
                (
                    F(1) if force == "hit" else hazard,
                    possible,
                    replace_at(fixed, coordinate, candidate),
                    replace_at(rows, coordinate, tuple(sorted(table_hit.items()))),
                    public[coordinate],
                    True,
                )
            )
        if force != "hit":
            residual = tuple(value for value in choices if value != candidate)
            for answer in values:
                table_miss = dict(table)
                table_miss[candidate] = answer
                branches.append(
                    (
                        (F(1) if force == "miss" else 1 - hazard) / n,
                        replace_at(possible, coordinate, residual),
                        fixed,
                        replace_at(rows, coordinate, tuple(sorted(table_miss.items()))),
                        answer,
                        False,
                    )
                )
    else:
        if candidate in table:
            answers = ((F(1), table[candidate]),)
        elif candidate == fixed[coordinate]:
            answers = ((F(1), public[coordinate]),)
        else:
            answers = tuple((F(1, n), answer) for answer in values)
        for mass, answer in answers:
            table_after = dict(table)
            table_after[candidate] = answer
            branches.append((mass, possible, fixed, replace_at(rows, coordinate, tuple(sorted(table_after.items()))), answer, False))
    assert sum(branch[0] for branch in branches) == 1
    return hazard, branches


def disclosure_branches(possible, fixed, coordinate):
    if fixed[coordinate] is not None:
        return ((F(1), fixed, fixed[coordinate]),)
    choices = possible[coordinate]
    return tuple((F(1, len(choices)), replace_at(fixed, coordinate, secret), secret) for secret in choices)


def run(forced_slot=None):
    distribution, density, first_events = Counter(), Counter(), {j: Counter() for j in range(1, budget + 1)}

    def finish(history, mass, likelihood, first_hit, reached):
        distribution[history] += mass
        if forced_slot is not None and reached and likelihood:
            density[history] += mass * likelihood
        if first_hit is not None:
            first_events[first_hit][history] += mass

    def step(slot, possible, fixed, rows, history, mass, likelihood, first_hit, reached):
        if slot > budget:
            finish(history, mass, likelihood, first_hit, reached)
            return
        for coin in values:
            previous_answer = next((item[4] for item in reversed(history) if item[0] == "hash"), 0)
            coordinate = (coin + slot - 1) % 2
            candidate = (coin + previous_answer + slot - 1) % n
            force = None if forced_slot is None or slot > forced_slot else ("hit" if slot == forced_slot else "miss")
            hazard, branches = query_branches(possible, fixed, rows, coordinate, candidate, force)
            next_likelihood = likelihood
            if forced_slot is not None:
                if slot < forced_slot:
                    next_likelihood *= 1 - hazard
                elif slot == forced_slot:
                    next_likelihood *= hazard
            for branch_mass, next_possible, next_fixed, next_rows, answer, hit in branches:
                next_history = history + (("coin", coin), ("hash", slot, coordinate, candidate, answer, hit))
                next_mass = mass * branch_mass / n
                next_first = slot if first_hit is None and hit else first_hit
                next_reached = reached or slot == forced_slot
                if slot == 1 and coin:
                    disclosed = (answer + coin) % 2
                    for reveal_mass, final_fixed, secret in disclosure_branches(next_possible, next_fixed, disclosed):
                        step(
                            slot + 1, next_possible, final_fixed, next_rows,
                            next_history + (("disclose", disclosed, secret),),
                            next_mass * reveal_mass, next_likelihood, next_first, next_reached,
                        )
                elif slot == 1 and answer == 2:
                    finish(next_history, next_mass, next_likelihood, next_first, next_reached)
                else:
                    step(slot + 1, next_possible, next_fixed, next_rows, next_history, next_mass, next_likelihood, next_first, next_reached)

    step(1, (values, values), (None, None), ((), ()), (), F(1), F(1), None, False)
    assert sum(distribution.values()) == 1
    return distribution, density, first_events


original, _, first_events = run()
for slot in range(1, budget + 1):
    forced, density, _ = run(slot)
    assert density == first_events[slot]
    assert all(density[record] <= forced[record] / (n - budget) for record in density)
print(f"Forced-first-guess densities agree pointwise on {len(original)} original terminal transcripts.")
print("The checks include adaptive queries, ambiguous output matches, disclosures, repeats, and early termination.")
print("These finite identities do not certify the full paper reduction or a Lean security theorem.")
