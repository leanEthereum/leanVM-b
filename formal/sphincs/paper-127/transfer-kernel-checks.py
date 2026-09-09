from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
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

    def row_probability(domain, candidate, answer, known=known):
        if candidate in known[domain]:
            return F(int(known[domain][candidate] == answer))
        return F(1, n)

    likelihood = sum(row_probability(0, start, middle) * row_probability(1, middle, endpoint) for start, middle in product(values, repeat=2))
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
                            slot + 1,
                            next_possible,
                            final_fixed,
                            next_rows,
                            next_history + (("disclose", disclosed, secret),),
                            next_mass * reveal_mass,
                            next_likelihood,
                            next_first,
                            next_reached,
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


def check_private_chain_erasure(size, depth):
    domain = tuple(range(size))
    functions = tuple(product(domain, repeat=size))
    real, ideal, weighted = Counter(), Counter(), Counter()
    private_flag_counterexample = False

    class BudgetEnd(Exception):
        pass

    def execute(prefix, endpoint, seed, reference_counter, cap, secret=None):
        trace, flags, signatures = [], [], []
        private_rows, external_rows = set(), set()

        def tick(item):
            if len(trace) == cap:
                raise BudgetEnd
            trace.append(item)

        def prefix_query(level, candidate, external):
            if len(trace) == cap:
                raise BudgetEnd
            answer = prefix[level][candidate]
            high = (seed + level + candidate) % 2
            row = level, candidate
            if external:
                flags.append(row in private_rows)
                tick((level, candidate, answer, high, row in external_rows))
                external_rows.add(row)
            else:
                tick(None)
                private_rows.add(row)
            return answer

        def private_prefix():
            if secret is None:
                for _ in range(depth):
                    tick(None)
                return endpoint
            current = secret
            for level in range(depth):
                current = prefix_query(level, current, False)
            return current

        def private_full_chain():
            current = private_prefix()
            tick(None)
            return (current + seed) % size

        root, terminal = None, "completed"
        try:
            root = private_full_chain()
            first_level = depth - 2 if depth >= 2 and seed == 0 else depth - 1
            candidate = (root + seed) % size
            answer = prefix_query(first_level, candidate, True)
            message = private_full_chain()
            counter = None
            for c in range(2):
                tick(None)
                encoded = 0 if c == reference_counter else 1 + (message + seed + c) % (size - 1)
                if encoded == 0:
                    counter = c
                    break
            signature = None
            if counter is not None:
                value = private_prefix()
                authentication = private_full_chain()
                signature = counter, value, authentication
            # The later layer runs even if the earlier encoding exhausted.
            later_layer = private_full_chain()
            signatures.append((signature, later_layer))
            if seed == 0:
                prefix_query(depth - 1, answer, True)
            elif seed == 1 and depth >= 2:
                prefix_query(depth - 2, (candidate + answer) % size, True)
            else:
                prefix_query(first_level, candidate, True)
        except BudgetEnd:
            terminal = "budget"
        return (endpoint, seed, reference_counter, cap, root, tuple(trace), tuple(signatures), terminal), tuple(flags)

    for prefix in product(functions, repeat=depth):
        endpoints = []
        for secret in domain:
            current = secret
            for function in prefix:
                current = function[current]
            endpoints.append(current)
        multiplicity = Counter(endpoints)
        for seed, reference, cap in product(range(3), (-1, 0, 1), (2 * depth + 5, 4 * depth + 11)):
            projected = {}
            for endpoint in domain:
                record, _ = execute(prefix, endpoint, seed, reference, cap)
                projected[endpoint] = record
                ideal[record] += 1
                weighted[record] += multiplicity[endpoint]
            flags_by_endpoint = {}
            for secret in domain:
                endpoint = endpoints[secret]
                record, flags = execute(prefix, endpoint, seed, reference, cap, secret)
                assert record == projected[endpoint]
                real[record] += 1
                if endpoint in flags_by_endpoint and flags_by_endpoint[endpoint] != flags:
                    private_flag_counterexample = True
                flags_by_endpoint[endpoint] = flags
    assert real == weighted
    assert sum(real.values()) == sum(ideal.values())
    assert private_flag_counterexample

    @lru_cache(None)
    def partial_density(endpoint, queried):
        mass = [F(1)] * size
        for rows in queried:
            known = dict(rows)
            next_mass = [F(0)] * size
            for candidate in domain:
                if candidate in known:
                    next_mass[known[candidate]] += mass[candidate]
                else:
                    for answer in domain:
                        next_mass[answer] += mass[candidate] / size
            mass = next_mass
        return mass[endpoint]

    real_cost, ideal_cost = 0, 0
    for record, count in ideal.items():
        endpoint, _, _, cap, _, trace, _, _ = record
        assert len(trace) <= cap
        known = [{} for _ in range(depth)]
        for row in trace:
            if row is not None:
                level, candidate, answer, _, _ = row
                known[level][candidate] = answer
        queried = tuple(tuple(sorted(rows.items())) for rows in known)
        likelihood = partial_density(endpoint, queried)
        allocated = sum(map(len, known))
        assert likelihood >= 1 - F(allocated, size)
        assert real[record] == count * likelihood
        ideal_cost += count * allocated
        real_cost += real[record] * allocated
    if size > 2:
        # At most two external prefix rows are queried; all private costs remain.
        assert ideal_cost <= real_cost / (1 - F(2, size))
    print(f"Private chain erasure, failure costs and stopped densities agree for N={size}, depth={depth}, on {len(ideal)} transcripts.")
    print("Retaining the private cache-hit flag fails the erasure test, as expected.")


for test_size, test_depth in ((2, 1), (2, 2), (2, 3), (3, 2)):
    check_private_chain_erasure(test_size, test_depth)

print("These finite identities do not certify the full paper reduction or a Lean security theorem.")
