"""Check finite minimax trees against their explicit primal and dual witnesses."""

from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product


def witnesses(strings):
    """Return minimax cumulative risk, prediction tables and a worst-case prior."""
    if not strings[0]:
        return Fraction(0), {}, {(): Fraction(1)}

    branches = defaultdict(list)
    for string in strings:
        branches[string[0]].append(string[1:])

    children = {y: witnesses(suffixes) for y, suffixes in branches.items()}
    labels = sorted(children, key=lambda y: (-children[y][0], y))
    candidates = []
    total = Fraction(0)
    for r, y in enumerate(labels, 1):
        total += children[y][0]
        candidates.append((1 + (total - 1) / r, r))
    value, count = max(candidates)

    prediction = {y: max(0, 1 + children[y][0] - value) for y in labels}
    assert sum(prediction.values()) <= 1
    prediction[labels[0]] += 1 - sum(prediction.values())
    tables = {(): prediction}
    prior = {}
    for rank, y in enumerate(labels):
        _, child_tables, child_prior = children[y]
        for history, distribution in child_tables.items():
            tables[(y,) + history] = distribution
        if rank < count:
            for suffix, mass in child_prior.items():
                prior[(y,) + suffix] = mass / count
    return value, tables, prior


def minority_mass(weighted_prefixes):
    table = defaultdict(lambda: defaultdict(Fraction))
    for string, weight in weighted_prefixes:
        for t, label in enumerate(string):
            table[string[:t]][label] += weight / len(string)
    return sum(sum(row.values()) - max(row.values()) for row in table.values())


def check_family(strings):
    value, prediction, prior = witnesses(strings)
    assert sum(prior.values()) == 1
    assert all(sum(q.values()) == 1 for q in prediction.values())
    risks = [
        sum(1 - prediction[string[:t]][y] for t, y in enumerate(string))
        for string in strings
    ]
    assert max(risks) == value
    assert minority_mass(prior.items()) == value / len(strings[0])


def main():
    checked = 0
    for alphabet, depth in [(2, 3), (3, 2)]:
        strings = list(product(range(alphabet), repeat=depth))
        for size in range(1, len(strings) + 1):
            for family in combinations(strings, size):
                check_family(family)
                checked += 1

    # Endpoints of different lengths contribute different masses per position.
    mixed = [((0, 1), Fraction(1, 3)), ((0, 2, 1), Fraction(2, 3))]
    assert minority_mass(mixed) == Fraction(1, 6)
    print(f"Checked primal and dual minimax witnesses on {checked} prefix trees.")
    print("Verified unequal-endpoint normalization on a mixed test.")


if __name__ == "__main__":
    main()
