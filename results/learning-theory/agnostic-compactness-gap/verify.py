"""Finite checks of the atom metric, comparator inequality and compression stability."""

from itertools import combinations, product


def subsets(items):
    items = tuple(items)
    for size in range(len(items) + 1):
        yield from map(frozenset, combinations(items, size))


def distance(left, right):
    if left == right:
        return 0
    left_kind, a = left
    right_kind, b = right
    if left_kind == right_kind:
        return 1 if left_kind == "prototype" else 2
    token, covered = (a, b) if left_kind == "observation" else (b, a)
    return 1 if token in covered else 2


def check_metric_and_comparators():
    tokens = range(3)
    prototypes = tuple(subsets(tokens))
    atoms = [("prototype", a) for a in prototypes] + [("observation", u) for u in tokens]
    for a, b, c in product(atoms, repeat=3):
        assert distance(a, b) == distance(b, a)
        assert distance(a, b) <= distance(a, c) + distance(c, b)
    comparisons = 0
    for family in subsets(prototypes):
        default = ("prototype", frozenset().union(*family))
        for candidate in family:
            comparator = ("prototype", candidate)
            for outcome in atoms:
                assert distance(default, outcome) - distance(comparator, outcome) <= (outcome == comparator)
                comparisons += 1
    return len(atoms) ** 3, comparisons


def check_activation():
    # All masses are integer quarters. Two distinct prototype atoms can activate
    # at the same time, and the remaining mass may lie on other atoms.
    labels = [(a, b) for a in range(5) for b in range(5 - a)]
    count = 0
    for history in product(labels, repeat=4):
        totals = [0, 0]
        inactive_mass = [0, 0]
        active = set()
        for rounds, label in enumerate(history, 1):
            for i, weight in enumerate(label):
                if i not in active:
                    inactive_mass[i] += weight
                totals[i] += weight
                if totals[i] >= 4:
                    active.add(i)
            assert len(active) <= rounds
        assert all(mass < 8 for mass in inactive_mass)
        count += 1
    return count


def finite_hull(sample, ordered_universe, depth):
    if not sample:
        return frozenset(), frozenset()
    last = max(sample, key=ordered_universe.index)
    segment = ordered_universe[:ordered_universe.index(last)]
    if depth == 0:
        return frozenset(segment + (last,)), frozenset({last})
    # Choose a different fixed order for each segment. The proof allows this.
    subhull, marked = finite_hull(sample - {last}, segment[::-1], depth - 1)
    return subhull | {last}, marked | {last}


def check_deletions():
    universe = tuple(range(8))
    count = 0
    for depth in range(4):
        for sample in subsets(universe):
            hull, marked = finite_hull(sample, universe, depth)
            assert sample <= hull and marked <= sample and len(marked) <= depth + 1
            for token in sample - marked:
                assert finite_hull(sample - {token}, universe, depth)[0] == hull
                count += 1
    return count


if __name__ == "__main__":
    triangles, comparisons = check_metric_and_comparators()
    print(f"Checked {triangles} metric triangles and {comparisons} comparator inequalities.")
    print(f"Checked activation accounting on {check_activation()} histories.")
    print(f"Checked {check_deletions()} stable hull deletions.")
