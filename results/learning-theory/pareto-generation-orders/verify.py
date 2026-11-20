"""Compare the recursive deadline test with brute-force feasibility on small classes."""
from itertools import combinations, permutations, product


def subsets(items):
    return [frozenset(part) for size in range(len(items) + 1)
            for part in combinations(items, size)]


def constraints(shared, language_count):
    # Each target also contains an infinite private tail. A sample that touches
    # a private tail determines the target, so only shared samples can obstruct.
    bad = []
    for sample in subsets(range(len(shared)))[1:]:
        compatible = set(range(language_count))
        for point in sample:
            compatible &= shared[point]
        for active in subsets(sorted(compatible)):
            if len(active) <= 1:
                continue
            if all(point in sample or not active <= support
                   for point, support in enumerate(shared)):
                bad.append((len(sample), active))
    return bad


def check(shared, language_count):
    bad = constraints(shared, language_count)
    limit = len(shared) + 1
    profiles = list(product(range(1, limit + 1), repeat=language_count))
    feasible = {d for d in profiles if all(any(d[i] > n for i in edge)
                                           for n, edge in bad)}
    minimal = {d for d in feasible if all(
        d[i] == 1 or d[:i] + (d[i] - 1,) + d[i + 1:] not in feasible
        for i in range(language_count))}
    ordered = set()
    for order in permutations(range(language_count)):
        d = {}
        for i in order:
            forbidden = [n for n, edge in bad if i in edge and all(
                j in d and d[j] <= n for j in edge if j != i)]
            d[i] = 1 + max(forbidden, default=0)
        ordered.add(tuple(d[i] for i in range(language_count)))
    assert ordered == minimal


if __name__ == "__main__":
    supports = [s for s in subsets(range(3)) if len(s) > 1]
    checked = 0
    for shared in product(supports, repeat=3):
        check(shared, 3)
        checked += 1
    print(f"Greedy orders and brute-force Pareto minima agree on {checked} classes.")
