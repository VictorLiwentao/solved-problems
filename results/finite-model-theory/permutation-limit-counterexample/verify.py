"""Exact finite checks for the first-order sentence and the class construction."""

from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, factorial


def common_least(perm):
    """Interpret the two-quantifier sentence using the position and value orders."""
    return any(all(not (y < x or perm[y] < perm[x]) for y in range(len(perm)))
               for x in range(len(perm)))


def prepend_minimum(perm):
    return (1,) + tuple(v + 1 for v in perm)


def decreasing_runs(perm):
    return int(bool(perm)) + sum(a < b for a, b in zip(perm, perm[1:]))


def from_colorings(n, k):
    outputs = set()
    for coloring in product(range(k), repeat=n):
        blocks = [[] for _ in range(k)]
        for value, color in enumerate(coloring, 1):
            blocks[color].append(value)
        outputs.add(tuple(v for block in blocks for v in reversed(block)))
    return outputs


def delete_entry(perm, index):
    value = perm[index]
    return tuple(v - (v > value) for v in perm if v != value)


def check_comparison_classes(universe):
    checked = 0
    for n, layer in enumerate(universe):
        for k in (1, 2, 3):
            outputs = from_colorings(n, k)
            assert outputs == {p for p in layer if decreasing_runs(p) <= k}
            assert len(outputs) <= k**n <= len(outputs) * comb(n+k-1, k-1)
            checked += 1
    return checked


def check_extension(universe, base, k):
    layers = []
    for n, layer in enumerate(universe):
        comparison = {p for p in layer if decreasing_runs(p) <= k}
        prepended = {prepend_minimum(p) for p in base[n-1]} if n else set()
        extended = base[n] | prepended | comparison
        if n:
            assert all(delete_entry(p, i) in layers[-1] for p in extended for i in range(n))
        if n >= 2:
            previous_small = {p for p in universe[n-1] if decreasing_runs(p) <= k-1}
            witnesses = {p for p in extended if common_least(p)}
            assert witnesses == {prepend_minimum(p) for p in base[n-1] | previous_small}
            assert len(extended - witnesses) <= len(base[n]) + len(comparison)
            assert len(witnesses) <= len(base[n-1]) + len(previous_small)
        layers.append(extended)


def one_cutoff(n):
    """Take the base to be all permutations of sizes at most n, and k=2."""
    comparison = from_colorings(n + 1, 2)
    shared = sum(common_least(p) for p in comparison)
    first = Fraction(factorial(n), factorial(n) + len(comparison) - shared)
    next_layer = from_colorings(n + 2, 2)
    second = Fraction(sum(common_least(p) for p in next_layer), len(next_layer))
    return first, second


def main():
    universe = [list(permutations(range(1, n + 1))) for n in range(8)]
    checked = check_comparison_classes(universe)
    truncated = [set(layer) if n <= 4 else set() for n, layer in enumerate(universe)]
    avoid_231 = [{p for p in layer if not any(c < a < b for a, b, c in combinations(p, 3))}
                 for layer in universe]
    for base in (truncated, avoid_231):
        for k in (2, 3):
            check_extension(universe, base, k)
    first, second = one_cutoff(10)
    assert (first, second) == (Fraction(907200, 907709), Fraction(1, 4084))
    low, middle, high = 8 * (5000 + 513), 44500, 9 * 5000
    assert low < middle < high and max(low, middle - 1) < middle
    print(f"{checked} comparison layers agree exactly with direct enumeration.")
    print("Heredity and the witness counts agree for four extension constructions through size 7.")
    print(f"Single-cutoff illustration at sizes 11 and 12: {first}, {second}.")


if __name__ == "__main__":
    main()
