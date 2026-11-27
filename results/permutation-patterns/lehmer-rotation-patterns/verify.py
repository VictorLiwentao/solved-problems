"""Exhaustive negative certificates for positional masks of lengths two and three."""
from collections import Counter
from itertools import combinations, permutations, product


def orbit_list(n):
    radices = tuple(range(n, 0, -1))
    remaining = set(product(*(range(m) for m in radices)))
    while remaining:
        code = next(iter(remaining))
        orbit = []
        while code in remaining:
            remaining.remove(code)
            available = list(range(n))
            orbit.append(tuple(available.pop(digit) for digit in code))
            code = tuple((digit + 1) % m for digit, m in zip(code, radices))
        yield orbit


def survivors(k):
    masks = range(1 << (k + 1))
    shapes = list(permutations(range(1, k + 1)))
    live = set(product(shapes, masks))
    counts_by_n = []
    for n in (4, 5, 6):
        reference = None
        for orbit in orbit_list(n):
            exact = Counter()
            for indices in combinations(range(n), k):
                padded = (-1,) + indices + (n,)
                mask = sum(1 << i for i, (a, b) in enumerate(zip(padded, padded[1:]))
                           if b == a + 1)
                for permutation in orbit:
                    word = [permutation[i] for i in indices]
                    ordered = sorted(word)
                    shape = tuple(1 + ordered.index(v) for v in word)
                    exact[shape, mask] += 1
            sums = {(p, f): sum(exact[p, m] for m in masks if m & f == f)
                    for p, f in live}
            if reference is None:
                reference = sums
            else:
                live = {pair for pair in live if sums[pair] == reference[pair]}
        counts_by_n.append(len(live))
    return live, counts_by_n


pairs, _ = survivors(2)
assert pairs == set(product(permutations((1, 2)), (0, 1, 2, 3, 6, 7)))
triples, sizes = survivors(3)
expected = set(product(permutations((1, 2, 3)), (2, 3, 14, 15)))
expected.update(product(((1, 2, 3), (3, 2, 1)), (6, 7)))
assert triples == expected and sizes == [44, 40, 28]
print("Exact orbit comparisons leave 12 pairs and 28 triples. All match the theorem.")
