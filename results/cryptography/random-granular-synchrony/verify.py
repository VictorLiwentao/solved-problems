"""Enumerate small network laws exactly and check the planted-witness edge estimates."""

from fractions import Fraction
from itertools import combinations
from math import prod


def pairs(n, f):
    full = set(range(n))
    h = n - 2*f
    for faults in combinations(range(n), f):
        honest = full.difference(faults)
        # An unordered pair has exactly one shore containing the first honest vertex.
        anchor = min(honest)
        for size in range(h, f+1):
            for others in combinations(sorted(honest - {anchor}), size-1):
                a = {anchor, *others}
                yield a, honest - a


def edge_mask(a, b, edge_ids):
    return sum(1 << edge_ids[min(u,v), max(u,v)] for u in a for v in b)


def verify_law(n, f):
    edges = list(combinations(range(n), 2))
    ids = {edge: i for i, edge in enumerate(edges)}
    masks = [edge_mask(a, b, ids) for a, b in pairs(n, f)]
    # Each edge probability is 1/3 or 2/3. All masses have denominator 3**m.
    probs = [1 + i % 2 for i in range(len(edges))]
    weight_two_absent = sum(1 << i for i, p in enumerate(probs) if p == 1)
    mass = expectation = unique = failure = 0
    for graph in range(1 << len(edges)):
        weight = 1 << (graph ^ weight_two_absent).bit_count()
        count = sum(graph & mask == 0 for mask in masks)
        mass += weight
        expectation += weight * count
        failure += weight * (count >= 1)
        unique += weight * (count == 1)
    assert mass == 3 ** len(edges)
    summed = sum(prod(3 - p if mask >> i & 1 else 3 for i, p in enumerate(probs))
                 for mask in masks)
    assert expectation == summed and unique <= failure <= expectation
    print(f"n={n}, f={f}: exact failure probability {Fraction(failure, mass)}, "
          f"expected witnesses {Fraction(expectation, mass)}.")
    return 1 << len(edges)


def verify_edge_bound(n, f):
    h = n - 2*f
    edge_ids = {edge: i for i, edge in enumerate(combinations(range(n), 2))}
    partitions = [(a, b, edge_mask(a, b, edge_ids)) for a, b in pairs(n, f)]
    checks = 0
    for size in range(h, (n-f)//2 + 1):
        x = set(range(size))
        y = set(range(size, n-f))
        left_over = set(range(n-f, n))
        planted = edge_mask(x, y, edge_ids)
        for a, b, mask in partitions:
            if mask == planted:
                continue
            additional = (mask & ~planted).bit_count()
            classes = [x, y, left_over]
            first = max(range(3), key=lambda i: len(a & classes[i]))
            second = max(range(3), key=lambda i: len(b & classes[i]))
            if {first, second} == {0, 1}:
                shores = (a, b) if first == 0 else (b, a)
                r = len(shores[0] - x) + len(shores[1] - y)
                changed = len((x - shores[0]) | (y - shores[1])
                              | (left_over & (a | b)))
                assert r >= 1 and changed <= 2*r and 3*additional >= r*h
            else:
                assert 9*additional >= h*h
            checks += 1
    return checks


if __name__ == "__main__":
    graphs = sum(verify_law(n, f) for n, f in ((3, 1), (5, 2), (6, 2)))
    rivals = sum(verify_edge_bound(n, f) for n in range(3, 11)
                 for f in range((n+2)//3, (n-1)//2 + 1))
    print(f"{graphs:,} weighted graphs and {rivals:,} planted/rival comparisons passed.")
