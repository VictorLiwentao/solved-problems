"""Compare two generating-function decompositions with direct labelled enumeration."""

from fractions import Fraction
from itertools import combinations, permutations
from math import factorial


def components(n, edges, mask):
    groups = [{i} for i in range(n)]
    for index, (a, b) in enumerate(edges):
        if mask & (1 << index):
            left = next(part for part in groups if a in part)
            right = next(part for part in groups if b in part)
            if left != right:
                left.update(right)
                groups.remove(right)
    return groups


def cycle_masks(n, edges):
    edge_bits = {pair: 1 << i for i, pair in enumerate(edges)}
    for size in range(3, n + 1):
        for vertices in combinations(range(n), size):
            for tail in permutations(vertices[1:]):
                if tail[0] > tail[-1]:
                    continue
                cycle = (vertices[0],) + tail
                pairs = zip(cycle, cycle[1:] + cycle[:1])
                yield size, sum(edge_bits[tuple(sorted(pair))] for pair in pairs)


def direct_counts(n):
    edges = list(combinations(range(n), 2))
    cycles = list(cycle_masks(n, edges))
    counts = [[0, 0], [0, 0]]
    for graph in range(1 << len(edges)):
        cyclic_edges = 0
        large_cycle = False
        for size, mask in cycles:
            if graph & mask == mask:
                cyclic_edges |= mask
                large_cycle |= size > 3
        seed_sizes = [len(group) for group in components(n, edges, cyclic_edges)]
        connected = len(components(n, edges, graph)) == 1
        for accepted, pair in zip(
            (not large_cycle, all(size in (1, 4) for size in seed_sizes)), counts
        ):
            if accepted:
                pair[0] += 1
                pair[1] += connected
    return counts


def exp_coefficients(poly, degree):
    """Coefficients of exp(poly) from its differential equation, poly(0)=0."""
    result = [Fraction(1)]
    for n in range(1, degree + 1):
        derivative = sum(k * a * result[n - k] for k, a in poly.items() if k <= n)
        result.append(Fraction(derivative, n))
    return result


def predicted_counts(max_size, bridge_seeds):
    connected = {}
    seed = Fraction(10, factorial(4))  # three cycles, six diamonds and one clique
    for n in range(1, max_size + 1):
        if bridge_seeds:
            # v = z exp(v + 4 c v^4), rooted T = v + 4 c v^4.
            powers = exp_coefficients({1: n, 4: 4 * n * seed}, n - 1)
            numerator = powers[n - 1]
            if n >= 4:
                numerator += 16 * seed * powers[n - 4]
        else:
            # T = z exp(T + T^2/2) when each block is an edge or triangle.
            numerator = exp_coefficients({1: n, 2: Fraction(n, 2)}, n - 1)[-1]
        connected[n] = numerator / (n * n)  # Lagrange inversion and unrooting
    all_graphs = exp_coefficients(connected, max_size)
    return [(all_graphs[n] * factorial(n), connected[n] * factorial(n))
            for n in range(1, max_size + 1)]


if __name__ == "__main__":
    max_size = 6
    predictions = [predicted_counts(max_size, b) for b in (False, True)]
    for n in range(1, max_size + 1):
        for actual, predicted in zip(direct_counts(n), predictions):
            assert tuple(actual) == predicted[n - 1]
    print("Both class decompositions give the direct connected and total counts through six vertices.")
