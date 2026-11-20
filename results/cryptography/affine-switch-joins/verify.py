"""Compare the coloring formula with a direct finite-group search over affine joins."""

from functools import lru_cache
from itertools import combinations, product


def proper_colorings(n, edges):
    def extend(colors):
        vertex = len(colors)
        if vertex == n:
            yield colors
            return
        for color in range(max(colors, default=-1) + 2):
            if all(colors[u] != color for u in range(vertex) if (u, vertex) in edges):
                yield from extend(colors + (color,))
    yield from extend(())


def coloring_cost(widths, colors):
    total = 0
    for level in range(1, max(widths) + 1):
        count = len({c for w, c in zip(widths, colors) if w >= level})
        total += count.bit_length()
    return total


def partitions(total, minimum=1):
    """All multisets of positive join widths with a given total cost."""
    if total == 0:
        yield ()
    for first in range(minimum, total + 1):
        for tail in partitions(total - first, first):
            yield (first,) + tail


@lru_cache(maxsize=None)
def cyclic_images(width, join_widths):
    """All possible nonzero-image sets for an injective single-word map."""
    moduli = [2**w for w in join_widths]
    order = 2**width
    zero = (0,) * len(moduli)
    subgroups = set()
    for generator in product(*(range(modulus) for modulus in moduli)):
        if any(order * x % m for x, m in zip(generator, moduli)):
            continue
        multiples = frozenset(
            tuple(k * x % m for x, m in zip(generator, moduli))
            for k in range(1, order)
        )
        if zero not in multiples:
            subgroups.add(multiples)
    return tuple(subgroups)


def admits_homomorphism(widths, edges, join_widths):
    options = [cyclic_images(w, join_widths) for w in widths]

    def extend(chosen):
        v = len(chosen)
        if v == len(widths):
            return True
        for subgroup in options[v]:
            # A sum of two cyclic images has a unique decomposition exactly
            # when the two images have no nonzero member in common.
            if all(subgroup.isdisjoint(chosen[u]) for u in range(v) if (u, v) in edges):
                if extend(chosen + (subgroup,)):
                    return True
        return False

    return extend(())


def minimum_direct_cost(widths, edges):
    # Singleton injectivity forces the budget to cover the largest input word.
    # Joining individual wires gives the finite upper bound below.
    for cost in range(max(widths), sum(widths) + 1):
        if any(admits_homomorphism(widths, edges, p) for p in partitions(cost)):
            return cost
    raise AssertionError("Individual joins always suffice")


if __name__ == "__main__":
    instances = 0
    for n in range(1, 5):
        pairs = tuple(combinations(range(n), 2))
        for graph in range(1 << len(pairs)):
            edges = {pair for i, pair in enumerate(pairs) if (graph >> i) & 1}
            colorings = list(proper_colorings(n, edges))
            for widths in product((1, 2), repeat=n):
                optimum = min(coloring_cost(widths, coloring) for coloring in colorings)
                assert optimum == minimum_direct_cost(widths, edges), (widths, edges)
                instances += 1
    print(f"{instances} graph/width instances agreed with the direct optimum.")
    edges = {(0, 1), (1, 2), (0, 2), (1, 3), (2, 3), (0, 4), (2, 4)}
    for width in range(2, 6):
        widths = (1, 1, 1, width, width)
        assert min(coloring_cost(widths, c) for c in proper_colorings(5, edges)) == width + 2
        assert minimum_direct_cost(widths, edges) == width + 2
    print("The five-vertex example attained W + 2 for W = 2, 3, 4, 5.")
