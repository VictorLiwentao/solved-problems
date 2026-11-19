"""Finite checks for transposition classes, orbit sizes, and template counts."""

from itertools import combinations, permutations, product
from math import comb, factorial, prod


def check_binary_relations(size, directed):
    if directed:
        pairs = [(a, b) for a in range(size) for b in range(size) if a != b]
    else:
        pairs = list(combinations(range(size), 2))
    positions = {pair: i for i, pair in enumerate(pairs)}
    actions = []
    transpositions = []
    for permutation in permutations(range(size)):
        images = [(permutation[a], permutation[b]) for a, b in pairs]
        if not directed:
            images = [tuple(sorted(pair)) for pair in images]
        actions.append([positions[pair] for pair in images])
        moved = [i for i in range(size) if permutation[i] != i]
        if len(moved) == 2:
            transpositions.append((len(actions) - 1, moved))

    orbit_sizes = {}
    for mask in range(1 << len(pairs)):
        if mask in orbit_sizes:
            continue
        edge_indices = [i for i in range(len(pairs)) if mask >> i & 1]
        images = [sum(1 << action[i] for i in edge_indices) for action in actions]
        copies = set(images)
        for copy in copies:
            orbit_sizes[copy] = len(copies)
        twins = [{v} for v in range(size)]
        for index, (a, b) in transpositions:
            if images[index] == mask:
                twins[a].add(b)
                twins[b].add(a)
        assert all(twins[a] == twins[b] for a in range(size) for b in twins[a])
        largest = max(map(len, twins))
        automorphisms = images.count(mask)
        assert automorphisms * len(copies) == factorial(size)
        assert automorphisms**2 <= size**size * largest ** (2 * size)
        if largest > size // 2:
            assert len(copies) % comb(size, largest) == 0
    return len(orbit_sizes)


def restricted_color_counts(n, colors, threshold):
    # Grow a labelled word one letter at a time, tracking truncated occupancies.
    counts = {(0,) * colors: 1}
    for _ in range(n):
        new = {}
        for state, multiplicity in counts.items():
            for i in range(colors):
                successor = list(state)
                successor[i] = min(successor[i] + 1, threshold)
                key = tuple(successor)
                new[key] = new.get(key, 0) + multiplicity
        counts = new
    return counts.get((threshold,) * colors, 0)


def inclusion_exclusion(n, colors, threshold):
    total = 0
    for forbidden in range(colors + 1):
        for sizes in product(range(threshold), repeat=forbidden):
            used = sum(sizes)
            if used <= n:
                ways = factorial(n) // (factorial(n - used) * prod(map(factorial, sizes)))
                total += ((-1) ** forbidden * comb(colors, forbidden) * ways
                          * (colors - forbidden) ** (n - used))
    return total


if __name__ == "__main__":
    undirected = sum(check_binary_relations(n, False) for n in range(1, 7))
    directed = sum(check_binary_relations(n, True) for n in range(1, 5))
    for n, colors, threshold in product(range(17), range(1, 5), range(1, 4)):
        assert restricted_color_counts(n, colors, threshold) == inclusion_exclusion(n, colors, threshold)
    print(f"Verified orbit and twin counts across {undirected} graphs and {directed} digraphs.")
    print("Verified 204 labelled template counts by independent occupancy recurrences.")
