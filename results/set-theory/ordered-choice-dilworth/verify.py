"""Exhaust finite order and block-permutation identities from the proof."""

from itertools import combinations, permutations, product


def posets(n):
    pairs = list(combinations(range(n), 2))
    for states in product(range(3), repeat=len(pairs)):
        successors = [0] * n
        for (a, b), state in zip(pairs, states):
            if state == 1:
                successors[a] |= 1 << b
            if state == 2:
                successors[b] |= 1 << a
        if all(not (successors[a] >> b & 1) or not (successors[b] & ~successors[a])
               for a in range(n) for b in range(n)):
            yield successors


def check_order(up):
    n = len(up)
    points = set(range(n))
    neighbors = [{j for j in points if j != i and not ((up[i] >> j | up[j] >> i) & 1)}
                 for i in range(n)]
    antichains = [set(t) for size in range(n + 1) for t in combinations(points, size)
                  if all(b in neighbors[a] for a, b in combinations(t, 2))]
    width = max(map(len, antichains))
    components = set()
    for base in points:
        seen, layer = {base}, {base}
        while layer:
            following = set().union(*(neighbors[v] for v in layer)) - seen
            first = {w: min(neighbors[w] & layer) for w in following}
            for v in set(first.values()):
                fibre = {w for w in following if first[w] == v}
                assert all(len(a) < width for a in antichains if a <= fibre)
            seen |= following
            layer = following
        components.add(frozenset(seen))
    for a, b in combinations(components, 2):
        directions = {(up[i] >> j) & 1 for i in a for j in b}
        assert len(directions) == 1


def check_wreath(n):
    identity = tuple(range(n))
    for perm in permutations(identity):
        first, second = list(identity), list(identity)
        left = set(identity)
        while left:
            cycle = [min(left)]
            while perm[cycle[-1]] != cycle[0]:
                cycle.append(perm[cycle[-1]])
            left.difference_update(cycle)
            for j, b in enumerate(cycle):
                first[b] = cycle[-j % len(cycle)]
                second[b] = cycle[(1 - j) % len(cycle)]
        assert all(first[first[j]] == second[second[j]] == j for j in identity)
        for flips in product(range(2), repeat=n):
            for block, bit in product(identity, range(2)):
                image = second[first[block]]
                assert (image, bit ^ flips[image]) == (perm[block], bit ^ flips[perm[block]])


if __name__ == "__main__":
    total = 0
    for order in posets(5):
        check_order(order)
        total += 1
    assert total == 4231
    check_wreath(5)
    print(f"Verified every root and component of {total:,} labelled five-point posets.")
    print("Verified the three-involution decomposition for 3,840 permutations of five pairs.")
