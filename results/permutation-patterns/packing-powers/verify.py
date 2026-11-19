"""Exact checks for the power-sequence construction and its base-two rigidity theorem.

Run with Python 3.9 or later: python3 verify.py
"""

from functools import lru_cache
from itertools import combinations, permutations
from math import comb


def pattern(a, b, c):
    length = a + b + c + 4
    prefix = (1, a + 2)
    suffix = (a + c + 3, length)
    middle = tuple(i for i in range(1, length + 1) if i not in prefix + suffix)
    return prefix + middle + suffix


def window_chains(ranks, overlap, copies):
    by_rank = sorted(range(len(ranks)), key=ranks.__getitem__)
    stride = len(ranks) - overlap
    return [tuple(t * stride + i for i in by_rank) for t in range(copies)]


def count_extensions(chains):
    """Build an extension by taking the next position in every chain that contains it."""
    length = len(chains[0])
    memberships = {}
    for row, chain in enumerate(chains):
        for rank, vertex in enumerate(chain):
            memberships.setdefault(vertex, []).append((row, rank))

    @lru_cache(None)
    def count(cursors):
        heads = {chain[i] for chain, i in zip(chains, cursors) if i < length}
        if not heads:
            return 1
        total = 0
        for vertex in heads:
            entries = memberships[vertex]
            if all(cursors[row] == rank for row, rank in entries):
                advanced = list(cursors)
                for row, _ in entries:
                    advanced[row] += 1
                total += count(tuple(advanced))
        return total

    total = count((0,) * len(chains))
    count.cache_clear()
    return total


def incomparable_pairs(chains):
    """Compute pairwise incomparability directly from transitive reachability."""
    successors = {vertex: set() for chain in chains for vertex in chain}
    for chain in chains:
        for lower, upper in zip(chain, chain[1:]):
            successors[lower].add(upper)

    @lru_cache(None)
    def reachable(start):
        targets = set(successors[start])
        for vertex in successors[start]:
            targets.update(reachable(vertex))
        return targets

    return [(x, y) for x, y in combinations(successors, 2)
            if y not in reachable(x) and x not in reachable(y)]


def check_construction():
    cases = 0
    for a in range(5):
        for b in range(7):
            for c in range(4):
                ranks = pattern(a, b, c)
                for copies in range(1, 7):
                    total = count_extensions(window_chains(ranks, 2, copies))
                    expected = comb(a + b, a) ** (copies - 1)
                    if total != expected:
                        raise AssertionError((a, b, c, copies, total, expected))
                    cases += 1
    print(f"Construction: {cases} exact counts agree with the binomial-power formula.")


def check_rigidity():
    cases = equality = 0
    for length in range(2, 7):
        for ranks in permutations(range(1, length + 1)):
            for overlap in range(1, length):
                if count_extensions(window_chains(ranks, overlap, 2)) != 2:
                    continue
                for copies in range(2, 6):
                    chains = window_chains(ranks, overlap, copies)
                    total = count_extensions(chains)
                    pairs = incomparable_pairs(chains)
                    endpoints = {p for pair in pairs for p in pair}
                    matching = len(pairs) == copies - 1 and len(endpoints) == 2 * len(pairs)
                    minimum = 2 ** (copies - 1)
                    if total < minimum or (total == minimum) != matching:
                        raise AssertionError((ranks, overlap, copies, total, pairs))
                    cases += 1
                    equality += total == minimum
    print(f"Base two: {cases} checks, with {equality} equalities and {cases-equality} strict inequalities.")


if __name__ == "__main__":
    check_construction()
    check_rigidity()
