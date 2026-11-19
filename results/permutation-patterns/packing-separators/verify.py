"""Compare the bounded test with the full occurrence poset on physical positions."""
from graphlib import TopologicalSorter
from itertools import permutations
from random import Random

from separators import has_separator


def direct_separators(pattern, overlap, copies):
    length = len(pattern)
    stride = length - overlap
    size = length + (copies - 1) * stride
    parents = {v: set() for v in range(size)}
    children = [set() for _ in range(size)]
    order = sorted(range(length), key=pattern.__getitem__)
    for row in range(copies):
        for x, y in zip(order, order[1:]):
            low, high = row * stride + x, row * stride + y
            parents[high].add(low)
            children[low].add(high)
    sorted_positions = tuple(TopologicalSorter(parents).static_order())
    below, above = [0] * size, [0] * size
    for v in sorted_positions:
        for p in parents[v]:
            below[v] |= below[p] | (1 << p)
    for v in reversed(sorted_positions):
        for p in children[v]:
            above[v] |= above[p] | (1 << p)

    def is_chain(subset):
        ordered = [v for v in sorted_positions if subset >> v & 1]
        return all(above[x] >> y & 1 for x, y in zip(ordered, ordered[1:]))

    return {v + 1 for v in sorted_positions
            if (below[v] | above[v] | (1 << v)).bit_count() == size
            and not is_chain(below[v]) and not is_chain(above[v])}


def compare(pattern, m, j):
    expected = bool(direct_separators(pattern, m, j))
    if has_separator(pattern, m, j) != expected:
        raise AssertionError((pattern, m, j, expected))


def admissible(pattern, m):
    return sorted(range(m), key=pattern[:m].__getitem__) == sorted(range(m), key=pattern[-m:].__getitem__)


def main():
    cases = 0
    for length in range(2, 6):
        for pattern in permutations(range(1, length + 1)):
            for m in range(1, length):
                if admissible(pattern, m):
                    for j in (1, 2, 3, 5, 6 * (m + 1) + 5):
                        compare(pattern, m, j)
                        cases += 1
    rng = Random(20261118)
    for _ in range(250):
        length = rng.randrange(6, 13)
        m = rng.randrange(1, length)
        # Rank a periodic family of affine keys to produce an admissible large overlap.
        stride = length - m
        offsets = rng.sample(range(-4 * length, 4 * length), stride)
        keys = [(i // stride + offsets[i % stride], i % stride) for i in range(length)]
        ranks = {key: j + 1 for j, key in enumerate(sorted(keys))}
        pattern = tuple(ranks[key] for key in keys)
        compare(pattern, m, rng.randint(2, 10 * (m + 1) + 2))
        cases += 1
    for length in range(8, 15):
        for a in range(3, length):
            for b in range(a + 1, length):
                for c in range(b + 2, length - 1):
                    middle = [v for v in range(1, length + 1) if v not in (1, a, b, c)]
                    p = (1, a, *middle, b, c)
                    for j in (2, 3, 9):
                        if length not in direct_separators(p, 2, j):
                            raise AssertionError((p, 2, j))
                        cases += 1
    print(f"{cases} direct-poset checks passed.")


if __name__ == "__main__":
    main()
