"""Verify the lifting theorem by comparing all pairwise order relations."""
from graphlib import TopologicalSorter
from itertools import permutations


def lift(pattern, overlap, extra_overlap, padding):
    if extra_overlap < 1 or padding < 0 or not 1 <= overlap <= len(pattern) // 2:
        raise ValueError("invalid lifting parameters")
    nlow = 2 * extra_overlap + padding
    seed = [v + nlow for v in pattern]
    new_prefix = list(range(extra_overlap + padding + 1, nlow + 1)) + seed[:overlap]
    new_middle = list(range(extra_overlap + 1, extra_overlap + padding + 1)) + seed[overlap:-overlap]
    new_suffix = list(range(1, extra_overlap + 1)) + seed[-overlap:]
    return new_prefix + new_middle + new_suffix


def reachability(pattern, overlap, copies):
    step = len(pattern) - overlap
    n = len(pattern) + (copies - 1) * step
    parents = {i: set() for i in range(n)}
    by_rank = sorted(range(len(pattern)), key=pattern.__getitem__)
    for i in range(copies):
        for a, b in zip(by_rank, by_rank[1:]):
            parents[b + i * step].add(a + i * step)
    before = [0] * n
    for v in TopologicalSorter(parents).static_order():
        for u in parents[v]:
            before[v] |= before[u] | (1 << u)
    return before


def check(seed, overlap, extra, padding, copies):
    p = lift(seed, overlap, extra, padding)
    m = overlap + extra
    actual = reachability(p, m, copies)
    original = reachability(seed, overlap, copies)
    step = len(p) - m
    low_by_position = [(p[i % step] if i < copies * step else p[-m + i - copies * step])
                       <= 2 * extra + padding for i in range(len(actual))]
    lows = [i for i, low in enumerate(low_by_position) if low]
    olds = [i for i, low in enumerate(low_by_position) if not low]
    if len(lows) != (copies + 1) * extra + copies * padding or len(olds) != len(original):
        raise AssertionError("incorrect decomposition sizes")
    low_mask = sum(1 << i for i in lows)
    # Distinct predecessor counts 0 through L-1 are equivalent to a total order on L elements.
    if sorted((actual[v] & low_mask).bit_count() for v in lows) != list(range(len(lows))):
        raise AssertionError("new positions do not form a chain")
    for v, dest in enumerate(olds):
        expected = low_mask | sum(1 << pos for u, pos in enumerate(olds) if original[v] >> u & 1)
        if actual[dest] != expected:
            raise AssertionError((seed, overlap, extra, padding, copies, v))


def main():
    cases = 0
    for length in range(2, 7):
        for p in permutations(range(1, length + 1)):
            for m in range(1, length // 2 + 1):
                if 1 not in p[:m]:
                    continue
                if sorted(range(m), key=p[:m].__getitem__) != sorted(range(m), key=p[-m:].__getitem__):
                    continue
                for extra, padding in ((1, 0), (1, 3), (2, 0), (3, 2)):
                    for copies in (1, 2, 5):
                        check(p, m, extra, padding, copies)
                        cases += 1
    print(f"{cases} full poset comparisons passed.")


if __name__ == "__main__":
    main()
