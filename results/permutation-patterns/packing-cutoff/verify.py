"""Check the packing-count formula using only the order constraints in each window.

Run with Python 3.9 or later: python3 verify.py
"""

from functools import lru_cache


def pattern(width, offset):
    """Return the ranks of the keys, listed in position order."""
    keys = [
        3 * (block + track * offset) + track
        for block in range(width)
        for track in range(3)
    ]
    ranks = {key: rank for rank, key in enumerate(sorted(keys), start=1)}
    return tuple(ranks[key] for key in keys)


def packing_count(ranks, overlap, occurrences):
    """Count all permutations satisfying the prescribed windows of any given pattern."""
    length = len(ranks)
    step = length - overlap
    size = length + (occurrences - 1) * step
    predecessors = [0] * size
    order = sorted(range(length), key=ranks.__getitem__)
    for window in range(occurrences):
        start = window * step
        for lower, upper in zip(order, order[1:]):
            predecessors[start + upper] |= 1 << (start + lower)

    @lru_cache(maxsize=None)
    def extensions(remaining):
        if not remaining:
            return 1
        count = 0
        candidates = remaining
        while candidates:
            bit = candidates & -candidates
            vertex = bit.bit_length() - 1
            if not (predecessors[vertex] & remaining):
                count += extensions(remaining ^ bit)
            candidates ^= bit
        return count

    result = extensions((1 << size) - 1)
    extensions.cache_clear()
    return result


def main():
    cases = 0
    for offset in range(1, 13):
        for width in range(offset + 2, 2 * offset + 2):
            ranks = pattern(width, offset)
            overlap = 3 * (width - 1)
            first_two = 2 * offset + 3 - width
            for occurrences in range(1, first_two + 5):
                expected = 2 ** max(0, width + occurrences - 2 * offset - 2)
                actual = packing_count(ranks, overlap, occurrences)
                if actual != expected:
                    raise AssertionError((offset, width, occurrences, expected, actual))
                cases += 1
    print(f"Exact window counts agreed with the formula in {cases} cases.")

    width = 9
    for offset in (6, 7):
        ranks = pattern(width, offset)
        counts = [packing_count(ranks, 3 * (width - 1), j) for j in range(1, 10)]
        print(f"w = {width}, d = {offset}: {counts}")


if __name__ == "__main__":
    main()
