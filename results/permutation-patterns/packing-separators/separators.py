"""Decide separator existence for any admissible fixed-overlap permutation packing."""
from bisect import bisect_left, bisect_right


def cutoffs(rank, source, target, length):
    """Inclusive last rank below and first rank above the marked vertex."""
    lower = upper = rank
    by_distance = [(lower, upper)]
    for _ in range(len(source) + 1):
        last = bisect_right(source, lower)
        first = bisect_left(source, upper)
        lower = target[last - 1] if last else 0
        upper = target[first] if first < len(target) else length + 1
        by_distance.append((lower, upper))
    return by_distance


def has_separator(pattern, overlap, copies):
    """The running time is bounded in terms of pattern length and overlap alone."""
    length = len(pattern)
    if sorted(pattern) != list(range(1, length + 1)):
        raise ValueError("pattern must be a permutation of 1 through its length")
    if not 1 <= overlap < length or copies < 1:
        raise ValueError("invalid overlap or number of copies")
    prefix = pattern[:overlap]
    suffix = pattern[-overlap:]
    by_prefix = sorted(range(overlap), key=prefix.__getitem__)
    if sorted(range(overlap), key=suffix.__getitem__) != by_prefix:
        raise ValueError("prefix and suffix have different relative orders")
    prefix, suffix = sorted(prefix), sorted(suffix)
    bound = overlap + 1
    rows = min(copies, 6 * bound + 1)
    full_row = (1 << length) - 1
    full = (1 << (rows * length)) - 1
    routes = [(cutoffs(rank, prefix, suffix, length), cutoffs(rank, suffix, prefix, length))
              for rank in range(1, length + 1)]
    down, up = [], []
    for home in range(rows):
        for left, right in routes:
            below = above = 0
            for target in range(rows):
                route = left if target < home else right
                lo, hi = route[min(abs(target - home), bound)]
                shift = target * length
                below |= ((1 << lo) - 1) << shift
                above |= (full_row ^ ((1 << (hi - 1)) - 1)) << shift
            down.append(below)
            up.append(above)
    incomparable = [full ^ (lo | hi) for lo, hi in zip(down, up)]

    def contains_incomparable_pair(subset):
        remaining = subset
        while remaining:
            bit = remaining & -remaining
            if incomparable[bit.bit_length() - 1] & subset:
                return True
            remaining ^= bit
        return False

    return any(not others and contains_incomparable_pair(lo) and contains_incomparable_pair(hi)
               for lo, hi, others in zip(down, up, incomparable))
