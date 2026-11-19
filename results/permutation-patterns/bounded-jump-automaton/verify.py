"""Count bounded-jump pattern avoiders by slot insertion. Uses only the standard library."""

from collections import Counter
from functools import cache
from itertools import combinations, permutations, product


def counts(m, patterns, n):
    """Return counts of lengths 0 through n for a positive jump bound m."""
    forbidden = frozenset(tuple(p) for p in patterns)
    if m < 1 or n < 0:
        raise ValueError("m must be positive and n must be nonnegative")
    for p in forbidden:
        if not p or sorted(p) != list(range(1, len(p) + 1)):
            raise ValueError("patterns must be nonempty permutations with ranks starting at 1")
    k = max(map(len, forbidden), default=1)
    start = (((None, None),), frozenset({()}))
    terminal = ((), frozenset())

    def update_records(records, gap, left, right):
        updated = set()
        for record in records:
            shift = left + right - 1
            before = tuple((rank, region) for rank, region in record if region <= gap)
            after = tuple((rank, region + shift) for rank, region in record if region > gap)
            updated.add(before + after)
            extended = before + ((len(record) + 1, gap + left),) + after
            if tuple(rank for rank, _ in extended) in forbidden:
                return None
            if len(extended) < k:
                updated.add(extended)
        return frozenset(updated)

    @cache
    def successors(state):
        slots, records = state
        older = tuple(tuple(None if v is None else v + 1 for v in pair) for pair in slots)
        following = []
        for gap, (previous, following_age) in enumerate(older):
            for left, right in product(range(2), repeat=2):
                # A closing side can use age m. An open side needs age below m.
                if not left and previous is not None and previous > m:
                    continue
                if not right and following_age is not None and following_age > m:
                    continue
                new_slots = older[:gap]
                if left:
                    new_slots += ((previous, 0),)
                if right:
                    new_slots += ((0, following_age),)
                new_slots += older[gap + 1:]
                if any(v is not None and v >= m for pair in new_slots for v in pair):
                    continue
                new_records = update_records(records, gap, left, right)
                if new_records is not None:
                    following.append((new_slots, new_records) if new_slots else terminal)
        return tuple(following)  # Different actions retain their multiplicity.

    row = {start: 1}
    totals = [1]
    for _ in range(n):
        following = Counter()
        for state, multiplicity in row.items():
            for target in successors(state):
                following[target] += multiplicity
        totals.append(following[terminal])
        row = following
    successors.cache_clear()
    return totals


def direct_counts(m_values, pattern_sets, n):
    result = {(m, basis): [1] for m in m_values for basis in pattern_sets}
    lengths = sorted({len(p) for basis in pattern_sets for p in basis})
    for size in range(1, n + 1):
        row = Counter()
        for perm in permutations(range(1, size + 1)):
            jump = max((abs(a - b) for a, b in zip(perm, perm[1:])), default=0)
            if jump > max(m_values):
                continue
            seen = set()
            for length in lengths:
                for subword in combinations(perm, length):
                    ranks = {value: rank for rank, value in enumerate(sorted(subword), 1)}
                    seen.add(tuple(ranks[value] for value in subword))
            for basis in pattern_sets:
                if seen.isdisjoint(basis):
                    for m in m_values:
                        if jump <= m:
                            row[m, basis] += 1
        for key in result:
            result[key].append(row[key])
    return result


if __name__ == "__main__":
    bases = [(), ((1,),), ((1, 2),), ((2, 1),)]
    bases += [(pattern,) for pattern in permutations((1, 2, 3))]
    bases += [((1, 2, 3, 4),), ((2, 4, 1, 3),), ((1, 3, 2), (2, 1, 4, 3))]
    expected = direct_counts((1, 2, 3), bases, 7)
    for (m, basis), values in expected.items():
        actual = counts(m, basis, 7)
        assert actual == values, (m, basis, actual, values)
    print(f"{len(expected)} jump-bound and pattern-set pairs agree through length 7.")
    print("m=2, forbid 1234:", counts(2, ((1, 2, 3, 4),), 10))
