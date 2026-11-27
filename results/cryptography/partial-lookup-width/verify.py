"""Check affine interpolation, the anchored counting formula, and power-sum labels."""

from functools import lru_cache, reduce
from itertools import combinations, product
from operator import xor


def subsets(mask):
    current = mask
    while current:
        yield current
        current = (current - 1) & mask
    yield 0


def forbidden(care, ones):
    return frozenset(t for t in subsets(care)
                     if t.bit_count() % 2 == 0 and (t & ones).bit_count() % 2 == 1)


def realizable(labels, width, care, ones):
    for slope in range(1 << width):
        value = sum(((slope & label).bit_count() % 2) << i
                    for i, label in enumerate(labels))
        if (value & care) == ones or (~value & care) == ones:
            return True
    return False


def rank(vectors):
    pivots = {}
    for v in vectors:
        while v:
            bit = v.bit_length()
            if bit not in pivots:
                pivots[bit] = v
                break
            v ^= pivots[bit]
    return len(pivots)


@lru_cache(maxsize=None)
def count_by_formula(width, bad):
    return sum((-1)**size * 2**(width * (3-rank(group)))
               for size in range(len(bad)+1) for group in combinations(bad, size))


def check_tables():
    n, full = 4, 15
    columns = [(care, ones) for care in range(16) for ones in subsets(care)]
    # Six two-row disagreements and four four-row unit columns.
    sample = [((1 << u) | (1 << v), 1 << u) for u, v in combinations(range(n), 2)]
    sample += [(full, 1 << u) for u in range(n)]
    comparisons = counts = 0
    for width in range(3):
        encodings = [(0,) + labels for labels in product(range(1 << width), repeat=n-1)]
        valid = {column: set() for column in columns}
        for i, labels in enumerate(encodings):
            for column in columns:
                bad = forbidden(*column)
                predicted = all(reduce(xor, (labels[v] for v in range(n) if t >> v & 1), 0)
                                for t in bad)
                actual = realizable(labels, width, *column)
                assert predicted == actual
                if actual:
                    valid[column].add(i)
                comparisons += 1
        for selection in range(1 << len(sample)):
            chosen = [c for i, c in enumerate(sample) if selection >> i & 1]
            bad = frozenset().union(*(forbidden(*c) for c in chosen))
            direct = set(range(len(encodings))).intersection(*(valid[c] for c in chosen))
            assert count_by_formula(width, bad) == len(direct)
            counts += 1
    return comparisons, counts


def multiply(a, b):
    # GF(16) with irreducible modulus x^4 + x + 1.
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & 16:
            a ^= 0b10011
    return result


def power(a, exponent):
    result = 1
    for _ in range(exponent):
        result = multiply(result, a)
    return result


def check_field_labels():
    checks = 0
    for t in range(1, 5):
        labels = [sum(power(x, 2*j+1) << (4*j) for j in range(t)) for x in range(16)]
        for size in range(2, 2*t+1, 2):
            for group in combinations(labels, size):
                assert reduce(xor, group) != 0
                checks += 1
    return checks


if __name__ == "__main__":
    columns, counts = check_tables()
    print(f"{columns:,} interpolation comparisons and {counts:,} encoding counts passed.")
    print(f"{check_field_labels():,} bounded even subsets passed over GF(16).")
