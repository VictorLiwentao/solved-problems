"""Check the witness coefficient independently via the Schur alternant in finite variables."""
from collections import Counter
from itertools import accumulate
from math import factorial, prod


def partitions(n, maximum):
    if n == 0:
        yield ()
        return
    for first in range(min(n, maximum), 0, -1):
        for tail in partitions(n - first, first):
            yield (first, *tail)


def dominates(upper, lower):
    return all(a >= b for a, b in zip(accumulate(upper), accumulate(lower)))


def witness(parts, shape):
    candidates = [p for p in parts if len(p) == len(shape) and p != shape and dominates(p, shape)]
    # The sum of the prefix sums strictly increases along every strict dominance step.
    return min(candidates, key=lambda p: sum(accumulate(p)))


def coefficient(shape, sizes):
    # Extract x^(shape+delta) from X_G times det(x_i^(r-j)). In r colors X_G
    # uses one whole part per color. Enumerate only compatible determinant terms.
    rank = len(shape)
    targets = [part + rank - i - 1 for i, part in enumerate(shape)]
    available = Counter(sizes)

    def expand(row, powers):
        if row == rank:
            inversions = sum(a < b for i, a in enumerate(powers) for b in powers[i + 1:])
            return (-1) ** inversions
        total = 0
        for size in available:
            power = targets[row] - size
            if available[size] and 0 <= power < rank and power not in powers:
                available[size] -= 1
                total += expand(row + 1, powers + (power,))
                available[size] += 1
        return total

    return expand(0, ()) * prod(factorial(count) for count in available.values())


if __name__ == "__main__":
    tested = 0
    for n in range(4, 17):
        parts = list(partitions(n, n))
        for shape in parts:
            if len(shape) == 1 or shape[1] == 1:
                continue
            sizes = witness(parts, shape)
            value = coefficient(shape, sizes)
            assert value < 0, (shape, sizes, value)
            tested += 1
    assert coefficient((2, 2), (3, 1)) == -1
    print(f"Verified a negative coefficient for all {tested} non-hook shapes through size 16.")
