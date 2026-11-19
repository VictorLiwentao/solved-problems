"""Exact finite checks for the adjacent jumps of Catalan permutations."""

from collections import Counter
from itertools import groupby, permutations, product
from math import comb, exp, pi, sqrt


def dyck_paths(n, up=0, down=0, prefix=()):
    if down == n:
        yield prefix
        return
    if up < n:
        yield from dyck_paths(n, up + 1, down, prefix + (1,))
    if down < up:
        yield from dyck_paths(n, up, down + 1, prefix + (-1,))


def bjs(path):
    """Set the exceedances from the valleys, then fill remaining values in order."""
    n = len(path) // 2
    sigma = [0] * n
    up = down = 0
    even_heights = []
    for time, step in enumerate(path):
        if step == 1:
            if time and path[time - 1] == -1:
                sigma[down - 1] = up + 1
            up += 1
        else:
            down += 1
        if time % 2:
            even_heights.append(up - down)
    used = set(sigma)
    remaining = iter(v for v in range(1, n + 1) if v not in used)
    return tuple(v or next(remaining) for v in sigma), even_heights


def avoids_123(perm):
    first = second = len(perm) + 1
    for value in perm:
        if value < first:
            first = value
        elif value < second:
            second = value
        else:
            return False
    return True


def jump_pair(perm):
    differences = [b - a for a, b in zip(perm, perm[1:])]
    return max([0, *differences]), max([0, *(-v for v in differences)])


def check_prefix_estimate(sigma, heights):
    delta = [value - index for index, value in enumerate(sigma, 1)]
    signs = [1 if value > 0 else -1 for value in delta]
    error = max(abs(d - s*h) for d, s, h in zip(delta, signs, heights))
    length = 1 + max(sum(1 for _ in run) for _, run in groupby(signs))
    height = rise = fall = 0
    for i, current_height in enumerate(heights):
        height = max(height, current_height)
        if i:
            step = sigma[i] - sigma[i - 1]
            rise, fall = max(rise, step), max(fall, -step)
        for value in (rise, fall):
            assert 2*height - 8*length - 2*error - 1 <= value <= 2*height + 2*error + 1


def binary_words(sigma):
    x = [int(value > i) for i, value in enumerate(sigma, 1)]
    y = [0] * len(sigma)
    for value, bit in zip(sigma, x):
        y[value - 1] = bit
    return x, y


def check_rank_matching(sigma):
    x, y = binary_words(sigma)
    by_bit = [iter(i for i, bit in enumerate(y, 1) if bit == 0),
              iter(i for i, bit in enumerate(y, 1) if bit == 1)]
    assert tuple(next(by_bit[bit]) for bit in x) == sigma
    height = largest = 0
    for i, (a, b, value) in enumerate(zip(x, y, sigma), 1):
        height += a - b
        largest = max(largest, height)
        assert height >= a
        interval_count = sum(y[i:value]) if a else y[value:i].count(0)
        assert height == interval_count
    assert height == 0
    displacement = max(abs(i - value) for i, value in enumerate(sigma, 1))
    for d in range(1, len(x) + 1):
        if all(min(y[j:j+d].count(0), y[j:j+d].count(1)) > largest
               for j in range(0, len(x) - d + 1)):
            assert displacement <= d


def strip_block_count(height_limit):
    # Two blocks of three bit pairs between the exterior up and down steps.
    # Each coordinate in a block has one or two ones. Count by matrix walks.
    matrix = [[0] * height_limit for _ in range(height_limit)]
    for x in product(range(2), repeat=3):
        for y in product(range(2), repeat=3):
            if sum(x) not in (1, 2) or sum(y) not in (1, 2):
                continue
            for start in range(1, height_limit + 1):
                height = start
                for a, b in zip(x, y):
                    height += a - b
                    if not 1 <= height <= height_limit:
                        break
                else:
                    matrix[start - 1][height - 1] += 1
    return sum(matrix[0][j]*matrix[j][0] for j in range(height_limit))


def belongs_to_strip(sigma, height_limit):
    x, y = binary_words(sigma)
    if (x[0], y[0], x[-1], y[-1]) != (1, 0, 0, 1):
        return False
    if any(sum(bits[j:j+3]) not in (1, 2) for j in (1, 4) for bits in (x, y)):
        return False
    height = 0
    for a, b in zip(x[:-1], y[:-1]):
        height += a - b
        if not 1 <= height <= height_limit:
            return False
    return height == 1


def main():
    paths_checked = 0
    strip_counts = Counter()
    for n in range(1, 10):
        counts = Counter()
        for path in dyck_paths(n):
            sigma, heights = bjs(path)
            check_prefix_estimate(sigma, heights)
            check_rank_matching(sigma)
            if n == 8:
                for height_limit in (1, 2, 3, 4):
                    strip_counts[height_limit] += belongs_to_strip(sigma, height_limit)
            pi_complement = tuple(n + 1 - v for v in sigma)
            assert avoids_123(pi_complement)
            counts[jump_pair(pi_complement)] += 1
        assert sum(counts.values()) == comb(2*n, n) // (n + 1)
        paths_checked += sum(counts.values())
        if n <= 8:
            direct = Counter(jump_pair(p) for p in permutations(range(1, n+1)) if avoids_123(p))
            assert direct == counts
    for height_limit, total in strip_counts.items():
        assert total == strip_block_count(height_limit)
    print("Binary rank matching and four restricted-strip transfer counts agree.")
    # Dual theta-series evaluations of the example at m/sqrt(n) = 4.
    h = sqrt(2)
    first = 1 + 2*sum((1 - 4*j*j*h*h)*exp(-2*j*j*h*h) for j in range(1, 10))
    second = sqrt(2*pi)*pi**2/h**3 * sum(j*j*exp(-j*j*pi*pi/(2*h*h)) for j in range(1, 10))
    assert abs(first - second) < 1e-12
    print(f"Checked both prefix bounds on {paths_checked} Dyck paths through semilength 9.")
    print("Joint jump histograms agree with direct permutation enumeration through length 8.")
    print(f"Limiting surviving fraction at m/sqrt(n) = 4: {first:.9f}")


if __name__ == "__main__":
    main()
