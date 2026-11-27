"""Compare the Walsh coefficient to direct truth tables and slice enumerators."""
from collections import Counter
from functools import lru_cache


def mask_bits(ell):
    return [int(c) for c in "0000" + "0110" * (ell - 2) + "0000"]


def direct_coefficient(ell):
    bits = mask_bits(ell)
    n = len(bits)
    mask = sum(b << i for i, b in enumerate(bits))
    # Under rotation, bit zero is the linear coordinate, bit n-1 is unused.
    first_in_pair = sum(1 << i for i in range(1, n - 1, 2))
    total = 0
    for x in range(1 << n):
        shift = (x.bit_count() - 1) % n
        rotated = ((x >> shift) | (x << (n - shift))) & ((1 << n) - 1)
        pairs = rotated & (rotated >> 1) & first_in_pair
        parity = (rotated & 1) + pairs.bit_count() + (x & mask).bit_count()
        total += 1 if parity % 2 == 0 else -1
    return total


def multiply(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            result[i+j] += u*v
    return result


@lru_cache(None)
def pair_product(linear, unused, zero_pairs, one_pairs, mixed):
    result = multiply((1, -linear), (1, unused))
    for count, factor in ((zero_pairs, (1, 2, -1)), (one_pairs, (1, -2, -1)), (mixed, (1, 0, 1))):
        for _ in range(count):
            result = multiply(result, factor)
    return result


def slice_coefficient(ell):
    signs = [1 - 2 * bit for bit in mask_bits(ell)]
    n = len(signs)
    total = 0
    for k in range(n + 1):
        pairs = Counter(signs[(k+i) % n] + signs[(k+i+1) % n] for i in range(0, n-2, 2))
        poly = pair_product(signs[(k-1) % n], signs[(k-2) % n], pairs[2], pairs[-2], pairs[0])
        total += poly[k]
    return total


def verify():
    for ell in range(3, 41):
        predicted = (1 << (2*ell)) + (1 << (3*ell - 1)) + 32*ell - 176
        assert slice_coefficient(ell) == predicted
        if ell <= 5:
            assert direct_coefficient(ell) == predicted
    coefficient = slice_coefficient(6)
    assert coefficient == 135184
    print("Slice enumerators verify the formula through 160 variables; direct truth tables agree at 12, 16 and 20.")
    print(f"At 24 variables the witness has Walsh coefficient {coefficient}, giving nonlinearity at most {2**23-coefficient//2}.")


if __name__ == "__main__":
    verify()
