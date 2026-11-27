"""Compare prime-alphabet counts with the source data and build both degree-31 designs."""
from itertools import product
from math import isqrt


def is_prime_power(n):
    for factor in range(2, isqrt(n) + 1):
        if n % factor == 0:
            while n % factor == 0:
                n //= factor
            return n == 1
    return n >= 2


def projective_parameters(p):
    pairs = []
    for q in range(2, isqrt(p) + 1):
        if not is_prime_power(q):
            continue
        total, d = 1 + q + q * q, 3
        while total <= p:
            if total == p:
                pairs.append((q, d))
            total = total * q + 1
            d += 1
    return pairs


def counts(p):
    divisors = sum((p - 1) % k == 0 for k in range(1, p))
    additional = len(projective_parameters(p)) + (p == 11)
    return divisors + additional, 1 + additional


def check_incidence(prime, dimension, expected_row_size):
    # With a prime field, normalize the first nonzero coordinate to one.
    vectors = [v for v in product(range(prime), repeat=dimension)
               if next((x for x in v if x), 0) == 1]
    assert len(vectors) == 31
    rows = [tuple(sum(x * y for x, y in zip(v, w)) % prime == 0
                  for w in vectors) for v in vectors]
    for lines in (rows, list(zip(*rows))):
        assert len(set(lines)) == 31
        assert {sum(line) for line in lines} == {expected_row_size}


def main():
    # All equal prime sizes in the two tables of the authors' data from 3 onward.
    all_classes = {3: 2, 5: 3, 7: 5, 11: 5, 13: 7}
    binary_classes = {3: 1, 5: 1, 7: 2, 11: 2, 13: 2, 17: 1, 19: 1, 23: 1}
    assert all(counts(p)[0] == n for p, n in all_classes.items())
    assert all(counts(p)[1] == n for p, n in binary_classes.items())
    assert counts(2) == (1, 1)
    assert projective_parameters(31) == [(2, 5), (5, 3)]
    assert counts(31) == (10, 3)
    check_incidence(2, 5, 15)
    check_incidence(5, 3, 6)
    print("Matched the published prime-size counts and constructed both degree-31 designs.")


if __name__ == "__main__":
    main()
