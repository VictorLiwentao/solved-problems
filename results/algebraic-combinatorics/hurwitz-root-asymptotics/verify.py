"""Exact finite checks using the connected cut-and-join recursion (CDM Theorem 3.7)."""

from functools import cache
from fractions import Fraction
from itertools import combinations
from collections import defaultdict
from math import factorial, prod


def partitions(total, largest=None):
    if not total:
        yield ()
        return
    for first in range(1, min(total, largest or total) + 1):
        for tail in partitions(total - first, first):
            yield (first, *tail)


def counter(t):
    """Evaluate the connected, unnormalized hive polynomial at an integer t."""
    def count(genus, parts):
        return value(genus, tuple(sorted(parts, reverse=True)))

    @cache
    def value(genus, parts):
        if genus < 0:
            return 0
        if parts == (1,):
            return int(genus == 0)
        first, *rest = parts
        result = 0
        for i, part in enumerate(rest):
            result += part * count(genus, (first + part, *rest[:i], *rest[i + 1:]))
        if first > 1:
            result += (t - 1) * count(genus, (first - 1, *rest))
        for a in range(1, first):
            b = first - a
            result += count(genus - 1, (a, b, *rest))
            # The two components receive labeled cycles, even for repeated sizes.
            for size in range(len(rest) + 1):
                for subset in combinations(range(len(rest)), size):
                    left = (a, *(p for i, p in enumerate(rest) if i in subset))
                    right = (b, *(p for i, p in enumerate(rest) if i not in subset))
                    for h in range(genus + 1):
                        result += count(h, left) * count(genus - h, right)
        return result

    return count


def limiting_polynomial(m, t):
    return t * prod(Fraction(m - j + j * t, m - j) for j in range(1, m))


def literal_four_letter_counts(length):
    """Build words from their transpositions, tracking connectivity and hive size."""
    identity = tuple(range(4))
    states = {(identity, (1, 2, 4, 8), -1, 0): 1}
    for _ in range(length):
        following = defaultdict(int)
        for (perm, components, last, hive), multiplicity in states.items():
            for b in range(max(1, last), 4):
                for a in range(b):
                    image = list(perm)
                    image[a], image[b] = image[b], image[a]
                    union = components[a] | components[b]
                    merged = tuple(union if union & mask else mask for mask in components)
                    following[tuple(image), merged, b, hive + (last != b)] += multiplicity
        states = following
    result = defaultdict(lambda: [0] * 4)
    for (perm, components, last, hive), multiplicity in states.items():
        if components[0] == 15:
            result[perm][hive] += multiplicity
    return result


def check_published_example():
    mu = (4, 2, 1)
    # Exact sign changes around the two most negative roots. Symmetry gives two
    # reciprocal roots, and -1 and 0 then account for the full degree six.
    for genus, left, right in [(10, -5041605, -5041604), (20, -5001057, -5001056)]:
        samples = [counter(t)(genus, mu) for t in range(7)]
        differences = []
        while samples:
            differences.append(samples[0])
            samples = [b - a for a, b in zip(samples, samples[1:])]

        def evaluate(x):
            value, binomial = 0, Fraction(1)
            for i, coefficient in enumerate(differences):
                value += coefficient * binomial
                binomial *= (x - i) / (i + 1)
            return value

        assert evaluate(Fraction(left, 10**6)) * evaluate(Fraction(right, 10**6)) < 0
        assert evaluate(Fraction(-21, 10)) * evaluate(Fraction(-2)) < 0
        assert evaluate(Fraction(-1)) == evaluate(Fraction(0)) == 0


def main():
    # Direct checks from words on three letters. For a 3-cycle at genus zero
    # the two monotone factorizations have hive numbers one and two.
    for t in (-2, -1, 0, 1, 3):
        count = counter(t)
        assert count(0, (3,)) == t + t*t
        assert count(0, (1, 1)) == t

    for mu, perm in [((4,), (1, 2, 3, 0)), ((3, 1), (1, 2, 0, 3)),
                     ((2, 2), (1, 0, 3, 2)), ((2, 1, 1), (1, 0, 2, 3)),
                     ((1, 1, 1, 1), (0, 1, 2, 3))]:
        for genus in (0, 1):
            length = 4 + len(mu) - 2 + 2 * genus
            coeff = literal_four_letter_counts(length)[perm]
            for t in range(4):
                assert sum(c*t**j for j, c in enumerate(coeff)) == counter(t)(genus, mu)
    check_published_example()
    print("Literal degree-four words and the degree-seven root brackets agree.")

    checked = 0
    # Remove the predicted two modes. All remaining modes a^(2g) times
    # polynomials in g are killed by (shift - a^2)^d: a product of character
    # factors uses at most d boxes in total, hence pole order at most d.
    # d distinct evaluation points check the entire degree-(d-1) polynomial.
    for t in range(6):
        count = counter(t)
        for d in range(3, 7):
            if t >= d:
                continue
            m, k = d - 1, d - 2
            for mu in partitions(d):
                errors = []
                for g in range(1, d * (d - 3) + 5):
                    r = d + len(mu) - 2 + 2 * g
                    first = m**r * limiting_polynomial(m, t)
                    second = (k + mu.count(1)) * (1 + t) * k**r * limiting_polynomial(k, t)
                    errors.append(Fraction(factorial(d), 2) * count(g, mu) - first + second)
                for a in range(1, k):
                    for _ in range(d):
                        errors = [y - a*a*x for x, y in zip(errors, errors[1:])]
                assert errors and all(e == 0 for e in errors), (mu, t, errors)
                checked += 1
    print(f"Two dominant terms checked by cut-and-join at {checked} profile/value pairs (degrees 3–6).")


if __name__ == "__main__":
    main()
