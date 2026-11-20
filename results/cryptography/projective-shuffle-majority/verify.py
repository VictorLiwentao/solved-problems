"""Check all input triples and the full opened-deck distribution."""
from collections import Counter
from itertools import combinations, product

PRIME = 5
INFINITY = 5
PAIRS = ((0, 1), (2, INFINITY), (4, 3))


def vector(point):
    return (1, 0) if point == INFINITY else (point, 1)


def determinant(u, v):
    return u[0] * v[1] - u[1] * v[0]


def decode(triple):
    u, v, w = map(vector, triple)
    value = determinant(u, v) * determinant(v, w) * determinant(w, u) % PRIME
    assert value != 0
    return int(value not in (1, 4))


def action(a, b, c, d, point):
    x, y = vector(point)
    numerator = (a * x + b * y) % PRIME
    denominator = (c * x + d * y) % PRIME
    if denominator == 0:
        return INFINITY
    return numerator * pow(denominator, -1, PRIME) % PRIME


def main():
    group = set()
    for a, b, c, d in product(range(PRIME), repeat=4):
        if (a * d - b * c) % PRIME == 1:
            group.add(tuple(action(a, b, c, d, x) for x in range(6)))
    assert len(group) == 60
    triples = list(combinations(range(6), 3))
    for bits in product(range(2), repeat=3):
        red = [pair[bit] for pair, bit in zip(PAIRS, bits)]
        majority = int(sum(bits) >= 2)
        histogram = Counter(tuple(sorted(g[x] for x in red)) for g in group)
        expected = {triple: 6 for triple in triples if decode(triple) == majority}
        assert len(expected) == 10 and histogram == expected
    print("Verified all 480 input/shuffle combinations and both output simulators.")


if __name__ == "__main__":
    main()
