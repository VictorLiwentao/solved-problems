"""Independent small-graph checks and end-to-end tests of the rational decoder."""
from fractions import Fraction
from itertools import combinations, product
from math import prod

from decode import decode, resistances


def is_tree(n, edges):
    if len(edges) != n - 1:
        return False
    groups = list(range(n))
    for u, v in edges:
        a, b = groups[u], groups[v]
        if a == b:
            return False
        groups = [a if x == b else x for x in groups]
    return True


def tree_readings(n, weights, pairs):
    # The resistance is the weighted separating two-forest sum divided by
    # the weighted spanning-tree sum (all-minors matrix-tree theorem).
    edges = [e for e, w in weights.items() if w]
    def mass(es):
        return prod(weights[e] for e in es)
    trees = sum(mass(es) for es in combinations(edges, n-1) if is_tree(n, es))
    if not trees:
        return None
    forests = [(es, mass(es)) for es in combinations(edges, n-2)]
    return [Fraction(sum(value for es, value in forests if is_tree(n, (*es, e))), trees)
            for e in pairs]


def check_separation():
    n = 4
    pairs = list(combinations(range(n), 2))
    connected = []
    for flags in product((0, 1), repeat=len(pairs)):
        measured = tree_readings(n, dict(zip(pairs, flags)), pairs)
        if measured is not None:
            connected.append((flags, measured))
    minimum = 1
    for (a, ra), (b, rb) in combinations(connected, 2):
        gap = max(abs(x-y) for i, (x, y) in enumerate(zip(ra, rb)) if a[i] != b[i])
        minimum = min(minimum, gap)
        assert gap >= Fraction(2, n*n)
    assert len(connected) == 38 and minimum == Fraction(1, 4)
    return len(connected)*(len(connected)-1)//2


def check_decoder(n, known, hidden, alphabet, noise_signs):
    pairs = list(hidden)
    levels = sorted(alphabet)
    W = max([*known.values(), *levels])
    eta = Fraction(63, 64) * min(b-a for a, b in zip(levels, levels[1:])) / (n*W)**2
    readings = tree_readings(n, known | hidden, pairs)
    for signs in noise_signs:
        data = [r + s*eta for r, s in zip(readings, signs, strict=True)]
        assert list(hidden.values()) == decode(n, known, pairs, levels, data, eta)


if __name__ == "__main__":
    count = check_separation()
    unknown = [(0,1), (2,3), (0,2), (1,3)]
    for n in range(4, 13):
        known = {pair: 1 for pair in combinations(range(n), 2) if pair not in unknown}
        first = resistances(n, known, unknown, [0,0,1,1])
        second = resistances(n, known, unknown, [1,1,0,0])
        assert all(abs(a-b) == Fraction(2, n*(n-2)) for a,b in zip(first,second))
    print("Four ambiguous readings match the sharpness construction for n = 4 through 12.")
    check_decoder(3, {(0,1): 1}, {(0,2): 1, (1,2): 0}, [0,1], product((-1,1), repeat=2))
    check_decoder(3, {(0,1): 1, (1,2): 1}, {(0,2): 1}, [0,1], [(1,), (-1,)])
    for matching in [{(0,1), (2,3)}, {(0,2), (1,3)}]:
        unknown = [(0,1), (2,3), (0,2), (1,3)]
        bits = {p: int(p not in matching) for p in unknown}
        check_decoder(4, {(0,3): 1, (1,2): 1}, bits, [0,1], [(1,-1,1,-1), (-1,1,-1,1)])
    check_decoder(4, {(0,1): 1, (1,2): 2}, {(0,2): Fraction(1,3), (0,3): 2, (2,3): 0},
                  [0,Fraction(1,3),2,5], [(1,-1,1), (-1,1,-1)])
    print(f"All {count} pairs of connected labeled four-vertex graphs satisfy the separation bound.")
    print("Exact rational decoding passed 12 noisy instances, including binary and four-level weights.")
