"""Check the affine-basis event and every cyclic gadget in dimension three."""

from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import prod


def value(form, point):
    return (form & point).bit_count() % 2 ^ (form >> 3)


def label(pair, point):
    a, b = pair
    return (0, a) if value(a ^ b, point) == 0 else (1, b)


def main():
    points = range(8)
    forms = range(16)
    nonconstant = [c for c in forms if c & 7]
    pairs = [(a, a ^ c) for a in forms for c in nonconstant]
    fibres = {(c, i): [x for x in points if value(c, x) == i]
              for c in nonconstant for i in range(2)}
    # Every ordered sample-test affine basis in a two-dimensional flat
    # consists of three distinct points.
    for fibre in fibres.values():
        triples = list(product(fibre, repeat=3))
        assert Fraction(sum(len(set(t)) == 3 for t in triples), len(triples)) == Fraction(3, 8)
    strength = prod(1 - Fraction(1, 2 ** k) for k in range(1, 3))
    assert strength == Fraction(3, 8)
    correct = {}
    for pair in pairs:
        c = pair[0] ^ pair[1]
        for side in range(2):
            outcome = side, pair[side]
            for triple in permutations(fibres[c, side], 3):
                candidates = [h for h in pairs if all(label(h, t) == outcome for t in triple)]
                assert candidates == [pair]
                correct[pair, side, triple] = 0

    cycles = 0
    for x in points:
        for c in nonconstant:
            if value(c, x):
                continue
            for cp in nonconstant:
                if value(cp, x) != 1 or (c & 7) == (cp & 7):
                    continue
                e = c ^ cp
                flats = [[t for t in points if value(c, t) == value(cp, t) == i]
                         for i in range(2)]
                for a in forms:
                    b = a ^ c
                    rows = ((a, b), (a, b ^ e), (a ^ e, b ^ e), (a ^ e, b))
                    for j, h in enumerate(rows):
                        i = j % 2
                        other = rows[(j + 1) % 4]
                        assert all(label(h, t) == label(other, t) for t in flats[i])
                        assert label(h, x) != label(other, x)
                        for u, v in permutations(flats[i]):
                            correct[h, i, (u, v, x)] += 1
                    cycles += 1
    frequencies = Counter(correct.values())
    assert len(frequencies) == 1 and 0 not in frequencies
    print(f"{cycles:,} four-cycles checked with both orders of each training basis.")
    print(f"All {len(correct):,} target, side and affine-basis outcomes have equal multiplicity.")
    print("Affine-basis probability 3/8. Every correct consistent hypothesis is unique.")


if __name__ == "__main__":
    main()
