"""Independent exact checks of the two switched networks. Uses only Python."""
from fractions import Fraction
from itertools import combinations
from random import Random


def make_edges(pairs, marked):
    edges = set(pairs)
    interior = sorted(v for pair in pairs for v in pair)
    for v in interior:
        edges.update({(0, v), (1, v)})
    if marked:
        assert len(marked) == 5
        edges.difference_update(marked)
        special = sorted(v for pair in marked for v in pair)
        for group in (special[:5], special[5:]):
            center = group[0]
            edges.remove((0, center))
            edges.remove((1, center))
            edges.update((center, leaf) for leaf in group[1:])
        edges.add((0, 1))
    return edges


def resistances(n, edges):
    # Ground the last labeled interior vertex, independently of the proof's blocks.
    size = n - 1
    matrix = [[Fraction(0) for _ in range(2 * size)] for _ in range(size)]
    for i in range(size):
        matrix[i][size + i] = 1
    for i, j in edges:
        if i < size:
            matrix[i][i] += 1
        if j < size:
            matrix[j][j] += 1
            matrix[i][j] -= 1
            matrix[j][i] -= 1
    for i in range(size):
        pivot = matrix[i][i]
        assert pivot > 0
        matrix[i] = [v / pivot for v in matrix[i]]
        for j in range(size):
            if i != j and matrix[j][i]:
                scale = matrix[j][i]
                matrix[j] = [a - scale * b for a, b in zip(matrix[j], matrix[i])]
    inv = [row[size:] + [Fraction(0)] for row in matrix] + [[Fraction(0)] * n]
    return {(i, j): inv[i][i] + inv[j][j] - 2 * inv[i][j]
            for i, j in combinations(range(n), 2)}


def check():
    rng = Random(20261128)
    count = 0
    for m in (5, 6, 9):
        n = 2 * m + 2
        for _ in range(4):
            interior = list(range(2, n))
            rng.shuffle(interior)
            pairs = [tuple(sorted(interior[k:k + 2])) for k in range(0, 2 * m, 2)]
            old_edges = make_edges(pairs, [])
            old = resistances(n, old_edges)
            choices = list(combinations(pairs, 5))
            for marked in rng.sample(choices, min(5, len(choices))):
                new_edges = make_edges(pairs, marked)
                new = resistances(n, new_edges)
                assert len(old_edges) == len(new_edges) == 5 * m
                assert (0, 1) not in old_edges and (0, 1) in new_edges
                special = sorted(v for edge in marked for v in edge)
                groups = [special[:5], special[5:]]
                for k, reading in old.items():
                    i, j = k
                    if k == (0, 1):
                        expected = Fraction(1, m)
                    elif i < 2:
                        expected = Fraction(3, 8) + Fraction(1, 4 * m)
                    else:
                        expected = Fraction(1, 2) if k in pairs else Fraction(3, 4)
                    assert reading == expected
                    if i in special and j in special:
                        expected = Fraction(3, 4)
                        for group in groups:
                            if i in group and j in group:
                                expected = Fraction(1, 2) if i == group[0] else Fraction(2, 3)
                    assert new[k] == expected
                count += 1
    print(f'Exact all-pairs resistance formulas passed on {count} switches.')


if __name__ == '__main__':
    check()
