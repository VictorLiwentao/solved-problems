"""Exact seed mutation for polygon triangulations, single cuts, and target arcs.

The only external dependency is SymPy, used for exact real-root counting.
Vertices have cyclic order 0,...,n-1. A cut joins two boundary edge interiors.
"""
from functools import cache
from itertools import combinations
from math import prod
from sympy import Poly, Symbol, oo

Q = Symbol("q")
ONE = Poly(1, Q)
FROZEN = Poly(Q, Q)


def diagonals(n):
    return [(a, b) for a, b in combinations(range(n), 2)
            if 1 < b - a < n - 1]


@cache
def triangulations(vertices):
    if len(vertices) <= 3:
        return ((),)
    result = []
    for i in range(1, len(vertices) - 1):
        left, right = vertices[:i + 1], vertices[i:]
        extra = tuple((v[0], v[-1]) for v in (left, right) if len(v) > 2)
        for a in triangulations(left):
            for b in triangulations(right):
                result.append(a + b + extra)
    return tuple(result)


def crosses(diagonal, arc):
    a, b = diagonal
    p, t = arc
    return a < p < b < t or p < a < t < b


def seed(n, edges, cut):
    """Quadrilateral side incidences and single-curve shear coordinates."""
    m = len(edges)
    index = {edge: i for i, edge in enumerate(edges)}
    sides = set(edges) | {(i, i + 1) for i in range(n - 1)} | {(0, n - 1)}
    matrix = [[0] * m for _ in range(m + 1)]
    for k, (e, g) in enumerate(edges):
        other = [v for v in range(n) if tuple(sorted((e, v))) in sides
                 and tuple(sorted((g, v))) in sides]
        f, h = sorted(other, key=lambda v: (v - e) % n)
        for a, b, sign in [(e, f, 1), (g, h, 1), (f, g, -1), (h, e, -1)]:
            pair = tuple(sorted((a, b)))
            if pair in index:
                matrix[index[pair]][k] += sign
            matrix[m][k] -= sign * ((a in cut) != (b in cut))
        assert matrix[m][k] % 2 == 0
        matrix[m][k] //= 2
    return matrix


def mutate_target(n, edges, matrix, arc):
    p, t = arc
    def before(k):
        a, b = edges[k]
        return b - a - 1 if a < p < b else n - 1 - (b - a)
    path = sorted((k for k, e in enumerate(edges) if crosses(e, arc)), key=before)
    if not path:
        return ONE
    values = [ONE] * len(edges) + [FROZEN]
    for k in path:
        col = [row[k] for row in matrix]
        assert values[k] == ONE
        values[k] = sum((prod((v**(s*b) for v, b in zip(values, col) if s*b > 0),
                              start=ONE) for s in [1, -1]), start=Poly(0, Q))
        matrix = [[-v if i == k or j == k
                   else v + max(col[i], 0) * max(matrix[k][j], 0)
                   - max(-col[i], 0) * max(-matrix[k][j], 0)
                   for j, v in enumerate(row)] for i, row in enumerate(matrix)]
    return values[path[-1]]


def paper_examples():
    # Use the vertex labels of the TikZ source. These sets are written one-based.
    examples = [
        (8, [(3, 1), (3, 8), (4, 8), (5, 8), (6, 8)],
         (2, 7), set(range(2, 6)), 2*Q**2 + 5*Q + 2),
        (12, [(1, 10), (12, 10), (2, 10), (2, 9), (2, 8),
              (3, 8), (3, 7), (4, 7), (5, 7)],
         (6, 11), {12, 1, 2, 3, 4, 5}, 8*Q**3 + 26*Q**2 + 22*Q + 5),
    ]
    for n, edges, arc, cut, expected in examples:
        edges = [tuple(sorted((a - 1, b - 1))) for a, b in edges]
        arc = tuple(a - 1 for a in arc)
        matrix = seed(n, edges, {a - 1 for a in cut})
        observed = mutate_target(n, edges, matrix, arc)
        assert observed == Poly(expected, Q), (observed, expected)
        print(f"{n}-gon example: {observed.as_expr()}")


if __name__ == "__main__":
    paper_examples()
    counts = 0
    seen = set()
    for n in range(4, 8):
        arcs = diagonals(n)
        for edges in triangulations(tuple(range(n))):
            for a, b in arcs:  # Nonadjacent boundary edges a and b.
                matrix = seed(n, edges, set(range(a + 1, b + 1)))
                for arc in arcs:
                    poly = mutate_target(n, edges, matrix, arc)
                    counts += 1
                    if poly in seen:
                        continue
                    seen.add(poly)
                    assert min(poly.all_coeffs()) > 0
                    for factor, _ in poly.sqf_list()[1]:
                        assert factor.count_roots(-oo, 0) == factor.degree()
    print(f"{counts} polygon seeds with target, {len(seen)} distinct polynomials, all checks passed.")
