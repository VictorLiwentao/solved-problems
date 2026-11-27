"""Verify full distance tables and the grounded trace comparison on a finite pair."""
from collections import Counter
from fractions import Fraction
from itertools import product


def cone(cycles):
    n = sum(cycles)
    graph = [set() for _ in range(n + 1)]
    start = 0
    for size in cycles:
        for j in range(size):
            v = start + j
            for w in (start + (j + 1) % size, n):
                graph[v].add(w)
                graph[w].add(v)
        start += size
    return graph


def signatures(graph):
    n = len(graph)
    d = [[0 if u == v else 1 if v in graph[u] else 2 for v in range(n)] for u in range(n)]
    def pair(u, v):
        counts = Counter(zip(d[u], d[v]))
        return tuple(counts[i, j] for i, j in product(range(3), repeat=2))
    return Counter(tuple(sorted((v == n-1, pair(u,v)) for v in range(n))) for u in range(n))


def trace_grounded(graph):
    # Ground the hub. Invert I+L_base using exact elimination.
    n = len(graph) - 1
    rows = [[Fraction(len(graph[i]) if i == j else -int(j in graph[i])) for j in range(n)]
            + [Fraction(i == j) for j in range(n)] for i in range(n)]
    for j in range(n):
        rows[j] = [a / rows[j][j] for a in rows[j]]
        for k in range(n):
            if j != k:
                factor = rows[k][j]
                rows[k] = [x-factor*y for x,y in zip(rows[k],rows[j])]
    return sum(row[n+i] for i,row in enumerate(rows))


for m in (5, 6, 8):
    a, b = cone([2*m]), cone([m, m])
    assert signatures(a) == signatures(b)
    assert trace_grounded(a) < trace_grounded(b)
print("Full distance-intersection signatures match and the rational grounded traces differ for three cone pairs.")
