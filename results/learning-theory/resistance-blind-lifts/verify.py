"""Check the s=4 lifts directly, using exact integer and rational arithmetic."""
from collections import Counter, deque
from fractions import Fraction


def lift(twist, s=4):
    base = []
    size = 3
    for side in range(3):
        u, v = side, (side + 1) % 3
        last = -1 if twist and side == 0 else 1
        base.append((u, v, last))
        for _ in range(s):
            nodes = [u, *range(size, size + s - 1), v]
            size += s - 1
            for j in range(s):
                base.append((nodes[j], nodes[j + 1], -last if j == s - 1 else 1))
    graph = [set() for _ in range(2 * size)]
    for u, v, sign in base:
        for sheet in range(2):
            a = 2 * u + sheet
            b = 2 * v + (sheet ^ int(sign < 0))
            graph[a].add(b)
            graph[b].add(a)
    return graph


def grounded_inverse(graph):
    # Fraction-free Gauss--Jordan on the integer grounded Laplacian.
    n = len(graph) - 1
    rows = []
    for i in range(n):
        left = [len(graph[i]) if i == j else -int(j in graph[i]) for j in range(n)]
        rows.append(left + [int(i == j) for j in range(n)])
    previous = 1
    for k in range(n):
        pivot = rows[k][k]
        assert pivot > 0
        for i, row in enumerate(rows):
            if i != k:
                coefficient = row[k]
                rows[i] = [(pivot * x - coefficient * y) // previous for x, y in zip(row, rows[k])]
        previous = pivot
    for i, row in enumerate(rows):
        assert all(row[j] == previous * int(i == j) for j in range(n))
    num = [row[n:] + [0] for row in rows] + [[0] * (n + 1)]
    # Check the inverse relation against the original matrix, independently.
    for i in range(n):
        for j in range(n):
            assert len(graph[i]) * num[i][j] - sum(num[v][j] for v in graph[i]) == previous * int(i == j)
    return [[Fraction(num[i][i] + num[j][j] - 2 * num[i][j], previous)
             for j in range(n + 1)] for i in range(n + 1)]


def distances(graph, start):
    d = {start: 0}
    todo = deque([start])
    while todo:
        u = todo.popleft()
        for v in graph[u]:
            if v not in d:
                d[v] = d[u] + 1
                todo.append(v)
    assert len(d) == len(graph)
    return d


graphs = [lift(False), lift(True)]
a, b = map(grounded_inverse, graphs)
for i in range(len(a)):
    for j in range(0, len(a), 2):
        assert sorted(a[i][j:j + 2]) == sorted(b[i][j:j + 2])
assert [sum(len(g[u] & g[v]) for u in range(len(g)) for v in g[u]) // 6 for g in graphs] == [2, 0]
for k, graph in enumerate(graphs):
    dist = distances(graph, 0)
    terminals = [v for v in range(len(graph)) if len(graph[v]) > 2]
    assert sum(dist[v] <= 3 for v in terminals) == (3, 6)[k]
    assert all((dist[v] - dist[u]) % 2 for u in range(len(graph)) for v in graph[u]) == bool(k)
print("Two 78-vertex lifts: all resistance pairs agree fiber by fiber; triangle, parity and distance tests differ.")
