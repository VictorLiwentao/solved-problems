"""Exhaust all 1,024 simple graphs on five vertices."""
from fractions import Fraction
from itertools import combinations


def rank(matrix):
    rows = [list(map(Fraction, row)) for row in matrix]
    i = 0
    for j in range(len(rows)):
        pivot = next((k for k in range(i, len(rows)) if rows[k][j]), None)
        if pivot is None:
            continue
        rows[i], rows[pivot] = rows[pivot], rows[i]
        for k in range(i+1, len(rows)):
            scale = rows[k][j]/rows[i][j]
            rows[k] = [x-scale*y for x,y in zip(rows[k], rows[i])]
        i += 1
    return i


n = 5
pairs = list(combinations(range(n), 2))
for mask in range(1 << len(pairs)):
    graph = [set() for _ in range(n)]
    for bit, (i, j) in enumerate(pairs):
        if mask >> bit & 1:
            graph[i].add(j)
            graph[j].add(i)
    cards = [[len(graph[i] - {j}) if i != j else 0 for j in range(n)] for i in range(n)]
    color = {}
    bipartite = 0
    for v in range(n):
        if v in color:
            continue
        todo = [v]
        color[v] = 0
        ok = True
        while todo:
            a = todo.pop()
            for b in graph[a]:
                if b not in color:
                    color[b] = 1 - color[a]
                    todo.append(b)
                elif color[b] == color[a]:
                    ok = False
        bipartite += ok
    assert n - rank(cards) == bipartite
print("Rank formula agrees with independent component coloring on all 1,024 five-vertex graphs.")
