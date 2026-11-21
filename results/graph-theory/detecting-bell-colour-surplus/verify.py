"""Direct enumeration of stable partitions and one-vertex moves."""
from itertools import combinations


def partitions(n, k):
    if not n:
        yield ()
        return
    for p in partitions(n - 1, k):
        for value in range(min(k, max(p, default=-1) + 2)):
            yield p + (value,)


def delete_vertex(p, i):
    renaming = {}
    return tuple(renaming.setdefault(v, len(renaming)) for v in p[:i] + p[i+1:])


def complete_bell_order(n, edges, k):
    states = [p for p in partitions(n, k) if all(p[i] != p[j] for i, j in edges)]
    for p, q in combinations(states, 2):
        assert any(delete_vertex(p, i) == delete_vertex(q, i) for i in range(n))
    return len(states)


for palette in range(2, 7):
    for clique in (palette, palette - 1):
        edges = list(combinations(range(clique), 2))
        assert complete_bell_order(clique + 1, edges, palette) == palette

join_edges = [(0, 1)] + [(i, j) for i in (0, 1) for j in (2, 3, 4)]
assert complete_bell_order(5, join_edges, 4) == 4
print("Stable-partition enumeration confirms both families and the equal-order pair.")
