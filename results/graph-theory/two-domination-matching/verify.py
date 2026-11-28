"""Exhaustive small graphs and exact optimization on the 23-vertex witness."""
from functools import cache
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
from small_graphs import connected_graphs, dominates


def matching(graph, available):
    @cache
    def optimum(vertices):
        if not vertices:
            return 0
        first = vertices & -vertices
        rest = vertices ^ first
        best = optimum(rest)
        partners = graph[first.bit_length() - 1] & rest
        while partners:
            partner = partners & -partners
            best = max(best, 1 + optimum(rest ^ partner))
            partners ^= partner
        return best
    return optimum(available)


def hitting_optimum(graph):
    # A 2-dominating set hits {v} union (N(v) minus {u}) for every u in N(v).
    clauses = set()
    for v, mask in enumerate(graph):
        if not mask:
            clauses.add(1 << v)
        for u in range(len(graph)):
            if mask & (1 << u):
                clauses.add((1 << v) | (mask ^ (1 << u)))
    minimal = tuple(sorted((c for c in clauses if not any(
        b != c and b & c == b for b in clauses)), key=lambda c: (c.bit_count(), c)))

    @cache
    def solve(remaining):
        if not remaining:
            return 0
        return 1 + min(solve(tuple(c for c in remaining if not c & (1 << v)))
                       for v in range(len(graph)) if remaining[0] & (1 << v))
    return solve(minimal)


def pentagons(k):
    graph = [0] * (5 * k + 3)

    def edge(u, v):
        graph[u] |= 1 << v
        graph[v] |= 1 << u
    for j in range(k):
        base = 3 + 5 * j
        for i in range(5):
            edge(base + i, base + (i + 1) % 5)
        edge(0, base)
        edge(1, base + 2)
    edge(0, 2)
    return graph


def components(graph, keep):
    total = 0
    while keep:
        component = keep & -keep
        while True:
            reached = component
            for v, neighbors in enumerate(graph):
                if component & (1 << v):
                    reached |= neighbors & keep
            if reached == component:
                break
            component = reached
        keep ^= component
        total += 1
    return total


if __name__ == "__main__":
    count = 0
    for n in range(3, 7):
        full = (1 << n) - 1
        for g in connected_graphs(n):
            degree = [row.bit_count() for row in g]
            low = sum(1 << v for v, d in enumerate(degree) if d == min(degree))
            two = sum(1 << v for v, d in enumerate(degree) if d == 2)
            fixed = low | sum(1 << v for v, row in enumerate(g) if (row & two).bit_count() == 1)
            value = min(s.bit_count() for s in range(1 << n) if dominates(g, s, 2))
            assert value <= fixed.bit_count() + matching(g, full ^ fixed)
            if n <= 5:
                assert value == hitting_optimum(g)
            count += 1
    assert count == 27474
    graph = pentagons(4)
    all_vertices = (1 << len(graph)) - 1
    cuts = [v for v in range(len(graph)) if components(graph, all_vertices ^ (1 << v)) > 1]
    leaves = [v for v, neighbors in enumerate(graph) if neighbors.bit_count() == 1]
    assert cuts == [0] and leaves == [2]
    match = matching(graph, all_vertices ^ (1 << leaves[0]))
    gamma = hitting_optimum(graph)
    assert (gamma, match) == (13, 10)
    print(f"392b checked on {count} connected labeled graphs. 392c witness: {gamma} > {match+2}.")
