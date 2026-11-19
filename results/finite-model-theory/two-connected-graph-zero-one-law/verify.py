"""Finite checks for edge gluing, separation, and the labelled growth count."""

from fractions import Fraction
from itertools import combinations
from math import factorial


def connected(graph, vertices):
    if not vertices:
        return False
    reached = vertices & -vertices
    while True:
        new = reached
        active = reached
        while active:
            bit = active & -active
            new |= graph[bit.bit_length() - 1] & vertices
            active ^= bit
        if new == reached:
            return new == vertices
        reached = new


def two_connected(graph, vertices):
    if vertices.bit_count() < 2 or not connected(graph, vertices):
        return False
    return all(connected(graph, vertices ^ (1 << v)) for v in range(len(graph))
               if vertices & (1 << v))


def check_separations(graph, vertices, edges):
    checked = 0
    for s, t in edges:
        if not graph[s] & (1 << t):
            continue
        poles = (1 << s) | (1 << t)
        interior = vertices ^ poles
        side = interior
        while side:
            other = interior ^ side
            if other and side < other and not any(
                graph[v] & other for v in range(len(graph)) if side & (1 << v)
            ):
                assert two_connected(graph, poles | side)
                assert two_connected(graph, poles | other)
                checked += 1
            side = (side - 1) & interior
    return checked


def run():
    normalized = []
    total_separations = 0
    for n in range(2, 7):
        edges = list(combinations(range(n), 2))
        vertices = (1 << n) - 1
        edge_sum = named = 0
        for mask in range(1 << len(edges)):
            graph = [0] * n
            for k, (s, t) in enumerate(edges):
                if mask & (1 << k):
                    graph[s] |= 1 << t
                    graph[t] |= 1 << s
            if not two_connected(graph, vertices):
                continue
            edge_sum += 2 * mask.bit_count()
            named += bool(graph[0] & 2)
            total_separations += check_separations(graph, vertices, edges)
        count = Fraction(named, factorial(n - 2))
        assert count == Fraction(edge_sum, factorial(n))
        normalized.append(count)
    for i, left in enumerate(normalized):
        for j, right in enumerate(normalized):
            if i + j + 1 < len(normalized):
                assert normalized[i + j + 1] >= left * right
    print(f"Both pieces are two-connected in all {total_separations} edge separations through six vertices.")
    print("The oriented-edge normalization and supermultiplicative inequalities agree with labelled counts.")


if __name__ == "__main__":
    run()
