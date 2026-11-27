"""Check the finite configurations in the canonical-clique argument.

Every ordered three-edge pattern uses at most six nonisolated vertices.
The coefficient calculation in the manuscript then handles the triangle.
"""
from collections import Counter
from itertools import combinations


def main():
    total = 0
    triangles = 0
    for size in range(3, 7):
        for edges in combinations(combinations(range(size), 2), 3):
            degrees = Counter(vertex for edge in edges for vertex in edge)
            if len(degrees) != size:
                continue
            total += 1
            if min(degrees.values()) >= 2:
                assert size == 3 and set(edges) == set(combinations(range(3), 2))
                triangles += 1
    assert triangles == 1
    print(f"{total} ordered graph patterns. The triangle is the only one without a leaf.")


if __name__ == "__main__":
    main()
