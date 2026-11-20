"""Count weak order maps directly from the two marked Hasse diagrams."""
from itertools import product


def count(size, edges, colors):
    return sum(all(f[a] <= f[b] for a, b in edges) for f in product(range(colors), repeat=size))


def substitute(edges, copies):
    # Vertex 0 is marked. Delete it and use 'copies' incomparable vertices instead.
    vertices = list(range(4, 4 + copies))

    def image(v):
        return vertices if v == 0 else [v - 1]

    return [(u, v) for a, b in edges for u in image(a) for v in image(b)]


if __name__ == "__main__":
    first = [(0, 2), (1, 2), (2, 3)]
    second = [(0, 1), (2, 3), (3, 4)]
    for copies in [0, 1]:
        size = 4 + copies
        # Each order polynomial has degree at most size.
        for colors in range(size + 1):
            assert count(size, substitute(first, copies), colors) == count(size, substitute(second, copies), colors)
    values = tuple(count(6, substitute(edges, 2), 3) for edges in (first, second))
    assert values == (138, 140)
    print(f"Deletion and original order polynomials agree. Two replacements give {values} at three colors.")
