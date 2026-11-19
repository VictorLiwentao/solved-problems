"""Check the finite orbit and two-pair identities used in the proofs."""

from itertools import combinations, product


def edges_for_mask(mask):
    """Two copies of four atoms, with edges invariant under atom permutations."""
    vertices = list(product(range(2), range(4)))
    edges = set()
    for (i, a), (j, b) in combinations(vertices, 2):
        orbit = i if i == j else 2 + int(a != b)
        if mask & (1 << orbit):
            edges.add(((i, a), (j, b)))
            edges.add(((j, b), (i, a)))
    return edges


def diagonal_orbit(x, y):
    return x[0], y[0], x[1] == y[1]


def check_descent():
    graphs = [edges_for_mask(mask) for mask in range(16)]
    for graph, other in product(graphs, repeat=2):
        quotient = {(x[0], u[0]) for x, u in graph}
        other_quotient = {(y[0], v[0]) for y, v in other}
        orbit_edges = {
            (diagonal_orbit(x, y), diagonal_orbit(u, v))
            for x, u in graph
            for y, v in other
        }
        for (i, j), (k, m) in product(quotient, other_quotient):
            assert ((i, k, False), (j, m, False)) in orbit_edges
    return len(graphs) ** 2


def check_rectangles():
    colorings = set()
    for a, b, c, d in product(range(2), repeat=4):
        if a != d and b != c:
            colorings.add((a, b, c, d))
    from_choices = set()
    for axis, selected in product(range(2), repeat=2):
        colors = tuple(int(point[axis] == selected) for point in product(range(2), repeat=2))
        from_choices.add(colors)
    assert colorings == from_choices and len(colorings) == 4


def check_signatures():
    checked = 0
    for r in range(1, 4):
        rows = list(product(range(r), repeat=r + 1))
        for left, right in product(rows, repeat=2):
            if all(left[i] != right[j] for i in range(r + 1) for j in range(r + 1) if i != j):
                assert left != right
                assert (left < right) != (right < left)
                checked += 1
    return checked


if __name__ == "__main__":
    checked = check_descent()
    check_rectangles()
    signatures = check_signatures()
    print(f"Verified independent placements for {checked} pairs of orbit graphs.")
    print(f"Verified rectangle choices and {signatures} proper pairs of color rows.")
