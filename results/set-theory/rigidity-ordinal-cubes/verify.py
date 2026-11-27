"""Check the path construction on every subset of the three-bit cube."""
from itertools import combinations, permutations, product


def split(cell):
    index = next(i for i in range(3) if len({point[i] for point in cell}) == 2)
    return [tuple(point for point in cell if point[index] == bit) for bit in (0, 1)]


def arcs(cell):
    if len(cell) <= 1:
        return set()
    halves = split(cell)
    children = [
        child
        for half in halves
        for child in (split(half) if len(half) > 1 else [half])
    ]
    edges = set().union(*(arcs(child) for child in children))
    for left, right in zip(children, children[1:]):
        edges.update(product(left, right))
    return edges


def verify():
    points = tuple(product((0, 1), repeat=3))
    domains = candidates = 0
    for size in range(len(points) + 1):
        for cell in combinations(points, size):
            edges = arcs(cell)
            for ordering in permutations(cell):
                candidates += 1
                if ordering == cell:
                    continue
                mapping = dict(zip(cell, ordering))
                if all((mapping[a], mapping[b]) in edges for a, b in edges):
                    raise AssertionError((cell, ordering))
            domains += 1
    print(f"Rigid on {domains} subfamilies, across {candidates} candidate permutations.")


if __name__ == "__main__":
    verify()
