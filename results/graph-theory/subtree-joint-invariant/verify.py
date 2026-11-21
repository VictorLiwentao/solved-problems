"""Enumerate each subtree by its highest vertex and compare complete histograms."""
from collections import Counter

PARENTS = (
    (1, 2, 3, 4, 5, 4, 3, 8, 2, 10, 11, 10, 1, 14, 15, 16, 17, 16, 15, 14, 21, 1),
    (1, 2, 3, 4, 5, 4, 3, 8, 2, 1, 11, 12, 13, 14, 13, 12, 11, 18, 19, 18, 1, 22),
)


def invariants(parents):
    order = len(parents) + 1
    neighbours = [set() for _ in range(order)]
    children = [[] for _ in range(order)]
    for child, parent in enumerate(parents, start=1):
        parent -= 1
        neighbours[parent].add(child)
        neighbours[child].add(parent)
        children[parent].append(child)

    descendants = [None] * order
    histogram = Counter()
    for root in reversed(range(order)):
        sets = {frozenset([root])}
        for child in children[root]:
            sets |= {first | second for first in sets for second in descendants[child]}
        descendants[root] = sets
        for vertices in sets:
            edges = len(vertices) - 1
            boundary = sum(len(neighbours[v] - vertices) for v in vertices)
            leaves = sum(len(neighbours[v] & vertices) == 1 for v in vertices)
            histogram[edges, boundary, 1 if edges == 1 else leaves] += 1

    def size(vertex, parent):
        return 1 + sum(size(v, vertex) for v in neighbours[vertex] if v != parent)

    centroids = []
    for v in range(order):
        sizes = sorted(size(u, v) for u in neighbours[v])
        if max(sizes) <= order // 2:
            centroids.append(sizes)
    return histogram, centroids


first, second = map(invariants, PARENTS)
assert first[0] == second[0]
assert (len(first[0]), sum(first[0].values())) == (405, 14532)
assert first[1] == [[4, 7, 11]] and second[1] == [[2, 9, 11]]
print("All 405 coefficients agree. Distinct centroid branch sizes certify nonisomorphism.")
