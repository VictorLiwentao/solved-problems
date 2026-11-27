"""Exact integer coefficients from the two parent lists."""
from collections import Counter
from itertools import combinations

PARENTS = (
    (1, 2, 2, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 14, 15, 16, 17, 18, 18, 19, 19, 21, 24, 25, 25, 27, 28, 29, 29, 30, 31, 32, 32, 33, 33, 33, 35, 35, 35, 35),
    (1, 2, 3, 3, 4, 4, 5, 5, 6, 7, 7, 9, 9, 9, 11, 11, 12, 12, 13, 14, 15, 15, 15, 15, 16, 17, 18, 19, 19, 22, 23, 24, 25, 29, 30, 30, 36, 37, 37, 39, 40),
)


def data(parents):
    vertices = range(1, len(parents) + 2)
    degrees = Counter(parents)
    degrees.update(vertices[1:])
    coefficients = Counter(degrees[i] + degrees[j] for i, j in combinations(vertices, 2))
    for i, parent in enumerate(parents, start=2):
        assert 1 <= parent < i
        total = degrees[i] + degrees[parent]
        coefficients[total] += 1
        coefficients[total - 1] -= 1
    return Counter(degrees.values()), coefficients


first, second = map(data, PARENTS)
assert first[0][1] == 15 and second[0][1] == 16
assert first[1] == second[1] and sum(first[1].values()) == 861
print("The square polynomials agree coefficient by coefficient, despite different leaf counts.")
