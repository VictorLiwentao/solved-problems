"""Check the finite-support class, grid templates and sharp packing example."""

from fractions import Fraction
from itertools import combinations, product


def southwest(p, q):
    return all(x < y for x, y in zip(p, q))


def compatible(p, a, q, b):
    if not a or not b:
        return True
    if a != b:
        return southwest(p, q) if a < b else southwest(q, p)
    if a == 2:
        return (p[0] - q[0]) * (p[1] - q[1]) < 0
    return southwest(p, q) or southwest(q, p)


def finite_classes(k):
    points = list(product(range(3), repeat=2))
    constant_pairs = [set() for _ in range(k + 1)]
    count = 0

    def visit(labels):
        nonlocal count
        i = len(labels)
        if i == len(points):
            count += 1
            for s, a in enumerate(labels):
                for t in range(s):
                    if a == labels[t]:
                        constant_pairs[a].add((s, t))
                if a == 2:
                    for point, actual in zip(points, labels):
                        omitted = 2 if southwest(point, points[s]) else 1
                        assert actual != omitted
            return
        for value in range(k + 1):
            if all(compatible(points[t], a, points[i], value) for t, a in enumerate(labels)):
                visit(labels + [value])

    visit([])
    assert not constant_pairs[1] & constant_pairs[2]
    return count


def balanced_template(k, copies):
    data = []
    for label in range(k + 1):
        for j in range(copies):
            y = copies - j - 1 if label == 2 else j
            data.append(((copies * label + j, copies * label + y), label))
    for (p, a), (q, b) in combinations(data, 2):
        assert compatible(p, a, q, b)
    assert all(len({p[i] for p, _ in data}) == len(data) for i in range(2))


def sharp_packing(n, gamma, middle):
    # First two atoms are common, and index i owns private atom 2+i.
    distributions = []
    for i in range(n):
        masses = [middle - gamma, 1 - middle - gamma] + [Fraction(0)] * n
        masses[2 + i] = 2 * gamma
        assert sum(masses) == 1 and min(masses) >= 0
        distributions.append(masses)
    for i, p in enumerate(distributions):
        for j, q in enumerate(distributions):
            if i == j:
                continue
            assert sum(abs(a - b) for a, b in zip(p, q)) / 2 == 2 * gamma
            event_mass = p[0] + sum(p[2:2 + j])
            assert event_mass == (middle - gamma if j < i else middle + gamma)


if __name__ == "__main__":
    counts = [finite_classes(k) for k in (2, 3, 4)]
    for k in range(2, 8):
        for copies in (1, 2, 5):
            balanced_template(k, copies)
    for gamma in (Fraction(1, 40), Fraction(1, 4), Fraction(1, 2)):
        for middle in (gamma, Fraction(1, 2), 1 - gamma):
            sharp_packing(11, gamma, middle)
    print(f"All {sum(counts)} admissible colorings on the 3-by-3 grid satisfy the dimension witnesses.")
    print("The balanced templates and the exact total-variation cutoff agree with direct checks.")
