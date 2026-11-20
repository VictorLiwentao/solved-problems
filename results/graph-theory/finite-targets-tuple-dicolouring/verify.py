"""Check cycle-coordinate constraints and star multiplicities for small type systems."""
from itertools import combinations, permutations, product


def has_cycle(successors):
    for start in successors:
        seen = set()
        v = start
        while v in successors:
            if v in seen:
                return True
            seen.add(v)
            v = successors[v]
    return False


def main():
    orders = assignments = 0
    for n, k in [(3, 2), (4, 2), (4, 3), (5, 4)]:
        types = [frozenset(b) for b in combinations(range(n), k)]
        for length in range(2, len(types) + 1):
            for group in combinations(types, length):
                for tail in permutations(group[1:]):
                    sequence = (group[0],) + tail
                    constraints = []
                    for i in range(n):
                        edges = {j: (j + 1) % length for j, b in enumerate(sequence)
                                 if i in b and i in sequence[(j + 1) % length]}
                        constraints.append(has_cycle(edges))
                    assert any(constraints) == bool(frozenset.intersection(*sequence))
                    orders += 1
        for labels in product(range(n), repeat=n):
            constant = all(sum(j in b for j in labels) == k for b in types)
            assert constant == (len(set(labels)) == n)
            assignments += 1
    print(f"Checked {orders} cyclic orders of types and {assignments} star assignments.")


if __name__ == "__main__":
    main()
