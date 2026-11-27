"""Check the formal-root cancellation used in the translation lemma.

Three formal roots use at most six indices. Order compression onto range(6)
preserves equality of vectors, so these tests cover every possible support.
"""
from itertools import combinations


def root(low, high):
    return tuple(int(i == high) - int(i == low) for i in range(6))


def main():
    edges = list(combinations(range(6), 2))
    roots = {root(*edge) for edge in edges}
    signed_roots = roots | {tuple(-v for v in u) for u in roots}
    for left, right in combinations(edges, 2):
        diff = tuple(v - w for v, w in zip(root(*left), root(*right)))
        shares_endpoint_in_same_position = left[0] == right[0] or left[1] == right[1]
        assert (diff in signed_roots) == shares_endpoint_in_same_position
    print("All two-root differences checked up to order-preserving relabeling.")


if __name__ == "__main__":
    main()
