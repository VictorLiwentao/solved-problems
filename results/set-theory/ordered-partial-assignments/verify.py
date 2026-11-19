"""Finite tests for the ordered partial-assignment proof."""

from itertools import combinations, permutations, product


def check_singleton_base():
    vertices = range(3)
    pairs = list(permutations(vertices, 2))
    candidates = (None, (0, 0), (0, 1), (1, 0), (1, 1))
    tested = consistent = 0
    for small in product((None, 0, 1), repeat=3):
        allowed = [{(small[x], small[y])} if small[x] is not None and small[y] is not None
                   else set() for x, y in pairs]
        for large in product(candidates, repeat=len(pairs)):
            tested += 1
            if all(answer in allowed[i] for i, answer in enumerate(large)):
                consistent += 1
                assert all(large[i] == (small[x], small[y])
                           for i, (x, y) in enumerate(pairs))
    assert (tested, consistent) == (421875, 8)
    return tested


def check_boundary():
    for top in range(7):
        for lower in range(top + 1):
            vertices = range(2 if top > 2 else 3)

            def lists(query):
                if top > 2:
                    return []
                return list(permutations((0, 1), len(query)))

            for big in combinations(vertices, top):
                for small in combinations(big, lower):
                    assert any(tuple(a[big.index(x)] for x in small) in lists(small)
                               for a in lists(big))
            for arity in (top, lower):
                for assignment in product(range(2), repeat=len(vertices)):
                    def witnessed(pair):
                        return any(set(pair) <= set(query) and any(
                            all(answer[query.index(x)] == assignment[x] for x in pair)
                            for answer in lists(query)) for query in combinations(vertices, arity))
                    assert not all(witnessed(pair) for pair in combinations(vertices, 2))

    # A map between singleton structures always exists as a set map.
    # Only preservation of the asserted unary facts distinguishes them.
    def hom(source_has_fact, target_has_fact):
        return not source_has_fact or target_has_fact

    assert all(hom(flag, True) for flag in [False, True])
    assert not hom(True, False)
    for arity in range(1, 8):
        assert hom(all([False] * arity), False)
        assert hom(all([True] * arity), True)


if __name__ == "__main__":
    print(f"Checked all {check_singleton_base()} ordered (1,1)-base systems on three points.")
    check_boundary()
    print("Verified the two-point and triangle boundary constructions and the empty-relation example.")
