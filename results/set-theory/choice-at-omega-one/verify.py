"""Check the branch-support identity and the finite group used in the paper."""

from itertools import permutations, product


def prefixes(branch):
    return {branch[:i] for i in range(len(branch) + 1)}


def last_common_level(left, right):
    return len(left.intersection(right)) - 1


def check_branches():
    paths = [prefixes(word) for word in product((0, 1), repeat=4)]
    count = 0
    for r, v, s, w in permutations(paths, 4):
        outer = last_common_level(r, s)
        inner = last_common_level(v, s)
        if not outer < inner < last_common_level(s, w):
            continue
        # r and s separate first, v separates from s and w next.
        assert last_common_level(r, v) == last_common_level(r, w) == outer
        assert last_common_level(v, w) == inner
        overlap = (r ^ s) & (v ^ w)
        assert overlap and overlap == (s & w) - v
        assert overlap <= s - r and overlap <= w - v
        count += 1
    assert count > 0
    return count


def compose(left, right):
    return tuple(left[i] for i in right)


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def is_even(p):
    inversions = sum(a > b for i, a in enumerate(p) for b in p[i + 1 :])
    return inversions % 2 == 0


def check_group():
    group = {p for p in permutations(range(5)) if is_even(p)}
    inverses = {p: inverse(p) for p in group}
    commutators = {
        compose(compose(a, b), compose(inverses[a], inverses[b]))
        for a in group
        for b in group
    }
    assert commutators == group
    assert {p[0] for p in group} == set(range(5))
    return len(group)


if __name__ == "__main__":
    print(f"{check_branches()} four-branch configurations, {check_group()} group elements")
