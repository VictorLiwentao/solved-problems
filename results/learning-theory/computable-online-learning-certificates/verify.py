"""Exhaust small classes for the unordered mistake certificates and tree traces."""

from functools import cache
from itertools import combinations, permutations, product


def bit(h, x):
    return (h >> x) & 1


def branch(version, x, y):
    return tuple(h for h in version if bit(h, x) == y)


@cache
def dimension(version):
    if not version:
        return -1
    splits = [(branch(version, x, 0), branch(version, x, 1)) for x in range(3)]
    return max((1 + min(dimension(a), dimension(b)) for a, b in splits if a and b),
               default=0)


def certificate_test(hypotheses):
    budget = dimension(hypotheses)
    families = [set() for _ in range(budget + 2)]

    def record(sample, version):
        families[len(sample)].add(sample)
        if not version:
            return
        for x in range(3):
            if any(old == x for old, _ in sample):
                continue
            left, right = (branch(version, x, y) for y in (0, 1))
            prediction = int(dimension(right) > dimension(left))
            wrong = 1 - prediction
            record(sample | {(x, wrong)}, (left, right)[wrong])

    record(frozenset(), hypotheses)
    assert all(not any(all(bit(h, x) == y for x, y in s) for h in hypotheses)
               for s in families[-1])
    maximum = 0
    for h in hypotheses:
        for order in permutations(range(3)):
            sample = frozenset()
            for x in order + order:
                if any(old == x for old, _ in sample):
                    continue
                signs = [b for b in (0, 1) if sample | {(x, b)} in families[len(sample) + 1]]
                assert signs
                if bit(h, x) == signs[0]:
                    sample |= {(x, signs[0])}
            maximum = max(maximum, len(sample))
    assert maximum == budget


def tree_test():
    # Paired entries (natural tree coordinate, free binary coordinate).
    nodes = [((0, b),) for b in (0, 1)]
    nodes += [((0, b), (1, c)) for b, c in product((0, 1), repeat=2)]
    invalid = ((2, 0),)
    hypotheses = [set()] + [{v[:k] for k in range(1, len(v) + 1)} for v in nodes]
    for labels in product((-1, 0, 1), repeat=len(nodes) + 1):
        positive = {v for v, y in zip(nodes + [invalid], labels) if y == 1}
        negative = {v for v, y in zip(nodes + [invalid], labels) if y == 0}
        if positive:
            longest = max(positive, key=len)
            path = {longest[:k] for k in range(1, len(longest) + 1)}
            accepted = longest in nodes and positive <= path and not path & negative
        else:
            accepted = True
        assert accepted == any(positive <= support and not negative & support
                               for support in hypotheses)


if __name__ == "__main__":
    for n in range(1, 9):
        for hypotheses in combinations(range(8), n):
            certificate_test(hypotheses)
    tree_test()
    print("Exact mistake bounds matched on all 255 nonempty binary classes over three inputs.")
    print("All 2187 finite partial traces agreed with the paired-prefix consistency test.")
