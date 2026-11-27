"""Enumerate decorated rooted trees and compute their fundamental expansions by extensions."""
from itertools import product


def representatives(size):
    trees = {}
    for tail in product(*(range(i) for i in range(1, size))):
        parents = (-1, *tail)
        for strict in product((False, True), repeat=size - 1):
            branches = [[] for _ in parents]
            for i in reversed(range(1, size)):
                branches[parents[i]].append((strict[i - 1], tuple(sorted(branches[i]))))
            tree = tuple(sorted(branches[0]))
            trees.setdefault(tree, (parents, strict))
    return trees


def coefficients(parents, strict):
    size = len(parents)
    before = [set() for _ in parents]
    for child, parent in enumerate(parents[1:], 1):
        lower, upper = (child, parent) if strict[child - 1] else (parent, child)
        before[upper].add(lower)
    labels = {}
    while len(labels) < size:
        vertex = next(i for i in range(size) if i not in labels and before[i] <= labels.keys())
        labels[vertex] = len(labels)
    histogram = [0] * (1 << (size - 1))

    def visit(word, used, mask):
        if len(word) == size:
            histogram[mask] += 1
            return
        for vertex, parent in enumerate(parents):
            if vertex in used or (parent != -1 and parent not in used):
                continue
            descent = bool(word and labels[word[-1]] > labels[vertex])
            bit = (1 << (len(word) - 1)) if descent else 0
            visit(word + (vertex,), used | {vertex}, mask | bit)

    visit((), set(), 0)
    return tuple(histogram)


def symmetric(fundamental, size):
    monomial = list(fundamental)
    for i in range(size - 1):
        for mask in range(len(monomial)):
            if mask & (1 << i):
                monomial[mask] += monomial[mask ^ (1 << i)]
    groups = {}
    for mask, value in enumerate(monomial):
        cuts = [0] + [i + 1 for i in range(size - 1) if mask & (1 << i)] + [size]
        partition = tuple(sorted(b - a for a, b in zip(cuts, cuts[1:])))
        if groups.setdefault(partition, value) != value:
            return False
    return True


def hook(branches):
    if len({color for color, _ in branches}) != len(branches):
        return False
    for color, arm in branches:
        while arm:
            if len(arm) != 1 or arm[0][0] != color:
                return False
            arm = arm[0][1]
    return True


if __name__ == "__main__":
    total = 0
    for size in range(1, 8):
        trees = representatives(size)
        seen = set()
        for tree, data in trees.items():
            signature = coefficients(*data)
            assert signature not in seen, (size, tree)
            seen.add(signature)
            assert symmetric(signature, size) == hook(tree), (size, tree)
        total += len(seen)
        print(f"{size} vertices: {len(seen)} distinct decorated trees and enumerators")
    print(f"{total} trees also passed the hook symmetry criterion.")
