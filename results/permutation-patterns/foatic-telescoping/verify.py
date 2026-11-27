"""Direct pointwise checks of all thirteen certificates through six letters."""
from itertools import permutations


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def transform(p, symbol):
    if symbol == "I":
        return inverse(p)
    if symbol == "D":
        return transform(inverse(p), "Q")
    if symbol in ("R", "Q"):
        p = p[::-1]
    if symbol in ("C", "Q"):
        p = tuple(len(p)-1-v for v in p)
    return p


def foata(p):
    remaining = set(p)
    cycles = []
    while remaining:
        first = max(remaining)
        current = first
        cycle = []
        while current in remaining:
            remaining.remove(current)
            cycle.append(current)
            current = p[current]
        cycles.append(cycle)
    return tuple(v for cycle in reversed(cycles) for v in cycle)


def undo(word):
    cuts = [i for i, x in enumerate(word) if i == 0 or x > max(word[:i])] + [len(word)]
    p = [None] * len(word)
    for i, j in zip(cuts, cuts[1:]):
        cycle = word[i:j]
        for a, b in zip(cycle, cycle[1:] + cycle[:1]):
            p[a] = b
    return tuple(p)


def certificates(p):
    a, b, d = int(p[0] == 0), int(p[-1] == len(p)-1), int(p[-1] == 0)
    single = int(foata(p)[0] == len(p)-1)
    exc = sum(v > i for i, v in enumerate(p))
    records = sum(v == max(p[:i+1]) for i, v in enumerate(p))
    return [a, -b, -b-d, a+d, a, a, a, -b-single, a+single, exc, exc, records, records]


actions = ["CC", "RR", "QC", "QR", "IQ", "ID", "DI", "CQ", "RQ", "QI", "QQ", "QI", "QQ"]
for n in range(1, 7):
    for p in permutations(range(n)):
        f = certificates(p)
        assert undo(foata(p)) == p
        imbalance = int(p[0] == 0) - int(p[-1] == n-1)
        exc_stat = sum((v >= i) + (v > i) for i, v in enumerate(p))
        minima = sum(v == min(p[i:]) for i, v in enumerate(p))
        target = [imbalance]*9 + [exc_stat-n]*2 + [f[11]-minima]*2
        for i, (a, b) in enumerate(actions):
            image = transform(undo(transform(foata(p), a)), b)
            assert target[i] == f[i] - certificates(image)[i]
print("Thirteen pointwise identities checked on every permutation through six letters.")
