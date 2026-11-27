"""Rebuild the ordinary Tamari cover graph and semidistributive rowmotion from definitions."""
from collections import Counter
from functools import cache
from itertools import combinations

BASE = "ENNNEEENEN"


def altitudes(word, east_runs):
    height = value = 0
    levels = [value]
    for step in word:
        if step == "N":
            height += 1
            value += east_runs[height]
        else:
            value -= 1
        levels.append(value)
    return levels


def verify(base):
    runs = tuple(map(len, base.split("N")))
    paths = []
    for north in combinations(range(len(base)), len(runs) - 1):
        word = "".join("N" if i in north else "E" for i in range(len(base)))
        if all(a.count("N") >= b.count("N")
               for a, b in ((word[:i], base[:i]) for i in range(len(base) + 1))):
            paths.append(word)
    upper = {p: set() for p in paths}
    lower = {p: set() for p in paths}
    for p in paths:
        levels = altitudes(p, runs)
        for i in range(len(p) - 1):
            if p[i:i+2] != "EN":
                continue
            j = levels.index(levels[i+1], i+2)
            target = p[:i] + p[i+1:j] + "E" + p[j:]
            upper[p].add(target)
            lower[target].add(p)

    @cache
    def below(p):
        return {p}.union(*(below(q) for q in lower[p]))

    # For each cover p < q its label is the unique minimum of [bottom,q] minus [bottom,p].
    down_labels = {p: set() for p in paths}
    up_labels = {p: set() for p in paths}
    for p in paths:
        for q in upper[p]:
            candidates = below(q) - below(p)
            label, = [v for v in candidates if below(v) & candidates == {v}]
            down_labels[q].add(label)
            up_labels[p].add(label)
    decoder = {frozenset(labels): p for p, labels in down_labels.items()}
    assert len(decoder) == len(paths)
    remaining = set(paths)
    totals = Counter()
    while remaining:
        start = min(remaining)
        p = start
        period = total = 0
        while p in remaining:
            remaining.remove(p)
            period += 1
            total += len(lower[p])
            p = decoder[frozenset(up_labels[p])]
        assert p == start
        totals[period, total] += 1
    return totals


spectrum = verify(BASE)
assert spectrum[22, 45] > 0 and spectrum[22, 46] > 0
print("Ordinary Tamari orbit (length, down-degree sum) frequencies:", sorted(spectrum.items()))
