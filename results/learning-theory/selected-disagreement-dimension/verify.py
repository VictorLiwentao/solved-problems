"""Check the singleton selection witnesses and every realizable support on three data points."""
from itertools import combinations


def subsets(points):
    for size in range(len(points) + 1):
        yield from map(frozenset, combinations(points, size))


def main():
    ordinary = tuple(range(3))
    finite_sets = list(subsets(ordinary))
    markers = {("marker", i): i for i in range(len(finite_sets))}
    domain = (*ordinary, *markers)
    fallback = "fallback"
    center = "center"
    preference = [fallback, *range(len(finite_sets)), center]

    def label(hypothesis, point):
        if hypothesis == center:
            return None
        if hypothesis == fallback:
            return fallback if point in markers else None
        if point in markers:
            return None if markers[point] == hypothesis else hypothesis
        return hypothesis if point in finite_sets[hypothesis] else None

    for marker, index in markers.items():
        feasible = [h for h in preference if label(h, marker) is None]
        assert feasible == [index, center]
        assert frozenset(x for x in ordinary if label(index, x) is not None) == finite_sets[index]

    total = 0
    for target in preference:
        agreement = {
            h: frozenset(x for x in domain if label(h, x) == label(target, x))
            for h in preference
        }
        for support in subsets(domain):
            selected = next(h for h in preference if support <= agreement[h])
            if any(label(target, x) is not None for x in support):
                assert selected == target
            else:
                names = {markers[x] for x in support if x in markers}
                assert selected in {fallback, center} | names
                if len(names) >= 2:
                    assert selected == center
            total += 1
    print(f"Checked {len(markers)} singleton witnesses and {total:,} realizable supports.")


if __name__ == "__main__":
    main()
