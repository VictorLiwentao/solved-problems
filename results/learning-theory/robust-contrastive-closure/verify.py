"""Compare direct corruption counts with deletion of observed edges."""
from itertools import combinations, product


def check():
    # One point of each occupied membership type of the three-target example.
    targets = [{1, 2}, {0, 2}, {0, 1}]
    edges = list(combinations(range(4), 2))
    cuts = [{e for e in edges if sum(x in h for x in e) == 1} for h in targets]
    assert all(sum(e not in cut for cut in cuts) >= 1 for e in edges)
    for size in range(len(edges) + 1):
        for chosen in combinations(edges, size):
            E = set(chosen)
            for budget in range(3):
                direct = {i for i, cut in enumerate(cuts) if len(E - cut) <= budget}
                deletion = set()
                for d in range(min(size, budget) + 1):
                    for removed in combinations(E, d):
                        deletion.update(i for i, cut in enumerate(cuts) if E - set(removed) <= cut)
                assert direct == deletion
    for observations in product(edges, repeat=5):
        losses = [sum(e not in cut for e in observations) for cut in cuts]
        discarded = losses.index(max(losses))
        assert all(i != discarded for i, loss in enumerate(losses) if 3 * loss < len(observations))


if __name__ == '__main__':
    check()
    print('Verified robust deletion equivalence and all length-five violation-count decisions.')
