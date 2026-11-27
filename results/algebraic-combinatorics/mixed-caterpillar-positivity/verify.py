"""Exhaust the side orders and labelings through four vertices."""
from collections import Counter
from itertools import permutations, combinations


def extensions(n, relations):
    return [p for p in permutations(range(n)) if all(p.index(a) < p.index(b) for a, b in relations)]


def descents(word):
    return tuple(i for i in range(len(word) - 1) if word[i] > word[i + 1])


def check(words, labels):
    # Label the new u,m,r by k+1,k,k+2 on the left, k,k+1,k+2 on the right (zero-based).
    k = len(labels)
    old, target, images = Counter(), Counter(), set()
    for vertices in words:
        w = tuple(labels[v] for v in vertices)
        for i in range(k + 1):
            left = w[:i] + (k + 1,) + w[i:] + (k, k + 2)
            if i < k:
                right = w[:i] + (k,) + w[i:] + (k + 1, k + 2)
            else:
                right = tuple(k if v == k - 1 else v for v in w) + (k + 1, k - 1, k + 2)
            assert descents(left) == descents(right)
            assert right not in images
            images.add(right)
            old[descents(left)] += 1
        for i, j in combinations(range(k + 2), 2):
            it = iter(w)
            right = tuple(k if pos == i else k + 1 if pos == j else next(it)
                          for pos in range(k + 2)) + (k + 2,)
            target[right] += 1
    assert images <= target.keys()
    frequencies = Counter(descents(w) for w in target.elements())
    assert all(frequencies[key] >= value for key, value in old.items())


if __name__ == "__main__":
    count = 0
    for k in range(1, 5):
        pairs = list(combinations(range(k), 2))
        seen = set()
        for mask in range(1 << len(pairs)):
            relations = [pair for i, pair in enumerate(pairs) if mask & (1 << i)]
            words = tuple(extensions(k, relations))
            if words in seen:
                continue
            seen.add(words)
            maxima = {word[-1] for word in words}
            for labels in permutations(range(k)):
                if labels.index(k - 1) in maxima:
                    check(words, labels)
                    count += 1
    print(f"Verified injection, admissibility and descent preservation on {count} labeled side orders.")
