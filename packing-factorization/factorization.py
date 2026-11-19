"""Find splitting overlaps and construct counterexample words when a split fails."""
from bisect import bisect_right
from collections import deque


def boundary(pattern, size):
    prefix, suffix = pattern[:size], pattern[-size:]
    if sorted(range(size), key=prefix.__getitem__) != sorted(range(size), key=suffix.__getitem__):
        raise ValueError(f"pattern disagrees with itself on overlap {size}")
    return tuple(sorted(prefix)), tuple(sorted(suffix))


def gap_witnesses(pattern, seam, alphabet, left):
    """Return a shortest outward overlap word for each occupiable seam gap."""
    k = len(pattern)
    directions = {}
    for a in sorted(set(alphabet)):
        p, s = boundary(pattern, a)
        here, there = (p, s) if left else (s, p)
        directions[a] = (here, (0,)+there+(k+1,))
    p, s = boundary(pattern, seam)
    anchors = (0,) + (s if left else p) + (k+1,)
    occupied = {}
    for h, (low, high) in enumerate(zip(anchors, anchors[1:])):
        if high > low+1:
            occupied[h] = ()
            continue
        states = deque([(low, ())])
        seen = {low}
        while states and h not in occupied:
            cut, word = states.popleft()
            for a, (here, there) in directions.items():
                i = bisect_right(here, cut)
                if there[i+1] > there[i]+1:
                    occupied[h] = word+(a,)
                    break
                if there[i] not in seen:
                    seen.add(there[i])
                    states.append((there[i], word+(a,)))
    return occupied


def obstruction(pattern, seam, alphabet):
    """Return (left word, right word, common gap) on failure and None on success."""
    k = len(pattern)
    alphabet = set(alphabet)
    if sorted(pattern) != list(range(1, k+1)):
        raise ValueError("expected a permutation of ranks 1 to K")
    if seam not in alphabet or any(not 1 <= a < k for a in alphabet):
        raise ValueError("the overlap alphabet must contain the marked seam")
    left = gap_witnesses(pattern, seam, alphabet, True)
    right = gap_witnesses(pattern, seam, alphabet, False)
    for h in sorted(left.keys() & right.keys()):
        return tuple(reversed(left[h])), right[h], h
    return None
