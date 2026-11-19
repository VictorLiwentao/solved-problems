"""Check mod-two extension marginals on all ordered posets through five points."""

from itertools import combinations, permutations, product


def ordered_posets(n):
    pairs = tuple(combinations(range(n), 2))
    for directions in product(range(3), repeat=len(pairs)):
        rows = [0] * n
        for (a, b), direction in zip(pairs, directions):
            if direction == 1:
                rows[a] |= 1 << b
            elif direction == 2:
                rows[b] |= 1 << a
        if all(not (row >> b & 1) or not (rows[b] & ~row)
               for row in rows for b in range(n)):
            yield tuple(rows)


def restrict(rows, removed):
    low_bits = (1 << removed) - 1
    return tuple((row & low_bits) | ((row >> (removed + 1)) << removed)
                 for i, row in enumerate(rows) if i != removed)


def drop(word, removed):
    return tuple(x - (x > removed) for x in word if x != removed)


def solve_binary(equations):
    pivots = {}
    for mask, target in equations:
        while mask:
            column = mask.bit_length() - 1
            if column not in pivots:
                pivots[column] = mask, target
                break
            other, rhs = pivots[column]
            mask ^= other
            target ^= rhs
        else:
            assert target == 0, "incompatible marginals"

    chosen = 0
    for column, (mask, target) in sorted(pivots.items()):
        if (mask & chosen).bit_count() % 2 != target:
            chosen |= 1 << column
    return chosen


def check_marginals():
    previous = {(): {(): 1}}
    counts = []
    tested = 0
    for n in range(1, 6):
        current = {}
        for rows in ordered_posets(n):
            words = []
            for word in permutations(range(n)):
                positions = {x: i for i, x in enumerate(word)}
                if all(positions[x] < positions[y] for x in range(n)
                       for y in range(n) if rows[x] >> y & 1):
                    words.append(word)
            equations = []
            for x in range(n):
                target = previous[restrict(rows, x)]
                masks = dict.fromkeys(target, 0)
                for i, word in enumerate(words):
                    masks[drop(word, x)] |= 1 << i
                equations.extend((mask, target[w]) for w, mask in masks.items())
            chosen = solve_binary(equations)
            weights = {word: chosen >> i & 1 for i, word in enumerate(words)}
            assert sum(weights.values()) % 2 == 1
            for x in range(n):
                marginal = dict.fromkeys(previous[restrict(rows, x)], 0)
                for word, value in weights.items():
                    marginal[drop(word, x)] ^= value
                assert marginal == previous[restrict(rows, x)]
                tested += 1
            current[rows] = weights
        previous = current
        counts.append(len(current))
    assert counts == [1, 3, 19, 219, 4231]
    return counts, tested


def check_orientation_obstruction():
    for a, b, c, d in [(0, 1, 2, 3), (1, 0, 3, 2)]:
        background = {(b, c), (d, a)}
        imposed = {(a, b), (c, d)}

        def extensions(edges):
            return [w for w in permutations(range(4))
                    if all(w.index(x) < w.index(y) for x, y in edges)]

        assert (a < b) == (c < d)
        assert all(extensions(background | {edge}) for edge in imposed)
        assert not extensions(background | imposed)


if __name__ == "__main__":
    counts, tested = check_marginals()
    check_orientation_obstruction()
    print(f"Ordered posets by size: {counts}")
    print(f"Verified {tested} deletion marginals and both four-cycle obstructions.")
