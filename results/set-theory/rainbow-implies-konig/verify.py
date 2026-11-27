"""Check the triple-coloring lemma on finite permutation and translation groups."""

from itertools import combinations, permutations, product


def verify_group(elements, multiply, identity, label):
    indices = {x: i for i, x in enumerate(elements)}
    size = len(elements)
    table = [[indices[multiply(x, y)] for y in elements] for x in elements]
    e = indices[identity]
    inverse = [row.index(e) for row in table]

    def translate(x, subset):
        return frozenset(table[x][y] for y in subset)

    def generate(generators):
        reached = {e}
        queue = [e]
        while queue:
            x = queue.pop()
            for y in generators:
                z = table[x][y]
                if z not in reached:
                    reached.add(z)
                    queue.append(z)
        return frozenset(reached)

    patterns = {}
    for triple in combinations(range(size), 3):
        if e not in triple:
            continue
        a = frozenset(triple)
        if sum(translate(x, a) == a for x in a) != 1:
            continue
        patterns.setdefault(generate(a), []).append(a)

    partner = {}
    for subgroup, candidates in patterns.items():
        a = candidates[0]
        involutions = [x for x in subgroup if x != e and table[x][x] == e]
        if involutions:
            b = translate(min(involutions), a)
        else:
            orbit = {translate(x, a) for x in subgroup}
            b = next((c for c in candidates if c not in orbit), None)
            if b is None:
                continue
        for x in range(size):
            left, right = translate(x, a), translate(x, b)
            assert left != right
            assert partner.setdefault(left, right) == right
            assert partner.setdefault(right, left) == left

    subgroups = {frozenset([e])}
    pending = list(subgroups)
    while pending:
        h = pending.pop()
        if len(h) > 3:
            assert any(a <= h and b <= h for a, b in partner.items())
        for x in range(size):
            if x in h:
                continue
            larger = generate((*h, x))
            if larger not in subgroups:
                subgroups.add(larger)
                pending.append(larger)

    for a, b in partner.items():
        for x in range(size):
            assert partner[translate(x, a)] == translate(x, b)
        for y in a:
            for z in a:
                assert generate(translate(inverse[y], a)) == generate(translate(inverse[z], a))

    if size <= 9:
        for mask in range(1, 1 << size):
            s = frozenset(i for i in range(size) if mask & (1 << i))
            if any(a <= s and b <= s for a, b in partner.items()):
                continue
            assert sum(translate(x, s) == s for x in range(size)) <= 3
    print(f"{label}: {len(subgroups)} subgroups, {len(partner) // 2} matched pairs")


def main():
    for d in range(2, 5):
        permutations_d = list(permutations(range(d)))
        verify_group(permutations_d, lambda x, y: tuple(x[i] for i in y),
                     tuple(range(d)), f"S_{d}")
    for p, rank in [(2, 3), (3, 2), (5, 1), (7, 1)]:
        def add(x, y):
            return tuple((a + b) % p for a, b in zip(x, y))
        verify_group(list(product(range(p), repeat=rank)), add, (0,) * rank,
                     f"({p})^{rank}")


if __name__ == "__main__":
    main()
