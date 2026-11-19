"""Check the finite orbit, character, and fork identities used in the tree proof."""

from itertools import combinations

DIMENSION = 4
VECTORS = range(1 << DIMENSION)


def subspaces():
    spaces = {frozenset({0})}
    for vector in VECTORS:
        spaces.update(
            space | frozenset(x ^ vector for x in space)
            for space in tuple(spaces)
        )
    return sorted(spaces, key=lambda space: (len(space), tuple(sorted(space))))


def annihilator(space):
    return frozenset(
        vector for vector in VECTORS
        if all((vector & character).bit_count() % 2 == 0 for character in space)
    )


def coset_labels(subgroup):
    return tuple(min(vector ^ shift for shift in subgroup) for vector in VECTORS)


def main():
    spaces = subspaces()
    stabilizers = {space: annihilator(space) for space in spaces}
    pairs = [(p, c) for p, c in combinations(spaces, 2) if p < c]
    jumps = 0
    for fixed in VECTORS:
        moving = [x for x in VECTORS if x & fixed == 0]
        labels = {}
        for space, stabilizer in stabilizers.items():
            supported = [d for d in space if d & ~fixed == 0]
            assert (set(moving) <= stabilizer) == (len(supported) == len(space))
            joined = {a ^ b for a in moving for b in stabilizer}
            labels[space] = coset_labels(joined)
            assert len(set(labels[space])) == len(supported)
        for parent, child in pairs:
            fibers = {}
            for lower, higher in zip(labels[parent], labels[child]):
                fibers.setdefault(lower, set()).add(higher)
            sizes = {len(fiber) for fiber in fibers.values()}
            assert len(sizes) == 1
            if len(set(labels[child])) > len(set(labels[parent])):
                # The distinguished orbit above the zero parent has a sibling.
                assert fibers[0] - {0}
                jumps += 1
    print(f"{len(spaces)} character spaces, {len(pairs)} inclusions, "
          f"{len(VECTORS)} coordinate supports, {jumps} strict orbit refinements")


if __name__ == "__main__":
    main()
