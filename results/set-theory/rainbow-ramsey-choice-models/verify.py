"""Check the local closures and petal orbits of small finite configurations."""
from itertools import combinations, permutations


def main():
    cases = 0
    for arity in range(2, 5):
        stem = frozenset(range(arity - 1))
        for bound in range(2, 7):
            petals = tuple(range(arity - 1, arity - 1 + bound))
            domain = stem.union(petals)
            active = {stem | {v}: frozenset(petals) for v in petals}
            for size in range(1, arity + 1):
                for input_tuple in combinations(sorted(domain), size):
                    input_set = frozenset(input_tuple)
                    closure = input_set | active.get(input_set, frozenset())
                    assert closure == (domain if input_set in active else input_set)
            fixed, other = petals[:2]
            images = set()
            for rest in permutations(petals[1:]):
                permutation = dict(zip(petals, (fixed,) + rest))
                images.add(stem | {permutation[other]})
            assert images == set(active) - {stem | {fixed}}
            cases += 1
    intersection_cases = 0
    for arity in range(2, 6):
        first = frozenset(range(arity))
        for overlap in range(arity):
            second = frozenset(range(arity - overlap, 2 * arity - overlap))
            vertices = first | second
            mate = {first: second, second: first}
            for subset in combinations(sorted(vertices), arity):
                item = frozenset(subset)
                closure = item | mate.get(item, frozenset())
                active_inside = {key for key in mate if key <= closure}
                if item in mate:
                    assert closure == vertices and active_inside == {first, second}
                    assert mate[mate[item]] == item and len(item & mate[item]) == overlap
                else:
                    assert closure == item and not active_inside
            intersection_cases += 1
    print(f"Checked {cases} petal configurations and {intersection_cases} intersection configurations.")


if __name__ == "__main__":
    main()
