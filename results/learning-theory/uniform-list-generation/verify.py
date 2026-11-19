"""Check the obstruction formula on small families and the first triangle obstruction."""

from itertools import combinations


def subsets(items):
    items = tuple(items)
    for size in range(len(items) + 1):
        for part in combinations(items, size):
            yield frozenset(part)


def has_list(candidates, sample, width):
    available = set.union(*(set(language) for language in candidates)) - sample
    return any(
        all(language.intersection(proposal) for language in candidates)
        for size in range(1, min(width, len(available)) + 1)
        for proposal in combinations(available, size)
    )


def check_obstruction_formula():
    # Each extra private symbol represents an infinite tail. After observing any
    # private symbol the target is known, so only samples of shared symbols matter.
    shared = {0, 1, 2}
    languages = [part | {i + 3} for i, part in enumerate(subsets(shared))]
    cases = 0
    for family in subsets(languages):
        if not family:
            continue
        for width in (1, 2, 3):
            bad_sample = -1
            for sample in subsets(shared):
                consistent = [language for language in family if sample <= language]
                if consistent and not has_list(consistent, sample, width):
                    bad_sample = max(bad_sample, len(sample))
            bad_core = -1
            for group in subsets(family):
                if len(group) < 2:
                    continue
                common = frozenset.intersection(*group)
                if not has_list(group, common, width):
                    bad_core = max(bad_core, len(common))
            assert bad_sample == bad_core
            cases += 1
    return cases


def triangle_free_colorings(order):
    edges = list(combinations(range(order), 2))
    triangles = [
        sum(1 << edges.index(edge) for edge in combinations(triple, 2))
        for triple in combinations(range(order), 3)
    ]
    return sum(
        all((coloring & triangle) not in (0, triangle) for triangle in triangles)
        for coloring in range(1 << len(edges))
    )


def check_ramsey_blocks():
    checked = 0
    for width in range(2, 6):
        for order in range(width, 8):
            vertices = list(combinations(range(order), width - 1))
            blocks = list(combinations(range(order), width))
            memberships = {
                vertex: {block for block in blocks if set(vertex) <= set(block)}
                for vertex in vertices
            }
            for block in blocks:
                targets = [vertex for vertex in vertices if block in memberships[vertex]]
                assert len(targets) == width
                for left, right in combinations(targets, 2):
                    assert memberships[left] & memberships[right] == {block}
                checked += 1
    assert triangle_free_colorings(5) == 12
    assert triangle_free_colorings(6) == 0
    return checked


if __name__ == "__main__":
    print(f"Checked {check_obstruction_formula()} family/width pairs.")
    print(f"Checked {check_ramsey_blocks()} blocks and all two-colorings of K5 and K6.")
