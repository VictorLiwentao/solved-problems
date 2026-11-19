"""Finite checks of the rigid extension and the explicit three-color rule."""

from itertools import combinations, product


def build(vertices, edges):
    transitive = set(vertices)
    pending = list(vertices)
    while pending:
        for member in pending.pop():
            if member not in transitive:
                transitive.add(member)
                pending.append(member)

    graph = {}

    def join(a, b):
        graph.setdefault(a, set()).add(b)
        graph.setdefault(b, set()).add(a)

    root = ("root",)
    graph[root] = set()
    for y in transitive:
        join(root, ("set", y))
        for x in y:
            left, right = ("in", x, y), ("out", x, y)
            join(("set", x), left)
            join(left, right)
            join(right, ("set", y))
    for v in vertices:
        join(("original", v), ("bridge", v))
        join(("bridge", v), ("set", v))
    for a, b in edges:
        join(("original", a), ("original", b))

    lengths = {"root": 3, "set": 4, "in": 5, "out": 6, "original": 7, "bridge": 8}
    for base in list(graph):
        for length in (1, 2, lengths[base[0]]):
            last = base
            for distance in range(1, length + 1):
                node = ("pendant", base, length, distance)
                join(last, node)
                last = node
    return graph


def check_rigidity(graph):
    # Automorphisms preserve each successive partition by neighbor-class counts.
    classes = dict.fromkeys(graph, 0)
    while True:
        indices = {}
        updated = {}
        for v, neighbors in graph.items():
            signature = (classes[v], tuple(sorted(classes[w] for w in neighbors)))
            updated[v] = indices.setdefault(signature, len(indices))
        if len(indices) == len(graph):
            return
        assert len(indices) > len(set(classes.values())), "nonsingleton stable class"
        classes = updated


def check_extension(graph, original):
    colors = {("original", v): c for v, c in original.items()}
    uniform = {"root": 0, "set": 1, "in": 0, "out": 2}
    for v in graph:
        if v[0] in uniform:
            colors[v] = uniform[v[0]]
        elif v[0] == "bridge":
            colors[v] = next(c for c in range(3) if c != 1 and c != original[v[1]])
    for v in graph:
        if v[0] == "pendant":
            _, base, length, distance = v
            predecessor = base if distance == 1 else ("pendant", base, length, distance - 1)
            colors[v] = next(c for c in range(3) if c != colors[predecessor])
    assert len(colors) == len(graph)
    assert all(colors[v] != colors[w] for v in graph for w in graph[v])


def main():
    empty = frozenset()
    one = frozenset([empty])
    singleton_one = frozenset([one])
    # Several original labels share members. Some of their members are not labels.
    labels = [one, singleton_one, frozenset([empty, one]), frozenset([empty, singleton_one])]
    total = extensions = 0
    for n in range(len(labels) + 1):
        vertices = labels[:n]
        pairs = list(combinations(vertices, 2))
        for mask in product((False, True), repeat=len(pairs)):
            edges = [pair for pair, keep in zip(pairs, mask) if keep]
            graph = build(vertices, edges)
            assert all((("original", b) in graph[("original", a)]) == keep
                       for (a, b), keep in zip(pairs, mask))
            check_rigidity(graph)
            total += 1
            for values in product(range(3), repeat=n):
                original = dict(zip(vertices, values))
                if all(original[a] != original[b] for a, b in edges):
                    check_extension(graph, original)
                    extensions += 1
    print(f"Verified induced embeddings and rigidity on {total} finite graphs.")
    print(f"Verified all {extensions} proper three-color extensions on those inputs.")


if __name__ == "__main__":
    main()
