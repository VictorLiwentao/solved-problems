"""Finite checks of the local ordering lemma and the signed 3-SAT construction."""
from itertools import combinations, permutations, product


def backward_edges(order, flipped):
    position = {v: i for i, v in enumerate(order)}
    return [(a, b) for a, b in combinations(range(len(order)), 2)
            if (position[a] < position[b]) == ((a, b) in flipped)]


def graph_type(order, edges):
    neighbors = {v: set() for v in order}
    for a, b in edges:
        neighbors[a].add(b)
        neighbors[b].add(a)
    maximum_degree = max(map(len, neighbors.values()), default=0)
    unseen = set(order)
    forest = True
    while unseen:
        start = unseen.pop()
        stack = [start]
        vertex_count = degree_sum = 0
        while stack:
            vertex = stack.pop()
            vertex_count += 1
            degree_sum += len(neighbors[vertex])
            for other in neighbors[vertex] & unseen:
                unseen.remove(other)
                stack.append(other)
        forest &= degree_sum == 2 * (vertex_count - 1)
    return maximum_degree, forest


def tournament(clauses):
    """The reference orientation goes from smaller to larger except on flipped."""
    variables = sorted({abs(literal) for clause in clauses for literal in clause})
    ports = {}
    blocks = {}
    flipped = set()
    nonports = []
    size = 0
    for variable in variables:
        occurrences = [(i, j, lit) for i, clause in enumerate(clauses)
                       for j, lit in enumerate(clause) if abs(lit) == variable]
        length = 6 * len(occurrences) + 5
        blocks[variable] = range(size, size + length)
        flipped.update((v, v + 1) for v in range(size, size + length - 1))
        occupied = set()
        for occurrence, (i, j, lit) in enumerate(occurrences):
            start = size + 6 * occurrence + (2 if lit > 0 else 3)
            ports[i, j] = start, start + 1
            occupied.update(ports[i, j])
        nonports.extend(v for v in blocks[variable] if v not in occupied)
        size += length + 5
    for i in range(len(clauses)):
        for j in range(3):
            ends = ports[i, j][1], ports[i, (j + 1) % 3][0]
            flipped.add(tuple(sorted(ends)))
    for v in nonports:
        flipped.add((v, size))
        size += 1
    return size, blocks, flipped


def check_formula(clauses):
    size, blocks, flipped = tournament(clauses)
    satisfying = 0
    for values in product((False, True), repeat=len(blocks)):
        truth = dict(zip(blocks, values))
        order = list(range(size))
        for variable, block in blocks.items():
            swap_parity = 0 if truth[variable] else 1
            for v in range(block.start + swap_parity, block.stop - 1, 2):
                order[v], order[v + 1] = order[v + 1], order[v]
        degree, forest = graph_type(order, backward_edges(order, flipped))
        sat = all(any(truth[abs(lit)] == (lit > 0) for lit in clause)
                  for clause in clauses)
        assert degree == 2 and forest == sat
        satisfying += sat
    return satisfying


if __name__ == "__main__":
    adjacent = {(v, v + 1) for v in range(4)}
    matches = [p for p in permutations(range(5))
               if graph_type(p, backward_edges(p, adjacent))[0] <= 1]
    assert matches == [(0, 2, 1, 4, 3), (1, 0, 3, 2, 4)]
    clauses = [tuple(v * sign for v, sign in zip((1, 2, 3), signs))
               for signs in product((-1, 1), repeat=3)]
    assert check_formula(clauses) == 0
    for i in range(8):
        assert check_formula(clauses[:i] + clauses[i + 1:]) == 1
    print("All 120 local orders and 72 formula/assignment pairs passed.")
