"""Finite checks for the code windows, tuple domains, and graph encoding."""

from collections import deque
from itertools import product
from math import isqrt


def decode(value):
    if value < 2:
        return None
    square = isqrt(value) ** 2
    base = square
    depth = 0
    while base > 1 and isqrt(base) ** 2 == base:
        base = isqrt(base)
        depth += 1
    n = isqrt(base) + 1
    if depth >= 2 and base == n * (n - 1) and value - square <= n:
        return depth, n
    return None


def check_windows():
    count = 0
    for depth, n in product(range(2, 7), range(2, 26)):
        start = (n * (n - 1)) ** (2**depth)
        for j in range(n + 1):
            assert decode(start + j) == (depth, n)
            count += 1
        assert decode(start - 1) is None
        assert decode(start + n + 1) is None
        for scale, singleton in product((1, 2, 5, 127), (0, 1)):
            size = scale * start + singleton * n
            assert decode(size // scale) == (depth, n)
    return count


def check_domains():
    for n, pairs, scale, keep_singleton in product(
        range(1, 5), (1, 2), (1, 2, 3), (False, True)
    ):
        tags = (scale - 1).bit_length()
        size = 0
        for row in product(range(n), repeat=2 * pairs + tags):
            if keep_singleton and len(set(row)) == 1:
                size += 1
                continue
            if any(row[2 * i] == row[2 * i + 1] for i in range(pairs)):
                continue
            tail = row[2 * pairs :]
            if all(value in row[:2] for value in tail):
                code = sum((value == row[1]) << i for i, value in enumerate(tail))
                size += code < scale
        assert size == scale * (n * (n - 1)) ** pairs + keep_singleton * n


RING = 18
ARM = 20
PORTS = (2, 4, 6, 8, 10)
CELL_SIZE = RING + ARM * len(PORTS) + 7 + 1


def encoded_grid(width, height, tail):
    graph = []
    cycles = []
    cells = {}

    def vertex():
        graph.append(set())
        return len(graph) - 1

    def edge(u, v):
        assert u != v and u not in graph[v]
        graph[u].add(v)
        graph[v].add(u)

    def arm(start, length):
        path = [start]
        for _ in range(length):
            end = vertex()
            edge(path[-1], end)
            path.append(end)
        return path

    def cell(key, kind):
        ring = [vertex() for _ in range(RING)]
        for i, u in enumerate(ring):
            edge(u, ring[(i + 1) % RING])
        cycles.append(ring)
        tree = arm(ring[0], 6)
        arm(tree[2 + kind], 1)
        arm(ring[1], 1)
        cells[key] = [arm(ring[p], ARM)[-1] for p in PORTS]

    for x, y in product(range(width), range(height)):
        cell((x, y), 0)
        if x:
            edge(cells[x, y][3], cells[x - 1, y][1])
        if y:
            edge(cells[x, y][2], cells[x, y - 1][0])
        if x == 0:
            cell((-1, y), 1)
            edge(cells[x, y][4], cells[-1, y][0])
    arm(cycles[0][12], tail)
    assert len(graph) == CELL_SIZE * (width * height + height) + tail
    return graph, cycles


def check_graph(width, height, tail):
    graph, rings = encoded_grid(width, height, tail)
    assert all(1 <= len(nbrs) <= 3 for nbrs in graph)
    colors = {0: 0}
    pending = deque([0])
    while pending:
        u = pending.popleft()
        for v in graph[u]:
            if v in colors:
                assert colors[u] != colors[v]
            else:
                colors[v] = 1 - colors[u]
                pending.append(v)
    assert len(colors) == len(graph)

    # An edge belongs to a cycle of length <= RING exactly when its ends
    # have an alternative path of length <= RING-1.
    expected = {
        tuple(sorted((u, ring[(i + 1) % RING])))
        for ring in rings for i, u in enumerate(ring)
    }
    found = set()
    for u, neighbors in enumerate(graph):
        for v in neighbors:
            if u >= v:
                continue
            seen = {u}
            todo = deque([(u, 0)])
            while todo:
                w, distance = todo.popleft()
                if w == v:
                    assert distance == RING - 1
                    found.add((u, v))
                    break
                if distance < RING - 1:
                    for z in graph[w]:
                        if z not in seen and (w, z) != (u, v):
                            seen.add(z)
                            todo.append((z, distance + 1))
    assert found == expected


if __name__ == "__main__":
    count = check_windows()
    check_domains()
    for width, height, tail in ((1, 1, 0), (2, 2, 1), (2, 3, CELL_SIZE - 1)):
        check_graph(width, height, tail)
    print(f"{count} decoded window entries, 48 tuple domains, three graph encodings.")
