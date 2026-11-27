"""Check the two graph parameters from the Li–Sun figure by enumeration."""
from fractions import Fraction
from itertools import combinations


def edges(labels):
    return [(f"A{i}", f"B{j}") for i, j in labels.split()]


QUALIFIED = edges("11 21 22 31 32 33 43 44")
UNQUALIFIED = edges("12 13 23 24 34 41")


def adjacency(edge_set):
    neighbors = {}
    for a, b in edge_set:
        neighbors.setdefault(a, set()).add(b)
        neighbors.setdefault(b, set()).add(a)
    return neighbors


def simple_paths(graph, path, end):
    if path[-1] == end:
        yield path
        return
    for neighbor in graph[path[-1]]:
        if neighbor not in path:
            yield from simple_paths(graph, path + (neighbor,), end)


def connects_and_covers(cover, path):
    graph = adjacency(cover)
    if not set(path) <= graph.keys():
        return False
    seen = {path[0]}
    frontier = [path[0]]
    while frontier:
        for vertex in graph[frontier.pop()] - seen:
            seen.add(vertex)
            frontier.append(vertex)
    return seen == graph.keys()


def main():
    graph = adjacency(UNQUALIFIED)
    distances, cover_sizes = [], []
    for edge in QUALIFIED:
        for path in simple_paths(graph, (edge[0],), edge[1]):
            distances.append(len(path) - 1)
            for size in range(1, len(QUALIFIED) + 1):
                if any(edge in cover and connects_and_covers(cover, path)
                       for cover in combinations(QUALIFIED, size)):
                    cover_sizes.append(size)
                    break
    d, rho = min(distances), min(cover_sizes)
    assert (d, rho) == (3, 5)
    graph_bound = Fraction((rho - 1) * (d - 1), rho * d - 1)
    communication_capacity = Fraction(7, 18)  # Li and Sun, Theorem 3
    noise_bound = 1 / (1 / (2 * communication_capacity) + Fraction(1, d - 1))
    assert (graph_bound, noise_bound) == (Fraction(4, 7), Fraction(14, 25))
    assert graph_bound - noise_bound == Fraction(2, 175)
    print("Verified d=3, rho=5 and a strict gap of 2/175 on the published graph.")


if __name__ == "__main__":
    main()
