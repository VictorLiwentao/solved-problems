"""Exhaustive labeled graphs for the Graffiti.pc domination checks (bit masks)."""

from itertools import combinations


def connected_graphs(order):
    edges = list(combinations(range(order), 2))
    for code in range(1 << len(edges)):
        graph = [0] * order
        for i, (u, v) in enumerate(edges):
            if code & (1 << i):
                graph[u] |= 1 << v
                graph[v] |= 1 << u
        seen = 1
        while True:
            grown = seen
            for v, neighbors in enumerate(graph):
                if seen & (1 << v):
                    grown |= neighbors
            if grown == seen:
                break
            seen = grown
        if seen.bit_count() == order:
            yield graph


def independent_masks(graph):
    return [mask for mask in range(1 << len(graph))
            if all(not (mask & (1 << v) and mask & neighbors)
                   for v, neighbors in enumerate(graph))]


def dominates(graph, mask, demand=1):
    return all(mask & (1 << v) or (mask & neighbors).bit_count() >= demand
               for v, neighbors in enumerate(graph))
