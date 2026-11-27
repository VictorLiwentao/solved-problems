"""Check the distance separation and the join-count identity on small graphs."""
from collections import Counter, deque
from itertools import combinations, product

def edges(n, predicate):
    return {pair for pair in combinations(range(n), 2) if predicate(*pair)}

def distances(n, graph, root):
    dist = {root: 0}
    queue = deque([root])
    while queue:
        u = queue.popleft()
        for v in range(n):
            if tuple(sorted((u,v))) in graph and v not in dist:
                queue.append(v)
                dist[v] = dist[u] + 1
    return tuple(sorted(Counter(dist.values()).items()))

def hom(vertices, pattern, n, graph):
    count = 0
    for images in product(range(n), repeat=len(vertices)):
        mapping = dict(zip(vertices, images))
        count += all(tuple(sorted((mapping[a],mapping[b]))) in graph for a,b in pattern)
    return count

cube = edges(8, lambda a,b: (a ^ b).bit_count() == 1)
ladder = edges(8, lambda a,b: b-a in (1,4,7))
for v in range(8):
    assert distances(8,cube,v) == ((0,1),(1,3),(2,3),(3,1))
    assert distances(8,ladder,v) == ((0,1),(1,3),(2,4))

host = {(0,1),(1,2)}
for pattern in ({(0,1),(1,2)}, {(0,1),(1,2),(0,2)}):
    vertices = set(range(3))
    for t in range(5):
        complete = edges(t, lambda a,b: True)
        joined = edges(3+t, lambda a,b: (a,b) in host or b >= 3)
        total = 0
        for size in range(4):
            for subset in combinations(range(3),size):
                inside = set(subset)
                outside = vertices - inside
                left = {e for e in pattern if set(e) <= inside}
                right = {e for e in pattern if set(e) <= outside}
                total += hom(sorted(inside),left,t,complete) * hom(sorted(outside),right,3,host)
        assert total == hom(range(3),pattern,3+t,joined)
print("Checked all 16 distance profiles and ten join identities against enumerated homomorphisms.")
