"""Test the finite-state padding rule against the primitive island factors."""
from collections import deque
from itertools import combinations, product


def words(length):
    return ("".join(bits) for bits in product("01", repeat=length))


def safe_machine(dictionary):
    blocked = set(dictionary) | {word[::-1] for word in dictionary}
    prefixes = {""} | {word[:i] for word in blocked for i in range(1, len(word))}
    graph = {}
    for state in prefixes:
        graph[state] = {}
        for bit in "01":
            candidate = state + bit
            if not any(candidate.endswith(word) for word in blocked):
                graph[state][bit] = max((p for p in prefixes if candidate.endswith(p)), key=len)
    return graph


def advance(graph, state, string):
    for bit in string:
        if state is None:
            break
        state = graph[state].get(bit)
    return state


def avoider(graph, padding):
    start = advance(graph, "", "0" * padding)
    if start is None:
        return None
    queue = deque([(start, False, "")])
    visited = {(start, False)}
    while queue:
        state, positive, middle = queue.popleft()
        if positive and advance(graph, state, "0" * padding) is not None:
            return "0" * padding + middle + "0" * padding
        for bit, next_state in graph[state].items():
            key = next_state, positive or bit == "1"
            if key not in visited:
                visited.add(key)
                queue.append((*key, middle + bit))
    return None


if __name__ == "__main__":
    options = [word for n in range(1, 4) for word in words(n)]
    checked = 0
    for size in range(4):
        for dictionary in combinations(options, size):
            graph = safe_machine(dictionary)
            bound = len(graph)
            threshold = None
            for b in range(1, bound + 4):
                witness = avoider(graph, b)
                short = [d for d in dictionary if "0" * (b + 1) not in d]
                assert (witness is None) == (avoider(safe_machine(short), b) is None)
                if witness is None and threshold is None:
                    threshold = b
                if witness is not None:
                    assert threshold is None
                    assert all(d not in witness and d[::-1] not in witness for d in dictionary)
            assert threshold is None or threshold <= bound
            checked += 1
    print(f"Padding thresholds and zero-run truncation checked for {checked} dictionaries.")
