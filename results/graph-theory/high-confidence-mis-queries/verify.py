"""Check the common answers and the Harris estimate by exact enumeration."""
from fractions import Fraction
from itertools import combinations


def subsets(values):
    values = tuple(values)
    for k in range(len(values) + 1):
        yield from (frozenset(items) for items in combinations(values, k))


def is_maximal(answer, query, edges):
    if any(edge <= answer for edge in edges):
        return False
    return all(any(frozenset((x, y)) in edges for y in answer) for x in query - answer)


def main():
    vertices = frozenset(range(5))
    cases = 0
    correlations = 0
    for pair in combinations(vertices, 2):
        e = frozenset(pair)
        others = vertices - e
        blockers = list(subsets(others))
        for blocked in blockers:
            clique = e | blocked
            complete = {frozenset(edge) for edge in combinations(clique, 2)}
            for query in subsets(vertices):
                answers = []
                for has_edge in (False, True):
                    answer = set(query - clique)
                    if query & blocked:
                        answer.add(min(query & blocked))
                    elif has_edge and query & e:
                        answer.add(min(query & e))
                    else:
                        answer.update(query & e)
                    assert is_maximal(answer, query, complete if has_edge else complete - {e})
                    answers.append(answer)
                assert (answers[0] != answers[1]) == (e <= query and not query & blocked)
                cases += 1
        extensions = [v for v in subsets(others) if v]
        for schedule in subsets(extensions):
            actual = Fraction(sum(all(b & q for q in schedule) for b in blockers), len(blockers))
            bound = Fraction(1)
            for q in schedule:
                bound *= 1 - Fraction(1, 2 ** len(q))
            assert actual >= bound
            correlations += 1
    print(f"Checked {cases} graph-pair queries and {correlations} exact Harris bounds.")


if __name__ == "__main__":
    main()
