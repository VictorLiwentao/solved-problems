"""Compare the decision procedure with actual linear-extension counts."""
from functools import lru_cache
from itertools import combinations, permutations, product
from factorization import boundary, gap_witnesses, obstruction


@lru_cache(maxsize=4000)
def count(p, word):
    starts = [0]
    for a in word:
        starts.append(starts[-1] + len(p)-a)
    n = starts[-1]+len(p)
    pred = [0]*n
    ranks = sorted(range(len(p)), key=p.__getitem__)
    for start in starts:
        for i, j in zip(ranks, ranks[1:]):
            pred[start+j] |= 1 << (start+i)
    full = (1<<n)-1
    @lru_cache(None)
    def build(used):
        if used == full:
            return 1
        return sum(build(used | (1<<i)) for i in range(n)
                   if not used & (1<<i) and not pred[i] & ~used)
    ans = build(0)
    build.cache_clear()
    return ans


def main():
    positive = negative = 0
    for k in range(2, 6):
        for p in permutations(range(1, k+1)):
            admissible = []
            for a in range(1, k):
                try:
                    boundary(p, a)
                except ValueError:
                    continue
                admissible.append(a)
            for size in range(1, min(len(admissible), 3)+1):
                for alpha in combinations(admissible, size):
                    for seam in alpha:
                        failure = obstruction(p, seam, alpha)
                        if failure is not None:
                            u, v, _ = failure
                            assert len(u) <= k+1 and len(v) <= k+1
                            assert count(p,u+(seam,)+v) > count(p,u)*count(p,v)
                            negative += 1
                        else:
                            words = [(), *product(alpha,repeat=1), *product(alpha,repeat=2)]
                            for u, v in product(words, repeat=2):
                                assert count(p,u+(seam,)+v) == count(p,u)*count(p,v)
                                positive += 1
    p = (1,2,5,3,4,6)
    assert set(gap_witnesses(p,2,(2,3),True)) == {0,1}
    assert set(gap_witnesses(p,2,(2,3),False)) == {2}
    assert count(p,(3,)) == 3 and count(p,(3,2,3)) == 9
    print(f"{positive} product equalities and {negative} strict obstructions passed, plus the example.")


if __name__ == "__main__":
    main()
