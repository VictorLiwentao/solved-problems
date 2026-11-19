"""Check the binomial formula against direct coarea sequences."""
from collections import Counter
from run_return import distribution


def direct(m, n):
    strides = {1, m//n}
    counts = {d: Counter() for d in strides}
    flags = [i*m//n for i in range(n)]
    def visit(values, hits):
        i = len(values)
        if i == n:
            occupied = set(values)
            for d in strides:
                run = next(r for r in range(1, n+1) if d*r not in occupied)
                counts[d][run, hits] += 1
            return
        for x in range(values[-1] if values else 0, flags[i]+1):
            values.append(x)
            visit(values, hits + (x == flags[i]))
            values.pop()
    visit([], 0)
    return counts


def main():
    checked = 0
    for n in range(1, 8):
        for m in range(n, 3*n+2):
            for d, reference in direct(m, n).items():
                for k in range(1, n+1):
                    answer = distribution(m, n, k, d)
                    assert answer == [reference[k,r] for r in range(n+1)], (m,n,d,k)
                    checked += 1
    print(f"{checked} joint-distribution rows agree with direct enumeration.")
    for d in (1, 2):
        print(f"m=7, n=3, stride={d}", [distribution(7,3,k,d)[1:] for k in (1,2,3)])


if __name__ == "__main__":
    main()
