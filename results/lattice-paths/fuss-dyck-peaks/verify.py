"""Compare the formula with a direct dynamic program on lattice paths."""
from collections import Counter
from math import comb, gcd


def path_counts(north, east):
    # State tracks the last vertical run, capped at two, and both pattern counts.
    states = {(0, 0): Counter({(0, 0, 0): 1})}
    for diagonal in range(north+east):
        for y in range(max(0, diagonal-east), min(north, diagonal)+1):
            x = diagonal-y
            for (run, peaks, doubles), count in states.pop((x, y), {}).items():
                if y < north:
                    dest = states.setdefault((x, y+1), Counter())
                    dest[min(2, run+1), peaks, doubles] += count
                if x < east and east*y >= north*(x+1):
                    dest = states.setdefault((x+1, y), Counter())
                    dest[0, peaks+(run>0), doubles+(run==2)] += count
    return {(k, j): v for (_, k, j), v in states[east, north].items()}


def formula(north, slots):
    out = {}
    for k in range(1, min(north, slots)+1):
        s = north-k
        for j in range(0 if s == 0 else 1, min(k, s)+1):
            choices = 1 if not s else comb(k, j)*comb(s-1, j-1)
            number, rem = divmod(comb(slots, k)*choices, slots)
            assert rem == 0
            out[k, j] = number
    return out


def main():
    cases = 0
    for n in range(1, 11):
        for m in range(1, 8):
            assert path_counts(n, m*n) == formula(n, m*n+1), (n, m)
            cases += 1
    for a in range(1, 15):
        for b in range(1, 21):
            if gcd(a, b) == 1:
                assert path_counts(a, b) == formula(a, b), (a, b)
                cases += 1
    print(f"{cases} full coefficient distributions agree.")


if __name__ == "__main__":
    main()
