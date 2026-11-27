"""Compare direct tree colorings with the full-poset Euler characteristic."""
from functools import cache
from pathlib import Path
from runpy import run_path

posets = run_path(str(Path(__file__).resolve().parent.parent
                      / "multiweighted-partition-polynomials" / "verify.py"))


@cache
def root_colors(labels, k):
    # A leaf has sentinel color zero; its edge never restricts a positive root.
    if labels.bit_count() == 1:
        return (1,) + (0,) * k
    counts = [0] * (k + 1)
    rest = labels & (labels - 1)
    right = rest
    while right:
        left_choices = sum(root_colors(labels ^ right, k))
        right_colors = root_colors(right, k)
        for color in range(1, k + 1):
            counts[color] += left_choices * sum(right_colors[:color])
        right = (right - 1) & rest
    return tuple(counts)


if __name__ == "__main__":
    checks = 0
    for n in range(2, 6):
        for k in range(1, 5):
            admissible = sum(root_colors((1 << n) - 1, k)[:-1])
            ranks, _ = posets["enumerate_poset"](n, k)
            assert admissible == (-1)**(n - 1) * sum(ranks)
            checks += 1
    print(f"{checks} restricted-comb counts agree with direct poset inversion.")
