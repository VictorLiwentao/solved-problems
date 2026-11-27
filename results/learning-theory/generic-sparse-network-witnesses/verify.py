"""Check the two-dimensional LU boundary example and its deterministic parabola sample."""
from fractions import Fraction
from itertools import combinations

def multiply(left, right):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*right)] for row in left]

for k in range(1, 10):
    e = Fraction(1, 2**k)
    lower = [[1, 0], [1/e, 1]]
    upper = [[e, 1], [0, -1/e]]
    assert multiply(lower, upper) == [[e, 1], [1, 0]]

# Two first-layer hyperplanes meet (t,t^2) at most four times in total,
# omitting identically zero polynomials, so there are at most five intervals.
# Any fixed affine formula agreeing with the swap on three of these points
# has linear part equal to the swap, which has no 2-by-2 LU factorization.
points = [(i, i**2) for i in range(11)]
for (a,b), (c,d), (e,f) in combinations(points, 3):
    assert (c-a)*(f-b) != (e-a)*(d-b)
assert len(points) > 2 * (1 + 2 * 2)
print("Verified the LU limiting family at nine scales and all 165 affine-independence triples on the parabola.")
