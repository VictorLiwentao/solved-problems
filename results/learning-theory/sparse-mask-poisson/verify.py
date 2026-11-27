"""Check the nine-example obstruction on rational inputs and the local LU sequence."""
from fractions import Fraction as F
from itertools import combinations

points = [(F(i,10), F(i,10)**2) for i in range(1,10)]
for (x,y),(u,v),(s,t) in combinations(points,3):
    assert (u-x)*(t-y) != (s-x)*(v-y)
for t in (2,8,32,128):
    t = F(t)
    block = [[t,F(1)],[F(1),1/t]]
    assert block[0][0]*block[1][1] == block[0][1]*block[1][0]
    for x,y in points:
        # Both preactivations are positive, with offset one. Remove output biases explicitly.
        first = max(F(0), t*x+y+1)
        second = max(F(0), x+1)
        out = first-t*second+t-1, (first-1)/t
        assert out == (y, x+y/t)
print("All 84 triples of the nine inputs are affinely independent; the rational networks approach the target.")
