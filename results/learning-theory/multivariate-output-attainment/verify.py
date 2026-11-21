"""Exact checks of the weighted projection and the endpoint identity."""
from fractions import Fraction as F
for weight in range(1, 15):
    for numerator in range(18):
        t = F(numerator, 17)
        gap = 2*(2-t)**2 - (1+(1-t)**2/weight+t*t)
        assert gap == (1-t)*(6+(1-F(1,weight))*(1-t))
        assert (gap == 0) == (t == 1)
        assert gap >= 0
    assert F(-2*2-2, 4) == F(-3,2)
print("Weighted endpoint and strict-gap identities checked on 252 rational inputs.")
