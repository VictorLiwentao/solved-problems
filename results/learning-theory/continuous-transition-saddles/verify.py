"""Extract the trigonometric Landau coefficient exactly by Laurent convolution."""
from collections import defaultdict
from fractions import Fraction as F

# A key records t-degree and Fourier frequency in q(t)-1.
u = {(1,1):1, (1,-1):1, (2,2):2, (2,-2):2}
power = {(0,0):F(1)}
entropy = defaultdict(F)
for j in range(1,5):
    product = defaultdict(F)
    for (d,k),a in power.items():
        for (e,l), b in u.items():
            if d+e <= 4:
                product[d+e,k+l] += a*b
    power = product
    coeff = F(1) if j == 1 else F((-1)**j, j*(j-1))
    for (d,k),value in power.items():
        if k == 0:
            entropy[d] += coeff*value

assert entropy[2] - 1 == 0
assert entropy[4] - F(3,4)*4 == F(-1,2)
print("The quartic coefficient of entropy minus interaction is exactly -1/2.")
