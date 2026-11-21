"""Check the unisolvent integer simplices in the finite-constraint construction."""
from itertools import product
from math import comb, prod
from fractions import Fraction

for dim in range(1,5):
    for degree in range(1,5):
        points = sorted((p for p in product(range(degree+1),repeat=dim) if sum(p)<=degree),
                        key=lambda p:(sum(p),p))
        assert len(points)==comb(dim+degree,degree)
        for i, point in enumerate(points):
            for j, exponent in enumerate(points[i:],i):
                value = prod(comb(t,n) if n<=t else 0 for t,n in zip(point,exponent))
                assert value == int(i==j)
# Two-variable degree-two determinant, recovered away from the integer simplex.
def det(u,v):
    return (2*u-v)*(u+3*v)-(u+v)*(3*u-2*v)
p00,p10,p01,p20,p11,p02 = [det(*p) for p in [(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)]]
u,v = Fraction(-3,2),Fraction(7,3)
interpolated = (p00+(p10-p00)*u+(p01-p00)*v+(p11-p10-p01+p00)*u*v
                +(p20-2*p10+p00)*u*(u-1)/2+(p02-2*p01+p00)*v*(v-1)/2)
assert interpolated==det(u,v)
print("Verified 16 triangular interpolation systems and an exact off-grid determinantal identity.")
