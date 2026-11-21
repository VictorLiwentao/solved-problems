"""Differentiate the full Gaussian kernel loss independently at high precision."""
import mpmath as mp
mp.mp.dps = 60

def kernel(u, v):
    dot = sum(x*y for x, y in zip(u, v))
    det = abs(u[0]*v[1] - u[1]*v[0])
    return (det + (mp.pi - mp.atan2(det, dot))*dot)/(2*mp.pi)

def loss(t):
    vectors = [(1, t), (-t, 1), (1, 0), (0, 1)]
    signs = [1, 1, -1, -1]
    return sum(sa*sb*kernel(a, b) for a, sa in zip(vectors, signs)
               for b, sb in zip(vectors, signs))/2

for k in (1, 2, 4, 8, 12):
    t = mp.mpf(10)**-k
    h = mp.diff(loss, t, 2)
    bound = 1 - 1/mp.pi
    assert h < bound < 2*h
    exact_difference = (2/mp.pi)*(1-(1+t)/(1+t*t)**2)
    assert abs(h-bound-exact_difference) < mp.mpf("1e-50")
print("The differentiated Gaussian kernel agrees with the curvature formula at all five scales.")
