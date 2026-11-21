"""Cross-check the Lie derivative with a Christoffel-symbol Hessian."""
import mpmath as mp
mp.mp.dps = 65
# Three equal-weight tokens in two dimensions, squared scale 9.
x = [mp.mpf(j) for j in (3, 0, 6, 3, -24, 72)]
def kernel(x, i, j):
    return mp.exp(sum(x[2*i+h]*x[2*j+h] for h in (0, 1)))
def metric(x, i):
    return sum(kernel(x, i//2, j) for j in range(3))/9
def energy(x):
    return sum(kernel(x, i, j) for i in range(3) for j in range(3))/18
def deriv(f, u, i, order=1):
    def on_line(t):
        v = list(u)
        v[i] = t
        return f(v)
    return mp.diff(on_line, u[i], order)
# Use analytic ordinary derivatives of E; direct subtraction of its enormous
# constant summand would lose the curvature signal in finite precision.
def gradient(x, k):
    return sum(kernel(x, k//2, j)*x[2*j+k%2] for j in range(3))/9
g0 = metric(x, 0)
h = deriv(lambda u: gradient(u, 0), x, 0)
for k in range(6):
    dg0 = deriv(lambda u: metric(u, 0), x, k)
    christoffel = (2*(k==0)*dg0-dg0)/(2*metric(x, k))
    h -= christoffel*gradient(x, k)
assert h/g0 < -1
print("The equal-mass three-token intrinsic Hessian is negative. Hessian / metric =", mp.nstr(h/g0, 12))
