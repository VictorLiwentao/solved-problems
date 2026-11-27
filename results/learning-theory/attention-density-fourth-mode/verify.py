"""Exact enclosure for the fourth Fourier obstruction."""
from fractions import Fraction
from math import factorial


def bessel_term(order, index):
    denominator = 2 ** (2 * index + order) * factorial(index) * factorial(index + order)
    return Fraction(1, denominator)


def bessel_interval(order):
    lower = sum(bessel_term(order, index) for index in range(8))
    return lower, lower + 2 * bessel_term(order, 8)


lower, upper = zip(*(bessel_interval(k) for k in range(5)))
lo = lower[4] * lower[1] ** 2 - 2 * upper[1] * upper[2] * upper[3] + lower[2] ** 3
hi = upper[4] * upper[1] ** 2 - 2 * lower[1] * lower[2] * lower[3] + upper[2] ** 3
assert Fraction(-26, 10**6) < lo <= hi < Fraction(-25, 10**6)
print("Certified -26/10^6 < J < -25/10^6 using rational interval arithmetic.")
