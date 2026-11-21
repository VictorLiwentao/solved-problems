"""Exact risk of a centered ramp for a grid of rational radii and widths."""
from fractions import Fraction as F


def risk(radius, width):
    # For a negative example at -x, the maximal ramp prediction occurs at -x+radius.
    # Evenness gives the same integrated loss on the positive half.
    a, b = radius - width, radius + width

    def full_integral(x):
        return x + x**2 / 2

    def ramp_integral(x):
        return (b*x + (b-1)*x**2/2 - x**3/3) / (2*width)

    return F(2, 3) * (full_integral(a) + ramp_integral(b) - ramp_integral(a))


for denominator in range(3, 16):
    r = F(1, denominator)
    optimum = F(2, 3) * (r + r**2/2)
    for shrink in range(2, 12):
        h = r / shrink
        assert risk(r, h) - optimum == h**2 / 9
print("Verified the exact excess h^2/9 over the discontinuous optimum for 130 rational ramps.")
