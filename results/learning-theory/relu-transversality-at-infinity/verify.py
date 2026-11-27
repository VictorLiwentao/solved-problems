"""Exact gate and transversality calculations on the escaping vertex."""
from fractions import Fraction

def gate_values(x, y, e):
    a, b = max(0, x), max(0, y)
    p, s = a + e*b - 1, b+1
    return p, s, max(0,p) + e/(1+e)*max(0,s) - 1

for k in range(1, 33):
    e = Fraction(1, k)
    p, s, q = gate_values(0, 1/e, e)
    assert p == q == 0 and s == 1+1/e
    assert gate_values(0, 1/e - Fraction(1,2), e)[0] < 0
    assert gate_values(0, 1/e + Fraction(1,2), e)[0] > 0
    assert gate_values(0, 1/e, Fraction(0))[2] == -1
for y in range(-3,4):
    assert gate_values(2, y, Fraction(0))[2] == 0
print("Checked 32 exact escaping vertices and the reference threshold.")
