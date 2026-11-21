"""Verify the finite network sequence and its exact loss on all 30 samples."""
from fractions import Fraction

def relu(value):
    return max(0, value)

samples = [(x, Fraction(k, 4)) for x in range(6) for k in range(5)]
for exponent in range(1, 11):
    epsilon = Fraction(1, 2**exponent)
    squared_error = 0
    for x, y in samples:
        h = relu(x + epsilon * y)
        output = relu(h) / epsilon + (1 - 1 / epsilon) * relu(h - epsilon)
        target = y if x == 0 else x + 1
        error = output - target
        assert error == (0 if x == 0 else epsilon * (y - 1))
        squared_error += error**2
    assert squared_error == Fraction(75, 8) * epsilon**2
print("Checked all 30 rational samples at ten scales. Total squared error = (75/8) epsilon^2.")
