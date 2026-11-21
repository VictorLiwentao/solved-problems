"""Check the output-bias construction on three scalar-chain shapes using exact values."""
from fractions import Fraction

def relu(x):
    return max(0, x)

for length in (3, 4, 8):
    for shape in ("constant", "ray", "clipped"):
        seen_biases = set()
        for t in (Fraction(1, 8), Fraction(5, 3), Fraction(8)):
            output_bias = (2 - 3 * t, -4 + t)
            seen_biases.add(output_bias)
            for i in range(-30, 31):
                x = Fraction(i, 7)
                inner = relu(x - 1)
                if shape == "constant":
                    feature = 0
                elif shape == "ray":
                    feature = relu(inner)
                else:
                    feature = relu(2 - inner)
                hidden = feature
                for _ in range(length - 3):
                    hidden = relu(hidden)
                hidden = relu(hidden + t)
                result = (3 * hidden + output_bias[0], -hidden + output_bias[1])
                assert result == (3 * feature + 2, -feature - 4)
        assert len(seen_biases) == 3
print("Exact outputs agree for constant, ray and clipped shapes at three depths with distinct output biases.")
