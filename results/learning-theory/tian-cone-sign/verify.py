"""Compare the cone formula and mixed stationary branches with Tian's original gating vector."""
import mpmath as mp

mp.mp.dps = 65
pi = mp.pi


def direction(angle):
    return mp.matrix([mp.cos(angle), mp.sin(angle)])


def angle_between(a, b):
    return abs(mp.atan2(mp.sin(a - b), mp.cos(a - b)))


def h(angle):
    t = angle_between(angle, 0)
    return mp.sin(t) + (pi - t) * mp.cos(t)


def projection(theta, beta, length=1):
    """Unnormalized expected gated vector, Tian equation (5)."""
    t = angle_between(theta, beta)
    return length * ((pi - t) * direction(beta) + mp.sin(t) * direction(theta))


def residual(b, x):
    matrix = mp.matrix([[pi, h(b)], [h(b), pi]])
    lengths = mp.lu_solve(matrix, mp.matrix([h(x), h(x - b)]))
    diff = projection(0, x) - projection(0, 0, lengths[0]) - projection(0, b, lengths[1])
    return mp.fdot(diff, direction(b))


def lengths_at(b, x, y, rho, rotation):
    target = mp.matrix([h(x - rotation) + rho * h(y - rotation),
                        h(x - b - rotation) + rho * h(y - b - rotation)])
    normal = mp.matrix([[pi, h(b)], [h(b), pi]])
    return mp.lu_solve(normal, target), target


def verify_opening(b):
    for left, right, sign in [(0, b, 1), (b, pi, -1),
                              (pi, pi + b, -1), (pi + b, 2 * pi, -1)]:
        for i in range(1, 8):
            assert sign * residual(b, left + i * (right - left) / 8) > 0

    def ratio(z):
        return residual(b, z) / residual(b, b - z)

    midpoint = b / 2
    x = midpoint + min(b, pi - b) / 100000
    y = mp.findroot(lambda z: ratio(z) - ratio(x), (pi + midpoint, pi + midpoint + (x - midpoint)))
    assert abs(y - x - pi) > abs(x - midpoint) / 2
    rho = -residual(b, x) / residual(b, y)
    lengths, _ = lengths_at(b, x, y, rho, 0)
    assert min(rho, *lengths) > 0
    for angle in [0, b]:
        grad = (projection(angle, 0, lengths[0]) + projection(angle, b, lengths[1])
                - projection(angle, x) - projection(angle, y, rho))
        assert mp.norm(grad) < mp.mpf("1e-48")

    def profiled_loss(rotation):
        radii, target = lengths_at(b, x, y, rho, rotation)
        return -(radii.T * target)[0] / 2  # Up to a constant and positive scaling.

    assert mp.diff(profiled_loss, 0, 2) < 0


if __name__ == "__main__":
    for b in [pi / 32, pi / 6, pi / 2, 2 * pi / 3, 31 * pi / 32]:
        verify_opening(b)
    print("Gating signs, noncollinear critical points and negative curvature checked at five openings.")
