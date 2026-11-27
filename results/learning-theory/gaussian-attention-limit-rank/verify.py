"""Check the Schur complement derivative and an exact softmax trajectory."""
import numpy as np
from scipy.linalg import expm


def check_schur_derivative():
    random = np.random.default_rng(603)
    for dimension in range(2, 9):
        for rank in range(1, dimension + 1):
            covariance_factor = random.normal(size=(dimension, dimension))
            covariance = covariance_factor @ covariance_factor.T + np.eye(dimension)
            key = random.normal(size=(rank, dimension))
            value = random.normal(size=(dimension, dimension))
            cross = covariance @ key.T
            visible = key @ cross
            gain = np.linalg.solve(visible, cross.T).T
            for weight in [np.eye(rank), 2 * np.linalg.inv(np.eye(rank) + 2 * visible)]:
                forcing = cross @ weight @ cross.T
                velocity = -value @ forcing - forcing @ value.T
                dcross = velocity @ key.T
                conditional_derivative = (velocity - dcross @ gain.T - gain @ dcross.T
                                          + gain @ (key @ dcross) @ gain.T)
                residual = np.linalg.norm(conditional_derivative) / max(1, np.linalg.norm(velocity))
                assert residual < 1e-9


def check_rank_one():
    value = np.array([[1., -1.], [1., 1.]])
    key = np.array([1., 0.])
    fixed = np.diag([0., 1.])
    for time_parameter in np.linspace(0., np.pi / 2, 19):
        z = expm(-time_parameter * value) @ key
        sigma = fixed + np.outer(z, z)
        cross = sigma @ key
        speed = (z @ key) ** 2
        explicit_velocity = -speed * (np.outer(value @ z, z) + np.outer(z, value @ z))
        forcing = np.outer(cross, cross)
        np.testing.assert_allclose(explicit_velocity, -value @ forcing - forcing @ value.T, atol=1e-12)
    np.testing.assert_allclose(sigma, np.diag([0, 1 + np.exp(-np.pi)]), atol=1e-12)


if __name__ == '__main__':
    check_schur_derivative()
    check_rank_one()
    print('Both covariance flows and the nontrivial rank-one limit checked.')
