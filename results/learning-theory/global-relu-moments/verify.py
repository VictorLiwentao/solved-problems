"""Check the Gaussian face recurrence for a rotated affine ReLU in two dimensions."""
import mpmath as m

m.mp.dps = 45
root_two_pi = m.sqrt(2*m.pi)
# The gate normal is (3,4)/5, the transform direction is (-1,2).
normal_component = m.mpf(1)
tangent_component = m.mpf(2)
# In this orthonormal frame, the integer direction has components 1 and 2.
def density(x):
    return m.exp(-x*x/2)/root_two_pi

for b in (m.mpf("-0.4"), m.mpf("1.2")):
    for t in (m.mpf("-0.2"), m.mpf("0"), m.mpf("0.3")):
        def moment(u, linear):
            inner = m.quad(lambda s: density(s)*m.exp(u*normal_component*s)*
                           ((s-b) if linear else 1), [b, m.inf])
            return inner*m.exp((u*tangent_component)**2/2)
        face = density(b)*m.exp(t*normal_component*b+(t*tangent_component)**2/2)
        full = moment(t, False)
        hinge = moment(t, True)
        first = m.diff(lambda u: moment(u, False), t)
        second = m.diff(lambda u: moment(u, True), t)
        norm_squared = normal_component**2 + tangent_component**2
        assert abs(first-(t*norm_squared*full+normal_component*face)) < m.mpf("1e-35")
        assert abs(second-(t*norm_squared*hinge+normal_component*full)) < m.mpf("1e-35")
print("The Gaussian face recurrence matches direct quadrature and derivatives at six threshold/tilt pairs.")
