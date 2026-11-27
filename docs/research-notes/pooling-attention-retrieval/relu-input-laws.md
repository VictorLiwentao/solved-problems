# Which input laws give exactly the Gaussian ReLU population gradient?

Wentao Li · Research note with OpenAI Codex assistance · November 21, 2026

Tian asks in §7.1 how far equation (5), his Gaussian formula for the population gating vector, extends to other distributions. Tsuchida, Roosta and Gallagher subsequently showed that the associated ReLU kernel extends to rotationally invariant laws. There is a necessary and sufficient condition that also covers direction-dependent radii. [Tian, ICML 2017, Theorem 1 and §7.1](https://proceedings.mlr.press/v70/tian17a.html) · [Tsuchida et al., ICML 2018](https://proceedings.mlr.press/v80/tsuchida18a.html)

**Characterization.** For any random $X\in\mathbb R^d$ with finite second moment, define a measure $\nu$ on the unit sphere by
$$
 \nu(B)=\mathbb E[\|X\|^2\,1_{\{X\ne0,\ X/\|X\|\in B\}}].
$$
Let $\sigma$ be uniform probability on the sphere. Then the gating vector $\mathbb E[X\,1_{\{e^\top X>0\}}(w^\top X)_+]$ agrees with Tian’s standard Gaussian formula for every unit $e$ and all $w$ if and only if $\nu=d\sigma$. Two input laws give the same entire bias-free two-neuron ReLU kernel if and only if their measures $\nu$ agree. Atom masses at the origin have zero weight in this criterion.

**Proof.** If $\nu$ agrees, direct polar decomposition gives both conclusions in the forward construction, since the integrands are homogeneous of degree two in the input. For necessity the inner product of the gating vector with $e$ gives the kernel $\mathbb E[(e^\top X)_+(w^\top X)_+]$, so it suffices to show the kernel determines $\nu$.

Suppose a signed finite measure $\mu$ on the sphere integrates every product $(a^\top u)_+(b^\top u)_+$ to zero. Adding or subtracting the equations for the four sign choices of $a,b$ shows that it annihilates both $|a^\top u||b^\top u|$ and $(a^\top u)|b^\top u|$. Averaging the first identity over a uniform $a$ shows $\int |b^\top u|\,d\mu(u)=0$ for every $b$.

Here is an elementary proof of the needed cosine-transform uniqueness. If a finite even signed measure $\xi$ has $\int |b^\top u|\,d\xi(u)=0$ for every $b$, average that identity for $b=G+tz$ with $G\sim N(0,I_d)$. One obtains $\int \psi(tz^\top u)\,d\xi(u)=0$, where $\psi(v)=\mathbb E|N(0,1)+v|$. Every even Taylor coefficient of $\psi$ at zero is nonzero because $\psi(0)>0$ and $\psi''(v)=\sqrt{2/\pi}\exp(-v^2/2)$. Differentiating under the integral on the compact sphere recovers every even moment $\int(z^\top u)^{2j}\,d\xi(u)=0$. Polarization and polynomial approximation on the sphere imply $\xi=0$.

Applying this to the even part of $\mu$ leaves an odd measure. For each coordinate $i$, $u_i\,d\mu$ is now even and has zero cosine transform by the second product identity. It therefore vanishes. Summing $u_i(u_i\,d\mu)$ over $i$ gives $\mu=0$. Take $\mu$ to be the difference of the two angular measures to conclude. For a standard Gaussian the squared radius has mean $d$ and is independent of the uniform direction, giving $d\sigma$.

**Examples and scope.** Take any nonconstant positive bounded density $p$ of integral one relative to $\sigma$, choose a direction $U$ with density $p$ and put $X=\sqrt{d/p(U)}\,U$. This typically gives a non-rotationally-invariant law with exactly the Gaussian gradient. Conversely, covariance $I$ alone is insufficient: in dimension at least two, the uniform law on the $2d$ vectors $\pm\sqrt d\,e_i$ has that covariance but a discrete angular measure. The criterion determines the population squared loss between any pair of positively one-homogeneous networks from the angular measure, since their squared difference is two-homogeneous.

The rotationally invariant sufficiency direction is established in the 2018 paper. The necessity argument uses the classical injectivity of the cosine transform on even measures and is included self-contained. Its status as a previously unstated statistical characterization remains unverified. It is outside the solved catalogue.
