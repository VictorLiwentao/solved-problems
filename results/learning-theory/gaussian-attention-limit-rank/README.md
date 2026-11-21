# The exact limiting rank in Gaussian attention

Wentao Li · Research draft with OpenAI Codex assistance · November 21, 2026

Castin, Ablin, Carrillo and Peyré study a constant attention head with opposite key and query maps. In their Figure 4 they report a rank bound for convergent Gaussian softmax dynamics with random value matrix $V$, outside the commutation hypothesis of their Proposition 4.3. Figure 11 reports an analogous observation for squared-distance attention. Assume the initial covariance $\Sigma_0$ is positive definite. Write the key Gram matrix as $C=R^\top R$ for a full-row-rank $r\times d$ matrix $R$; redundant rows of the original key map can be removed by using any such factor. [Castin et al., 2025, §4.5 and Appendix D.2](https://arxiv.org/abs/2501.18322)

[Proof (PDF)](gaussian-attention-limit-rank.pdf) · [LaTeX source](gaussian-attention-limit-rank.tex) · [BibTeX](citation.bib) · [Matrix checks](verify.py)

**Theorem.** For either head, if $V$ has no eigenvalue on the imaginary axis, every bounded maximal covariance trajectory is global and converges to a covariance with image exactly $\ker R$ and rank $d-r$. Every other trajectory escapes to infinity in norm at its maximal forward endpoint. If every eigenvalue of $V$ has positive real part, all trajectories converge. For every real $V$, including exceptional matrices, a finite limit has rank at least $d-r$. Thus when $r=\lfloor d/2\rfloor$ and $V$ has a density, every convergent run almost surely has rank exactly $\lceil d/2\rceil$.

**The conserved covariance.** Put $M=\Sigma R^\top$, $S=R\Sigma R^\top$. Both models obey
$$
 \dot\Sigma=-VB-BV^\top,\qquad B=M E M^\top,
$$
with $E=I_r$ for softmax and $E=2(I_r+2S)^{-1}$ for squared-distance attention. For the latter formula use the affine velocity in Lemma 4.12 of the source and $(I+2R^\top R\Sigma)^{-1}R^\top=R^\top(I+2S)^{-1}$. On finite intervals $\dot\Sigma=A_t\Sigma+\Sigma A_t^\top$ with $A_t=-VME R$. Congruence by the invertible fundamental solution preserves positive definiteness at every finite time of existence.

Let $H=\Sigma-MS^{-1}M^\top$ and $P=I-MS^{-1}R$. Differentiating gives $\dot H=P\dot\Sigma P^\top$. Since $PM=0$, both terms in this derivative vanish. This is the Gaussian conditional covariance given the visible coordinates $RX$. In particular,
$$
 \Sigma(t)\succeq H_0,\quad RH_0=0,\quad \operatorname{rank}H_0=d-r .
$$
For the rank identity, factor $H_0$ as $\Sigma_0^{1/2}(I-\Pi)\Sigma_0^{1/2}$, where $\Pi$ is orthogonal projection onto the row space of $R\Sigma_0^{1/2}$. These formulas give the lower bound at every finite limit, irrespective of $V$.

**Why bounded trajectories converge.** For a hyperbolic real matrix $V$ there is a symmetric matrix $J$ with $Q=V^\top J+JV\succ0$. To see this, split $V$ by real similarity into blocks of positive and negative real spectrum (here the sign refers to the real parts). On a positive block take the integral of $e^{-tV^\top}e^{-tV}$ over $t\geq0$. On a negative block take minus the integral of $e^{tV^\top}e^{tV}$. The Lyapunov sum equals the identity on each block; congruence back to the original coordinates preserves positive definiteness of $Q$. When all eigenvalues have positive real parts, $J$ itself is positive definite.

Along the flow,
$$
 (\operatorname{tr}J\Sigma)'=-\operatorname{tr}(QB)\leq-\lambda_{\min}(Q)\operatorname{tr}B,\qquad
 \|\dot\Sigma\|_F\leq2\|V\|_{\rm op}\operatorname{tr}B .
$$
If there is a bounded sequence of covariances approaching the maximal endpoint, the nonincreasing function $\operatorname{tr}(J\Sigma)$ is bounded below. Integrating proves finite total variation of $\Sigma$ and hence a finite limit. At a finite endpoint the matrix vector field extends smoothly to a neighborhood of that positive semidefinite limit, since $I+2R\Sigma R^\top$ stays invertible. The congruence equation with bounded coefficients up to this endpoint keeps $\Sigma$ positive definite there. This contradicts maximality. At an infinite endpoint continuity and integrability imply $\operatorname{tr}B_*=0$, so $\Sigma_*R^\top=0$. The upper image bound combines with the conserved $H_0$ to give the asserted image and rank. If there is no bounded subsequence, the norm tends to infinity. For $J\succ0$, the initial value of $\operatorname{tr}(J\Sigma)$ bounds $\operatorname{tr}\Sigma$ throughout, proving universal convergence.

Hyperbolicity holds almost everywhere. For instance, matrices with an imaginary-axis eigenvalue have a pair of eigenvalues summing to zero, counting zero twice if necessary. The determinant of the linear operation $X\mapsto VX+XV^\top$ on all matrices then vanishes. This determinant is a polynomial in the entries of $V$ and is nonzero at $V=I$.

**Sharpness of the spectral hypothesis.** For every $V$ with an imaginary-axis eigenvalue there is a stationary positive definite initial covariance for a nonzero key Gram matrix. For a zero eigenvalue take a real null vector as a one-column matrix $U$. For a nonzero purely imaginary eigenvalue take the real and imaginary parts of a complex eigenvector as the columns of $U$. Then $VU=U\Omega$ with $\Omega$ skew-symmetric. Choose another matrix $W$ completing these columns to a real basis, and let $R$ be the row block of $[U\,W]^{-1}$ satisfying $RU=I$, $RW=0$. For $\Sigma_0=UU^\top+WW^\top$, one has $M=U$, $S=I$ and $B$ proportional to $UU^\top$. Hence $\dot\Sigma=0$ for either model.

If $V$ has an eigenvalue of real part $a<0$, use the same real eigenvector or invariant real plane with $VU=U(aI+\Omega)$. For softmax, $\Sigma(t)=x(t)UU^\top+WW^\top$ with $x(0)=1$ satisfies $x'=-2ax^2$. It blows up at $-1/(2a)$. For squared-distance attention the equation is $x'=-4ax^2/(1+2x)$, giving unbounded growth as $t\to\infty$. Thus strict positivity of all eigenvalue real parts is necessary and sufficient for convergence to the predicted rank for **every** allowed key and initialization.

**A rank-one formula.** The residual covariance need not be the entire limit. For a softmax head $C=uu^\top$, let $a=u^\top\Sigma_0 u$, $z_0=\Sigma_0u$ and $H_0=\Sigma_0-z_0z_0^\top/a$. Set $z(s)=e^{-sV}z_0$ and $h(s)=u^\top z(s)$. Then
$$
 \Sigma(t)=H_0+z(s)z(s)^\top/a,\qquad ds/dt=h(s)^2/a,\quad s(0)=0 .
$$
Indeed $\Sigma u=z(s)h(s)/a$, so differentiation gives the original ODE and initial data. Scalar separation fixes the time change up to the first zero of $h$, which takes infinite physical time to reach. If $h$ has no positive zero the maximal physical time is $\int_0^\infty a/h(s)^2\,ds$. For example, take $u=e_1$, $\Sigma_0=I_2$ and $V=\left(\begin{smallmatrix}1&-1\\1&1\end{smallmatrix}\right)$. Here $h(s)=e^{-s}\cos s$ first vanishes at $\pi/2$; the limiting variance on the invisible second coordinate is $1+e^{-\pi}$. Thus even a positive-stable value matrix can leave strictly more variance than the conserved conditional covariance.

**Prior work and scope.** Castin et al. give the covariance evolution and a commuting solution. Alcalde, Ji and Zuazua study finite-time rank preservation, controllability with time-varying coefficients, and convergence or blow-up under other sign and definiteness hypotheses. The theorem here uses singular keys and identifies the surviving subspace for a constant head. It makes no claim about a trained transformer's attention on discrete text. Provisional significance **60/100** if correct and new. Independent proof and priority review are pending. [Alcalde, Ji and Zuazua, 2026](https://dcn.nat.fau.eu/wp-content/uploads/GaussianTransformer-manuscript.pdf)
