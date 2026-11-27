# A bounded-query counterexample to the full Gaussian leap exponent

Wentao Li · Research note with OpenAI Codex assistance · November 21, 2026

After Proposition 5 of their COLT 2023 paper, Abbe, Boix Adserà and Misiakiewicz conjecture that their Boolean correlational statistical query lower bound with the full leap exponent also holds for Gaussian data. Appendix F.2 uses queries $\phi:\mathbb R^d\to[-1,1]$ and an adversarial additive tolerance $\tau$ for $\mathbb E[\phi(X)Y]$. In Proposition 31 the complexity measure that governs the lower bound is the number of queries divided by $\tau^2$. Their separate Conjecture 2 concerns online SGD. [COLT 2023 paper, Proposition 5 and Appendix F.2](https://proceedings.mlr.press/v195/abbe23a.html)

**Counterexample.** Write $X\sim N(0,I_d)$ and $Y=\mathrm{He}_{2s+1}(w^\top X)$ for an arbitrary unknown unit vector $w$, where $\mathrm{He}_j$ is the probabilists' Hermite polynomial. For any fixed $s\geq2$ this target has leap and isotropic leap both equal to $2s+1$ by Definition 1 of the source. For every fixed desired positive squared error a deterministic bounded-query learner succeeds for **every** $w$ and every admissible sequence of oracle errors, with
$$
      N/\tau^2=O_s(d^{s+2}\log d),
$$
where the implicit constant also depends on the desired error. This is $o(d^{2s+1})$. In particular, leap five already permits $O(d^4\log d)$ instead of the proposed lower bound of order $d^5$. The targets form a whole family of odd-degree links. Independent centered label noise gives the same query responses.

**Proof.** Put $\lambda=d^{-1/2}$, $z=1-2i\lambda$, and $k=2s+1$. Gaussian integration and the Hermite generating function give
$$
 \mathbb E[X_j e^{i\lambda\|X\|^2} e^{t w^\top X-t^2/2}]
 =t w_j z^{-d/2-1}\exp(i\lambda t^2/z).
$$
Indeed the complex Gaussian tilt changes the quadratic precision to $zI$ with positive real part, and differentiating its moment generating function gives the $j$-th first moment. Coefficient extraction at zero gives
$$
 \mathbb E[Y X_j e^{i\lambda\|X\|^2}]
 =c_d w_j,\qquad c_d=(k!/s!)z^{-d/2-1}(i\lambda/z)^s.
$$
For fixed $s$, $|c_d|\asymp_s d^{-s/2}$ since $|z|^{-d/2}=(1+4/d)^{-d/4}$. The phase and magnitude of $c_d$ are known without $w$.

Fix a desired vector error $0<\eta<1/4$. Take $L=B\sqrt{\log(2d)}$ and submit the $d$ real queries
$$
 \phi_j(x)=L^{-1}\operatorname{clip}(x_j,[-L,L])\cos(\lambda\|x\|^2-\arg c_d).
$$
They are bounded by one. Before division by $L$, the clipping bias in the correlation is at most
$$
 \sqrt{k!}\,\big(\mathbb E[X_j^2\,1_{\{|X_j|>L\}}]\big)^{1/2}
 \leq C_k(1+L) e^{-L^2/4}
$$
by Cauchy–Schwarz and a Gaussian tail bound. Choose the constant $B=B(s,\eta)$ large enough that this is at most $\eta|c_d|/(2\sqrt d)$ uniformly in $d\geq2$. Use oracle tolerance $\tau=\eta|c_d|/(2L\sqrt d)$. Multiplication of the response by $L/|c_d|$ then recovers each $w_j$ within $\eta/\sqrt d$. The resulting vector has Euclidean error at most $\eta$, and its normalization $\widehat w$ has error at most $2\eta$. Thus $N=d$ gives the stated complexity.

Finally Hermite orthogonality for correlated Gaussian inputs gives squared prediction error $2k!(1-\langle w,\widehat w\rangle^k)\leq k\,k!\,\|w-\widehat w\|^2$. Choosing $\eta$ sufficiently small reaches any fixed error threshold, including one below the positive constant in the proposed lower bound. Constant normalization of the Hermite polynomial has no effect on the exponent.

**What prior work already supplies.** The radial mechanism has a clear precedent. Damian, Pillaud-Vivien, Lee and Bruna give partial traces of Gaussian Hermite tensors, including a vector estimator in odd degree. Joshi, Koubbi, Misiakiewicz and Srebro express the statistic as a radial polynomial times $X$. For a pure odd Hermite label their statistic can also be clipped and queried one coordinate at a time. In particular the underlying counterexample follows from existing techniques. The bounded oscillatory queries above give a direct proof in the precise 2023 oracle. The published Gaussian half-exponent lower bound and the online-SGD conjecture are compatible with this example. **No first-disproof claim or novelty score.** [Damian et al., COLT 2024, Algorithm 1](https://arxiv.org/abs/2403.05529) · [Joshi et al., NeurIPS 2025, Appendix A.3](https://papers.neurips.cc/paper_files/paper/2025/file/400693b9f90cd47ceae029071950179d-Paper-Conference.pdf)
