# Which sparse retrieval tasks attain the worst margin?

Wentao Li · Research draft with OpenAI Codex assistance · November 21, 2026

A document is a unit vector $v_i$ and a query for a subset $S$ is a unit vector $u_S$. The zero-threshold margin $m$ requires $\langle u_S,v_i\rangle\geq m$ inside $S$ and $\langle u_S,v_i\rangle\leq-m$ outside. Let $m(\mathcal F)$ be the optimal margin in arbitrary dimension for a nonempty family $\mathcal F$ of $k$-subsets of $[n]$. Bangachev, Bresler, Kogan and Polyanskiy pose the dimension-dependent problem for arbitrary incidence matrices (Problem 1), prove a compression theorem for approximate optimality, and give a spectral upper certificate for the complete $k$-uniform family in Appendix D. That certificate is a starting point here. [Original paper, 2026](https://arxiv.org/abs/2605.23556) · [Earlier margin-complexity theory, Kallweit and Simon, 2011](https://proceedings.mlr.press/v19/kallweit11a.html)

**Theorem.** For $1\leq k<n$, put
$$
 m_0=\frac{n}{2\sqrt{k(n-k)(n-1)}+|n-2k|}.
$$
Every $k$-uniform family has margin at least $m_0$. The full family attains equality. When $2k\ne n$, a family attains equality **if and only if** it supports a probability distribution under which every document has inclusion probability $k/n$ and every distinct pair has joint inclusion probability $k(k-1)/(n(n-1))$. This is a weighted block design, allowing zero mass on unused queries. Every optimal embedding for such an extremal family has the same document Gram matrix and needs document span of dimension $n$. For balanced queries $2k=n$, equality holds exactly when the family enlarged by its complements supports such a design. The least dimension for exact optimality of any balanced extremal family is $n-1$. These statements concern exact attainment. [Bangachev et al., Theorem 1.4, for near-optimality](https://arxiv.org/abs/2605.23556)

**Certificate.** By complementation take $k\leq n/2$, and initially $n>2$. Set $\delta=-m_0$ and
$$
 \alpha=\frac{1+\delta}{2k},\qquad \beta=\frac{1-\delta}{2(n-k)},\qquad s=\alpha+\beta.
$$
Both weights are positive. Let $y_S=2\,1_S-\mathbf 1$ and $w_S=s\,1_S-\beta\mathbf1$. Then $\sum_iw_{Si}=\delta$, $w_S^\top y_S=1$, and
$$
 \delta^2=\frac{k(n-k)}{n-1}s^2 .
$$
For a uniform random $k$-subset, or any distribution with the two stated inclusion probabilities, $\mathbb E w_Sw_S^\top=(\delta^2/n)I$. Indeed, its eigenvalue on constants is $\delta^2/n$, and on the orthogonal complement the hypergeometric covariance gives $s^2k(n-k)/(n(n-1))$. These agree by the displayed identity.

For any unit-vector representation on the support of that distribution, with document matrix $D=[v_1\ \cdots\ v_n]$,
$$
 m\leq\mathbb E\langle u_S,Dw_S\rangle
 \leq\mathbb E\|Dw_S\|\leq\sqrt{\mathbb E\|Dw_S\|^2}=m_0.
$$
The last equality uses $\operatorname{tr}(D^\top D)=n$. This is the two-weight spectral bound in the original paper with the exact constant retained.

**An attaining Gram matrix.** Let $G$ have eigenvalues $\lambda_\perp=2m_0^2/s$ on the orthogonal complement of the constant vectors and $\lambda_1=m_0^2(2k-n)/\delta$ on constants. Then $Gw_S=m_0^2y_S$ for every $S$ by decomposing the two vectors into their mean and centered parts. Both eigenvalues are nonnegative. Moreover $w_S^\top Gw_S=m_0^2$; averaging over all subsets shows $\operatorname{tr}G=n$. By permutation invariance its diagonal is one. Factor $G=D^\top D$ and put $u_S=Dw_S/m_0$. These are unit vectors and their document inner products equal $m_0y_S$. They realize the claimed lower bound simultaneously for every possible query.

**Rigidity.** At margin $m_0$ on a design, all three inequalities in the certificate are equalities. Every query in the positive-mass support satisfies $\|Dw_S\|=m_0$, $Dw_S=m_0u_S$, and every single signed logit is tight since all coordinate weights are strictly positive in magnitude. Hence $(D^\top D)w_S=m_0^2y_S$. The vectors $w_S$ on that support span $\mathbb R^n$ by their positive definite second moment. Thus $D^\top D=G$. Its rank is $n$ if $2k<n$, and $n-1$ if $2k=n$. The complementary unbalanced case follows by negating query vectors. For $n=2,k=1$, antipodal documents attain margin one in dimension one.

**Necessity of a design in the unbalanced case.** Now $G\succ0$. View all strictly positive definite unit-diagonal matrices $H$ as feasible document Gram matrices. For the documents realizing such an $H$, one can choose a unit query with logits $y_S/\sqrt{y_S^\top H^{-1}y_S}$: explicitly use $D H^{-1}y_S/\sqrt{y_S^\top H^{-1}y_S}$. At $H=G$ the denominator squared is $1/m_0^2$ and its directional derivative along a symmetric zero-diagonal matrix $T$ is
$$
 -y_S^\top G^{-1}TG^{-1}y_S=-m_0^{-4} w_S^\top T w_S .
$$
If the convex hull of the off-diagonal parts of $w_Sw_S^\top$ for $S\in\mathcal F$ omits zero, strict finite-dimensional separation supplies such a $T$ with $w_S^\top T w_S>0$ for every $S$. For sufficiently small positive $t$, $G+tT\succ0$ still has unit diagonal and strictly improves all the margins simultaneously. Therefore equality $m(\mathcal F)=m_0$ forces a distribution on $\mathcal F$ with $\mathbb E[w_iw_j]=0$ whenever $i\ne j$.

Since $\sum_jw_j=\delta$, it follows that $\delta\,\mathbb E w_i=\mathbb E w_i^2$. Each coordinate takes only the values $\alpha,-\beta$, so $w_i^2=(\alpha-\beta)w_i+\alpha\beta$. The coefficient $\delta-\alpha+\beta$ cannot vanish because $\alpha\beta>0$. Consequently $\mathbb E w_i$ is constant in $i$ and the one-point inclusion probabilities are equal. Expanding the off-diagonal identities gives a constant pair inclusion probability as well. Summing the inclusion indicators and the ordered pair indicators gives precisely the two required values. This proves the converse.

**Balanced converse.** Assume $n=2k>2$ and write $P=I-\mathbf1\mathbf1^\top/n$. For a family of margin $m_0$, take canonical documents $v_i=\sqrt{n/(n-1)}Pe_i$ and queries $u_S=y_S/\sqrt n$. All signed logits equal $m_0$. On the product of the unit spheres, the convex hull of the tangential gradients of these signed logits contains zero. Otherwise strict separation gives a tangent vector making every directional derivative positive. Moving a small distance along the corresponding curves on the spheres would improve the margin. Thus there are weights $c_{Si}\geq0$ summing to one such that their weighted tangential gradients vanish.

Set $w_{Si}=c_{Si}y_{Si}$. Stationarity of each query means $Pw_S$ is parallel to $y_S$, so $w_S=a_Sy_S+b_S\mathbf1$. Both signs occur in $y_S$, hence $a_S\geq |b_S|$ and $A=\sum_Sa_S>0$. Write $K=\sum_Sa_S y_Sy_S^\top$ and $h=\sum_S b_S y_S$. Stationarity of each document says $K e_i+h$ is proportional to $Pe_i$. Therefore for some vector $l$,
$$
 K+h\mathbf1^\top=P\operatorname{diag}(l).
$$
Right-multiplying by $P$ gives $K=P\operatorname{diag}(l)P$. The left diagonal is constant $A$, and the right diagonal at $i$ equals $(1-2/n)l_i+(\sum_jl_j)/n^2$. All $l_i$ must therefore be equal, giving $K=nA P/(n-1)$ by trace. Draw $S$ with mass $a_S/A$, then choose with equal probabilities between $S$ and its complement. Its signs have mean zero and second moment $nP/(n-1)$, precisely the required one- and two-point probabilities. Conversely, adding complements leaves a family’s feasible margins and dimensions unchanged because a query can be negated. The certificate and rigidity proof above now apply to any such design on the enlarged family. When $n=2$ any nonempty family of singleton queries becomes the full family on adding complements.

**Scope and priority.** The original paper already gave the isotropic dual weights in Appendix D.2 and the exact singleton margin was previously known. The results advanced here are the design converse, equality classification and corresponding exact-attainment dimension for general uniform families. The general margin curve in each restricted dimension remains open. Provisional significance **61/100** if correct and new. It identifies which incidence patterns force full dimension despite the availability of near-optimal compression. The score concerns the structural result; the exact numerical constant alone would merit less. Independent proof and priority review are pending.
