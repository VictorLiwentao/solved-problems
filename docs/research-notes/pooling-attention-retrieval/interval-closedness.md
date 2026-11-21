# A decision procedure for closedness of an individual interval architecture

Wentao Li · Research note with OpenAI Codex assistance · November 21, 2026

Martinet and Bungert ask whether the realization space of every two-hidden-layer dense ReLU network is closed in $C([a,b])$. Their higher-dimensional construction uses changes in the direction of walls. Here is a finite, exact test for any one scalar-input, scalar-output architecture, including arbitrary depth. I have no proof that the outcomes agree across all widths. [Martinet and Bungert, 2026, Remark 3.10](https://arxiv.org/abs/2611.09887)

Fix a standard feedforward architecture with hidden widths $w_1,\ldots,w_L$. By affine reparametrization take the input interval to be $[0,1]$. Put $B=\prod_{\ell=1}^L(w_\ell+1)$. On any cell where the previous layer is affine, each new preactivation is either identically zero or introduces at most one interior breakpoint. Thus every realization has at most $B$ affine intervals.

Every uniform limit of such functions is continuous piecewise affine with at most $B$ intervals. To see this, pad the list of breakpoints of each approximating function with repeated endpoints and pass to a subsequence along which the entire ordered list converges in $[0,1]^{B+1}$. On any compact subinterval between successive distinct limit knots, the approximants are eventually affine. The uniform limit satisfies affine interpolation there. Continuity fixes the knot values. Strong $W^{1,\infty}$ convergence also implies uniform convergence for the continuous interval representatives.

Represent an arbitrary candidate by ordered knots $0=t_0\leq\cdots\leq t_B=1$ and values $v_0,\ldots,v_B$, requiring duplicate knots to have equal values. Its graph is a finite polynomial predicate: on a nonzero length segment impose
$$
(t_{j+1}-t_j)(y-v_j)=(x-t_j)(v_{j+1}-v_j),\qquad t_j\leq x\leq t_{j+1}.
$$
The graph of the realized function $F_w$ has a first-order formula in the ordered real field by introducing variables for all neurons and using the two cases of ReLU. Nonclosedness in the uniform norm is exactly the following real-field sentence, with graph evaluations expanded by the preceding predicates:
$$
\exists(t,v)\quad
 [\,\forall \epsilon>0\ \exists w\ \forall x\in[0,1]\quad |F_w(x)-f_{t,v}(x)|<\epsilon\,]
 \quad\land\quad
 [\,\forall w\ \exists x\in[0,1]\quad F_w(x)\ne f_{t,v}(x)\,].
$$
Quantify only over valid candidates. Compactness in $x$ makes the first predicate equivalent to closure membership. Real quantifier elimination decides the sentence. If it is true, effective semialgebraic sample-point extraction can return algebraic knots and values witnessing the failure for this architecture.

For the strong Lipschitz norm, require in the approximation predicate both the uniform error bound and
$$
\forall x,y\in[0,1]\quad
|(F_w-f_{t,v})(x)-(F_w-f_{t,v})(y)|\leq\epsilon|x-y|.
$$
The Lipschitz seminorm of a continuous piecewise affine function on an interval equals the essential supremum of its derivative, so this gives exactly strong $W^{1,\infty}$ closure. The algorithm is uniform in the supplied architecture. Quantifier elimination for any finite input does not decide the single assertion quantified over *all* integer widths. No completed answer or significance score is claimed for that assertion.
