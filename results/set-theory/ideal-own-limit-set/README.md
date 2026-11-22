# An ideal that is its own set of ideal limit points

Wentao Li · Research draft with OpenAI Codex assistance · November 22, 2026

[Proof (PDF)](ideal-own-limit-set.pdf) · [LaTeX source](ideal-own-limit-set.tex) · [BibTeX](citation.bib)

Filipów, Kwela and Leonetti ask whether an ideal on the natural numbers must always be absent from its own family of sets of ideal limit points. The index set and the target space play different roles. A real in Cantor space is also a subset of the index set. This identification is essential to the question. [Original preprint, 2024, Question 10.11 in v1](https://arxiv.org/abs/2411.10866) · [Journal version, Question 10.11](https://doi.org/10.1017/jsl.2026.10181)

**Theorem (ZFC).** Let $s:\omega\to 2^\omega$ be an injective enumeration of a countable dense subset. There is a proper ideal $I$ on $\omega$, containing every finite set, such that
$$I=\Lambda_s(I)=\{x\in2^\omega:\exists B\subseteq\omega\;(B\notin I\ \text{and}\ s\!\upharpoonright B\longrightarrow x)\}.$$
Here a subsequence uses the increasing order of its indices. The theorem applies, for example, to a fixed enumeration of the eventually zero binary sequences. No continuum hypothesis is needed.

**The countable dependency sets.** For $a\subseteq\omega$ let $K(a)$ be the set of ordinary cluster points of the indices in $a$, meaning points every neighborhood of which contains $s_n$ for infinitely many $n\in a$. Inclusion of index sets preserves inclusion of cluster sets, and $K(a\cup b)=K(a)\cup K(b)$. In particular
$$J=\{a\subseteq\omega: K(a)\text{ is finite}\}$$
is a proper ideal containing the finite sets, since $K(\omega)=2^\omega$. We will define a smaller ideal by imposing a collection of almost-disjointness tests.

Identify $a$ with its characteristic function. Give $a$ the finite set of successors $K(a)$ when $a\in J$, and no successors otherwise. Every real generates a countable successor-closed set by taking its successors, theirs, and so on for finitely many steps. Well-order the reals. Starting with the empty set, adjoin the successor closure of one real at a time in this order, taking unions at limit stages. Every layer of newly adjoined points is countable, although the union of earlier layers can be uncountable. In particular, if $a\in J$ belongs to an earlier layer, every point of $K(a)$ is already present.

**Choosing index sets.** We will select some points $y$ and give each an infinite index set $W_y$ along which $s$ converges to $y$. At a new layer $D$, select precisely the $y\in D\cap J$ which meet each *previously chosen* $W_z$ in finitely many indices. Make these decisions before choosing any sets for the layer. For each selected $y$ choose $W_y$ so that
$$s\!\upharpoonright W_y\longrightarrow y,\qquad |W_y\cap a|<\infty \quad(a\in D\cap J).$$
To justify this joint requirement, exhaust the countable family $D\cap J$ by increasing finite families. At step $k$ avoid the union $b_k$ of the current finite family, as well as all previously used indices for this $y$. Inside the length-$k$ basic neighborhood of $y$, take a smaller nonempty clopen set disjoint from the finite set $K(b_k)$. Only finitely many indices of $b_k$ land in this clopen set, by compactness. Infinitely many indices of $s$ land there by density and injectivity. Choose a fresh index there, larger than the previous one. The resulting index set has both required properties. Separate choices for different $y$ cause no conflicts. Convergent subsequences with distinct limits have only finitely many indices in common.

Let $T$ be the set of selected points and set
$$I=\{a\in J:\ \forall y\in T\quad |a\cap W_y|<\infty\}.$$
This is an ideal, being the intersection of $J$ with hereditary, finite-union-closed conditions, and is proper since it is contained in $J$.

**Verifying the equality.** First $T=I$. For $a\in T$ all earlier tests passed. The construction makes all same-layer tests pass as well. If a later $y$ had infinite intersection $W_y\cap a$, the common subsequence would converge to $y$, so $y\in K(a)$. This contradicts successor closure at the stage when $a$ was included. Conversely, each unselected $a$ was either outside $J$ or failed a specific earlier test which still occurs in the definition of $I$.

For $y\in T$, $W_y$ fails its own test and hence is $I$-positive, witnessing $y\in\Lambda_s(I)$. For $y\notin T$, every infinite $B$ along which $s$ converges to $y$ has $K(B)=\{y\}$. It belongs to $J$ and meets every $W_z$, $z\in T$, only finitely, since the limits differ. Thus $B\in I$. This proves $\Lambda_s(I)=T=I$.

**Scope and priority.** The authors' earlier ideal for a *prescribed* set of target points and the later low-rank theorem of Kwela do not identify the resulting ideal with the target. Keeping all cluster points of an earlier small index set in its own or an earlier layer is what makes the self-reference work. The construction uses a well-order of the reals and establishes no Borel or projective upper bound for this ideal. Kwela independently settled the authors' different Question 10.9 about Borel ideals of class $\Pi^0_4$. [Filipów, Kwela and Leonetti, Theorem 10.8](https://arxiv.org/abs/2411.10866) · [Balcerzak, Głąb and Leonetti, Section 4](https://arxiv.org/abs/2407.12160) · [Kwela, Theorem 4.3](https://arxiv.org/abs/2611.03432)

The weaker question printed immediately after Question 10.11 has a cardinality answer under the paper's definition. There are $\mathfrak c$ sequences in Cantor space and $2^{\mathfrak c}$ subsets of Cantor space, so no single ideal realizes every subset. This elementary observation uses the same quantifiers as the printed sentence. It carries no novelty claim and receives no separate score. The proposed significance of the self-realization theorem is **62/100** for disproving a general exclusion question by a construction in ZFC. Independent proof and priority review are pending.
