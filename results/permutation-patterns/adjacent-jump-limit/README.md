# Adjacent jumps in 123-avoiding permutations at fixed and growing radii

Wentao Li · AI-assisted research note

[Read the proof (PDF)](adjacent-jump-limit.pdf) · [LaTeX source](adjacent-jump-limit.tex) · [Result catalogue](../../../README.md)

## The two questions

A 123-avoiding permutation contains no increasing subsequence of length three. There are $C_n=\binom{2n}{n}/(n+1)$ such permutations of length $n$. Let $a_{n,m}$ count those in which consecutive entries differ by at most $m$. Nadler asked how quickly their fixed-$m$ growth constant $\rho_m$ approaches four, and what fraction of all avoiders survive when $m$ grows with $n$. His Theorems 6 and 7 give existence of the growth constant and the bound $4-\rho_m=O((\log m)/m)$. [Original paper, §9.4](https://arxiv.org/pdf/2610.02526#page=48)

## Results

**Fixed radius.** Taking the length to infinity first gives the growth constant $\rho_m=\lim_{n\to\infty}a_{n,m}^{1/n}$. Its deficit satisfies

$$4-\rho_m\sim\frac{16\pi^2}{m^2}\qquad(m\to\infty).$$

**Growing radius.** Let $M$ be the maximum of a standard Brownian excursion of duration one and $F(h)=\Pr(M\le h)$. Then

$$\sup_{m\ge0}\left|\frac{a_{n,m}}{C_n}-F\left(\frac{m}{2\sqrt{2n}}\right)\right|\ \longrightarrow\ 0.$$

The surviving fraction tends to zero below the square-root scale and to one above it. At $m=\lfloor4\sqrt n\rfloor$ it tends to **0.743574078…**. The approximation controls absolute errors in probabilities. The PDF also gives the joint limit for the largest rise and the largest fall on every prefix.

## How the constants arise

Complementing the values turns a 123-avoider into a 321-avoider. On the square-root scale, the positive and negative displacements of a typical 321-avoider follow opposite sides of the same Dyck path. Near a high point, two adjacent entries switching sides give a jump of about twice that height. Hoffman, Rizzolo, and Slivken supply the displacement and spacing estimates. The Brownian excursion maximum distribution is classical. [Displacement theorem](https://arxiv.org/abs/1406.5156) · [Excursion maximum distribution](https://doi.org/10.1214/EJP.v4-52)

For fixed $m$, the proof encodes an avoider by two binary words indicating the positions and values of its exceedances. The difference of their running counts behaves like a walk with steps $-1,0,1$. A jump bound of $m$ effectively confines it to a strip of width $m/4$. Counting words in slightly narrower and slightly wider strips gives matching exponential rates and the factor $16\pi^2$.

## Verification and priority

The checker verifies the two signed prefix bounds and the binary matching identities on all 6,917 Dyck paths of semilengths one through nine. It compares joint jump distributions with direct permutation enumeration through length eight and checks four strip-matrix counts against permutation counts. Run the following from this directory.

~~~sh
python3 verify.py
~~~

The asymptotic claims have written proofs. I found no earlier derivation of the fixed-radius equivalent or the growing-radius jump law in the literature searched. Independent review and Lean formalization are pending. [Checker](verify.py) · [Verification guide](../../../docs/verification.md)
