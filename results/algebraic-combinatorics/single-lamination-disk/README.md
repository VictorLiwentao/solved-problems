# Real zeros for a single lamination in a polygon

Wentao Li · Prepared with assistance from OpenAI Codex

[Read the proof (PDF)](single-lamination-disk.pdf) · [LaTeX source](single-lamination-disk.tex) · [Verification script](verify.py) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/algebraic-combinatorics/single-lamination-disk/citation.bib)

## Original question

For an arc in any triangulation of a disk with one lamination curve, does specializing the cluster variables to one and its coefficient to $q$ give a log-concave coefficient sequence? [Wonwoo Kang, Kyeongjun Lee and Eunsung Lim, 2026](https://arxiv.org/abs/2508.04396v4) · Conjecture 1, disk formulation in v4. The original 2025 preprint asked about a broader class of surfaces

## Result

Every such polynomial has only negative real zeros and hence log-concave coefficients. The result holds for every triangulation, arc and single curve in an unpunctured disk.

The curve splits the polygon vertices into two intervals. On each triangle crossed by both the curve and the target arc, the two endpoint values update by adding either $V$ to $U$ or $qU$ to $V$. Tracking their ratio at complex $q$ excludes zeros in the upper half-plane. The manuscript also recomputes Examples 4 and 6 from the original triangulations.

## Earlier work and verification

The authors established disk unimodality. Earlier counterexamples use an annulus, which explains the importance of the November 2026 disk formulation. The proof uses the laminated lambda lengths of Fomin and Thurston. [Annular calculation by Tang](https://aixiv.online/abs/2611.00002) · [Fomin and Thurston](https://arxiv.org/abs/1210.5569)

The verifier mutates the extended exchange matrices and counts roots exactly with SymPy. It checks all 9,499 triangulation, lamination and target combinations for polygons with four through seven vertices, and recomputes the source’s two larger examples. Run `python3 verify.py` from this directory in a repository checkout.

**Significance 62/100.** Real-rootedness strengthens the proposed coefficient inequalities across all polygon triangulations. A single curve gives an invariant sector for two explicit transfer operations. Independent proof and priority review is pending. [Scoring scale](../../../docs/scores-and-sources.md#algebraic-combinatorics)
