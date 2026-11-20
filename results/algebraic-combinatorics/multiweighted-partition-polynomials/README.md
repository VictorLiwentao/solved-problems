# Characteristic polynomials of multiweighted partitions

Wentao Li · Prepared with assistance from OpenAI Codex

[Read the proof (PDF)](multiweighted-partition-polynomials.pdf) · [LaTeX source](multiweighted-partition-polynomials.tex) · [Verification script](verify.py) · [BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/algebraic-combinatorics/multiweighted-partition-polynomials/citation.bib)

## Original question

Is there a formula for the equal-variable weighted bond polynomial of the complete graph when more than two colors are available? [Rafael S. González D’León and Michelle L. Wachs, 2026](https://arxiv.org/abs/2608.08692v2) · Question 7.1

## Result

A Laguerre coefficient formula works for every size and number of colors above two. Odd ground-set size gives no real zero, even size gives one, and the absolute coefficients are strictly log-concave.

The reversed polynomial is a moment of a translated sum of gamma variables. Even powers are positive on the whole real line. Odd powers have strictly positive derivative after averaging. The manuscript gives both coefficient orders used in the source paper and proves ordinary strict log-concavity separately.

## Earlier work and verification

The earlier one-block inverse series and weighted Whitney-number sums are due to González D’León. The two-color specialization is also known. The more general Schur-log-concavity conjecture for every graph remains open in this work. [Earlier inverse series and rank sums](https://arxiv.org/abs/1408.5415) · [Two-color formula](https://arxiv.org/abs/1309.5527)

Direct Möbius inversion in 20 complete finite posets, containing 3,711 weighted partitions in total, reproduces every coefficient for one through five labels and two through five colors. Run `python3 verify.py` from this directory in a repository checkout.

**Significance 52/100.** Answers the equal-color formula question and classifies all real zeros. Its proof starts from the earlier inverse series for maximal intervals. Independent proof and priority review is pending. [Scoring scale](../../../docs/scores-and-sources.md#algebraic-combinatorics)
