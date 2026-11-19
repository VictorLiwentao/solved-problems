# Antichains in locally finite trees without countable choice

**Wentao Li**, with assistance from **OpenAI GPT-6.2 Astra**. [Paper (PDF)](tree-antichain-choice.pdf) · [LaTeX source](tree-antichain-choice.tex) · [Finite algebra check](verify.py) · [Download BibTeX](https://raw.githubusercontent.com/VictorLiwentao/solved-problems/main/results/set-theory/tree-antichain-choice/citation.bib)

In a rooted tree with finitely many children at each vertex, every level is finite. Without choice the union of the levels can still be uncountable. Banerjee and Gopaulsingh asked whether either of two principles that force certain such trees to be countable would suffice to choose from every sequence of finite sets. [Original paper, Questions 6.6 and 6.7](https://doi.org/10.4064/ba221221-6-6)

The proposed answer to **Question 6.6 is no in pure ZF**, even when both principles hold together. In the model every uncountable locally finite rooted tree has an uncountable antichain, yet some sequence of pairs has no selector. A Ramsey ultrafilter determines the allowed supports of coordinate flips. Finite character spaces track which flips distinguish vertices. The proof builds an antichain inside the permutation model, then uses Pincus’s transfer theorem to obtain the pure-set conclusion.

**Question 6.7 has a positive answer in Pincus’s Model X.** In that specified model the union of a well-orderable family of well-orderable sets is well-orderable. A permutation fixing a finite support can move any bounded interval of fresh rational positions away from a second finite set. This forces it to act trivially on each well-orderable member of the family.

The checker exhausts the 67 subspaces of a four-dimensional binary character space and all 16 coordinate supports. It checks 446 subspace inclusions and 4,408 strict refinements of orbits. The infinite construction and the transfer are justified in the paper. Independent proof and priority review are pending. [Related separation by Hall and Shelah](https://doi.org/10.4064/fm220-3-2) · [Howard and Tachtsis on related graph questions](https://doi.org/10.4064/fm250514-20-7)
