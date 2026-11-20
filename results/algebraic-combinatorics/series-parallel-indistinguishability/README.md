# Series-parallel structure under labeled partition equivalence

Wentao Li · Research draft prepared with assistance from OpenAI Codex

[Proof (PDF)](series-parallel-indistinguishability.pdf) · [LaTeX](series-parallel-indistinguishability.tex) · [BibTeX](citation.bib)

## Original problem

If a labeled series-parallel poset has the same partition enumerator as a second labeled poset, must the second poset be series-parallel? [Ricky Ini Liu and Michael Weselcouch, 2019](https://arxiv.org/abs/1903.00551) (Question 5.4).

## Result

No. Grafting identical chains below two three-element forks gives equal enumerators. One resulting poset is series-parallel and the other contains an induced N.

Liu and Weselcouch proved reconstruction for naturally labeled series-parallel posets. Their mixed-label example had both posets in the class. The construction here crosses its boundary.

**Significance 60/100.** Disproves the proposed extension of a reconstruction theorem to general labelings. The obstruction occurs even for connected Hasse trees. Independent review of the proof and priority is pending.

## Reproducible check

The six-, nine- and twelve-vertex pairs have identical descent histograms on 30, 560 and 11,550 linear extensions per poset, respectively. [Verification script](verify.py)
