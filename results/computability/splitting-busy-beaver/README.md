# Splitting the Busy Beaver runtime

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Proof (PDF)](splitting-busy-beaver.pdf) · [LaTeX source](splitting-busy-beaver.tex) · [Finite verification](verify.py)

Toby Ord and Scott Aaronson asked whether two functions could share the computational power of Busy Beaver. Upper bounds on both should decide halting, even though either function alone is too weak. The written construction assigns a colour to each actual halting two-symbol machine. Each colour has its own record for machines of at most $n$ states. [Ord’s original question](https://scottaaronson.blog/?p=4916#comment-1851063) · [Aaronson’s formulation](https://scottaaronson.blog/?p=4916#comment-1851125) · [Published background, Theorem 5](https://doi.org/10.1145/3427361.3427369)

## What the split achieves

- Take red and blue to be the even and odd colours. Both runtime records eventually exceed every computable function. Neither oracle can compute even an upper bound on the other. Their pointwise maximum is exactly the ordinary Busy Beaver function.
- The same construction gives countably many colours. Give an oracle the exact aggregate record for every colour except one. It still cannot compute an upper bound on the missing record. More generally, the problem of finding an upper bound for one group of colours reduces to that for another exactly when the first group is contained in the second. This holds even for noncomputable groups.
- Assume ZFC is arithmetically sound. Add the exact records of all the other colours as axioms. At every sufficiently large state count, this stronger theory still cannot prove any concrete numerical upper bound on the missing colour’s record. The threshold depends on the theory and the colour.
- The colouring algorithm terminates on each halting machine. If a rule must return one of finitely many colours on *every* description, some colour necessarily carries the full halting problem by itself.

One can also distinguish the information the two records give about where they trade the lead. Blue can enumerate infinitely many state counts at which red leads. Red cannot enumerate any infinite subsequence of those positions. Knowing such a subsequence in addition to red would be enough to recover blue.

## Proof and priority

The proof uses Sacks-style low splitting, Robinson’s theorem on settling times, and Harrington’s high noncuppable degree. These classical theorems supply the degree-theoretic ingredients. The proposed contribution is their realization by a partition of the original two-symbol runtimes, with an exact maximum at every state count and the inclusion criterion for arbitrary groups of colours. The finite check illustrates bounding and recovering runtimes. The proof of incomparability and independence is theoretical. The priority search found the 2020 public question and the classical splitting results, but no earlier publication giving this runtime construction. Independent review and Lean formalization are pending. [Classical splitting](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/notes-on-sacks-splitting-theorem/0ACA242AC51502CAF19C405DDD2C54AE) · [Robinson](https://doi.org/10.1002/malq.19680142105) · [Jockusch and Shore](https://doi.org/10.1090/S0002-9947-1983-0682720-1)
