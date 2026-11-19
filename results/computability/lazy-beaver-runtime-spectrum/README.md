# An exponential gap in the Lazy Beaver runtime spectrum

Wentao Li · Prepared with assistance from OpenAI GPT-6.2 Astra

[Read the proof (PDF)](lazy-beaver-runtime-spectrum.pdf) · [LaTeX source](lazy-beaver-runtime-spectrum.tex) · [Finite checks](verify.py) · [Result catalogue](../../../README.md)

## How many runtimes can the tables encode?

The $n$-state Busy Beaver maximizes the number of steps before halting on a blank tape. Its cousin, the Lazy Beaver $\mathrm{LB}(n)$, asks for the *first missing time*. If some machine halts after exactly $t$ steps for every $1\le t<T$, then $\mathrm{LB}(n)\ge T$. Scott Aaronson asked whether this initial interval is within a polynomial factor of the number of different transition tables, after identifying state renamings and mirror images. [The Busy Beaver Frontier, §§5.7 and 5.9, Conjecture 25](https://doi.org/10.1145/3427361.3427369)

Consider only tables in which some directed path leads from the start to every state. Even among these tables there is an **exponential gap**. Allow the input to be any binary tape. Each machine then has a runtime profile, a function that reports its halting time or infinite runtime on each tape. If $P_n$ counts the different profiles of *all* $n$-state machines and $D_{\rm acc}(n)$ counts the graphically accessible tables up to renaming and reflection, the draft proves that some constant $c>0$ satisfies

$$
\mathrm{LB}(n)-1 \ \le\ |R_n|\ \le\ P_n\ \le\ e^{-cn}D_{\rm acc}(n)
$$

for every sufficiently large $n$. Here $R_n$ is the set of finite runtimes on the blank tape. The proof also gives a computable list this small that represents every machine's complete execution on every tape.

## How a reachable state can have an unreadable instruction

Suppose the only way into state $B$ is from $A$, and the only way into $C$ is from $B$. The machine starts in $A$. On the arrow into $B$, it writes a **1** and moves right. On the arrow into $C$, it moves left. Whenever the head reaches $C$, it returns to the **1** it just wrote. The instruction for reading **0** in $C$ can never run, whatever tape the machine started with.

The proof counts how often this happens in a uniform accessible table. Except for an exponentially small fraction of tables, it exhibits linearly many disjoint pairs of moves like these. Varying the write bits of their unreadable instructions gives exponentially many different tables with the same execution on every tape.

## Proof and priority

The four-page draft gives the counting proof and the construction of the representative list. The checker exhausts the successor graphs through three states, verifies the rotation argument on 2,771 covered destination words, and compares 1,024 pairs of short traces. A six-state example exercises two simultaneous changes on 32 initial tapes. Independent review and Lean formalization are pending.

Prior accessible-graph counts and their published asymptotics already imply that Aaronson's original polynomial lower bound fails. That implication is prior work. The further result here is the exponential loss **within** the graphically accessible population, even when distinguishing machines by their runtimes on all initial tapes. I found no earlier statement of this stronger bound in the sources checked. [Earlier Lazy Beaver bound](https://oeis.org/A337805) · [Accessible graph counts and asymptotics](https://oeis.org/A107668) · [Smith and Aaronson on the original denominator](https://scottaaronson.blog/?p=4916#comment-1852007)
