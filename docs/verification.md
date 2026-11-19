# Reproducing the checks

[Result catalogue](../README.md) · [Lean formalizations](../lean/README.md)

Run these commands from the repository root. The scripts have been tested with Python 3.12. The type-D interlacing and random-graph independence-root checks use SymPy 1.14.0. The other eight checks use only the Python standard library.

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install sympy==1.14.0
python scripts/verify.py
```

The runner discovers each note’s `verify.py`, prints its output, and exits with a failure status if any check fails. To reproduce just the parking-function counterexample, run the following in any checkout with Python 3.12.

```sh
python3 results/algebraic-combinatorics/parking-excedances/verify.py
```

The last line gives the scaled Laguerre expression.

```text
B^2 - AC = -1177338341095610033551509654796761547971187113984
```

The negative sign certifies a failure of the Laguerre inequality. The proof explains why that single witness settles the universal conjecture. For general theorems such as type-D interlacing, the scripts compare finite examples with the statement and the PDF supplies the proof for all parameters. Each note describes what its own check covers.

## Rebuilding a PDF

The PDF and its matching LaTeX source sit together. With a TeX installation providing pdfLaTeX, latexmk, Latin Modern, and the packages listed in the source, run the build from the note’s directory. The surface map-graph note builds with the following commands.

```sh
cd results/graph-theory/surface-map-cliques
latexmk -pdf -interaction=nonstopmode -halt-on-error surface-map-cliques.tex
```

## Adding a note

Place the PDF, LaTeX source, and a short README under `results/<topic>/<problem>/`. Link the original question and state the hypotheses beside the claim. A computational check named `verify.py` is picked up by the runner. Add the note to the topic table in the main catalogue. When a Lean theorem accompanies the note, record its declaration and checked scope in the [formalization index](../lean/README.md).
