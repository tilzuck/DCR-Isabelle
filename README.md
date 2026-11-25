# DCR graphs in Isabelle/HOL

A formalisation of Dynamic Condition Response (DCR) graphs in Isabelle/HOL,
following the literature from the original paper by Hildebrandt and Mukkamala
(PLACES 2010) onwards. The session document
[output/document.pdf](output/document.pdf) contains the theories with their
explanations and the papers' figures.

## Building

Requires [Isabelle2026](https://isabelle.in.tum.de/) and a TeX distribution
with LuaLaTeX and BibTeX (e.g. TeX Live). Then run

```sh
isabelle build -D .
```

A precompiled version of the resulting document can be found here: `output/document.pdf`.
