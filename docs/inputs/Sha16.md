# Sha16: scope of the formalization

Alexander Shamov, *On Gaussian multiplicative chaos*, Journal of Functional Analysis 270 (2016), DOI 10.1016/j.jfa.2016.03.001; arXiv:1407.4418.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Approximation theorem (source shared-counter Theorem 3); restated approximation theorem later in the paper | Background for a conditional-GMC lower-tail argument; the KPZ proof uses lattice inverse moments instead. | — | Outside the formalized scope: the selected argument proves inverse/log bounds on the lattice and transfers heat-start laws; it does not construct subcritical GMCs from uniformly integrable field approximations. |
| Source shared-counter Theorem 4, (Peyrière/Cameron–Martin characterization); source shared-counter Theorem 6, (randomized shifts) | No remaining selected KPZ dependency. | — | Outside the formalized scope: no GMC/randomized-shift equivalence or conditional-GMC theorem is asserted by the polymer finite-Gaussian constructions. |
| Theorem 19, Hilbert–Schmidt moments, (label thm:HilbertSchmidtMoments) | No remaining selected KPZ dependency. | — | Outside the formalized scope: finite polymer moments do not establish this general Hilbert-space GMC theorem. |

## Scope

The KPZ proof uses lattice inverse-moment estimates rather than Shamov’s abstract GMC construction, approximation, characterization, randomized-shift or Hilbert–Schmidt moment theorems. None of those source theorems is claimed here.

The pinned source shares its theorem counter with problems, corollaries and definitions; Problems 1–2 precede the first theorem. The numbering in the table follows that shared counter.

## Source version

[Source version](https://arxiv.org/abs/1407.4418). PDF SHA-256: `dc1ca1acc2091f690f0a483d58b29245bfd8b4e323738953f17be13d855aaa86`.
