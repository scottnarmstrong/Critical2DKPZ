# BCT25: scope of the formalization

Quentin Berger, Francesco Caravenna and Nicola Turchi, *Strong Disorder for Stochastic Heat Flow and 2D Directed Polymers*, preprint (2025; pinned revision 2026), arXiv:2508.02478v3.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Theorem 1.1 | Strong-disorder background. | — | The source’s uniform large-time strong-disorder bounds are not formalized. The KPZ proof establishes its own local estimates and singularity criteria. |
| Proposition 2.10, variance estimates; equation (2.11) | Notation for the remaining distance parameter and the comparison preceding KPZ Lemma 7.6 / Claim B.1. | — | The source variance estimates are not formalized. KPZ uses the opposite sign for the distance parameter and proves its own renewal-gap estimates. |

## Scope

BCT25 supplies notation and methodological comparisons; its strong-disorder and uniform variance theorems are outside the scope of the formalization.

## Source version

[Source version](https://arxiv.org/abs/2508.02478v3). PDF SHA-256: `380229a336f7ee83f22df4c58f5b68f6db740f53afbc44d9a51ad68cb3e7fc39`.
