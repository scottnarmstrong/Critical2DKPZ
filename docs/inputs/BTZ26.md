# BTZ26: scope of the formalization

Quentin Berger, Nicola Turchi and Nikos Zygouras, *Fractional moments of the Stochastic Heat Flow and 2D Directed Polymers*, preprint (2026), arXiv:2608.13359v1.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Theorem 1.1 | Fractional-moment / intermittency context. | — | Outside the formalized scope: uniformity simultaneously over t>0, θ∈R and ball radius r≤√t is not supplied by the fixed heat-start KPZ estimates. The KPZ proof uses its own Gaussian-convexity bounds. |
| Proposition 1.6; equation (1.12) | KPZ Appendix B explicitly borrows notation from BCT25/BTZ26. | — | Outside the formalized scope as this proposition: the library’s critical-window and renewal-gap estimates are proved for the Gaussian polymer and do not establish BTZ26’s full parameter-uniform theorem. |

## Scope

BTZ26 supplies notation and methodological comparisons; its parameter-uniform fractional-moment and variance theorems are outside the scope of the formalization.

## Source version

[Source version](https://arxiv.org/abs/2608.13359v1). PDF SHA-256: `24f038463c5fb118c7db626d2aac5a3f16e7a18ab852ccdf83f26a4c8712f0f3`.
