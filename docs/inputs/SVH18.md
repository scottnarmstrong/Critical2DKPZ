# SVH18: scope of the formalization

Yair Shenfeld and Ramon van Handel, *The equality cases of the Ehrhard–Borell inequality*, Advances in Mathematics 331 (2018), DOI 10.1016/j.aim.2018.04.013; arXiv:1709.00061.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Theorem 1.1 (simpleeb) | Background Ehrhard–Borell inequality; KPZ needs the convex sum-one subcase. | [`Critical2DKPZ.Ehrhard.gaussian_set_ehrhard`](../../Critical2DKPZ/Ehrhard/GaussianSetInequality.lean) | Special case: convex sets, λ=1-t, μ=t, 0≤t≤1, any finite-dimensional Gaussian law, in threshold form. Proved by NP16. Does not cover arbitrary closed sets or all λ+μ≥1 regimes. |
| Theorem 1.2 (simpleeq); main functional equality cases | Equality-case alternative cited in FMP25, not used for KPZ Gaussian convexity theorem. | — | Outside the formalized scope: non-strict log-MGF convexity and Ehrhard representation suffice; no extremizer classification or equality rigidity from this paper is claimed. |

## Scope

Only the convex sum-one special case of the background Ehrhard–Borell inequality is proved, independently of this paper’s equality-case theory.

The equality-case classification, its functional variants and the full weighted nonconvex Ehrhard–Borell theorem are not formalized here.

## Source version

[Source version](https://arxiv.org/abs/1709.00061). PDF SHA-256: `f8b4b1ba84f6dd18c196c7856115ad52b121a8e566a1eba48deafeb0e1064994`.
