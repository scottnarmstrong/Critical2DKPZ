# Chen26: scope of the formalization

Wei-Kuo Chen, *A Gaussian Convexity for Logarithmic Moment Generating Functions with Applications in Spin Glasses*, Annales de l’Institut Henri Poincaré, Probabilités et Statistiques 62 (2026), no. 1, 195–206; arXiv:2311.08351v2.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Theorem 1 | KPZ Theorem 3.1 and all one-/two-point Gaussian convexity estimates. | [`Critical2DKPZ.gaussian_convexity`](../../Critical2DKPZStatements/GaussianConvexity.lean); [`Critical2DKPZ.Provider.gaussian_convexity`](../../Critical2DKPZ/Provider/GaussianConvexity.lean); [`Critical2DKPZ.GaussianConvexity.convexOn_logMGFRatio_of_convex_gaussian`](../../Critical2DKPZ/GaussianConvexity/ConvexGaussian.lean) | The normalized log-MGF is convex at every real order, including its mean extension at zero, for finite convex functions under arbitrary finite-dimensional Gaussian laws with all positive exponential moments. This includes the source standard-Gaussian conclusion. The proof uses Ehrhard interpolation and one-dimensional comparison rather than stochastic control. |
| Theorem 2; Theorem 3 | Negative-order consequences and concentration background. | — | Outside the formalized scope as the complete numbered theorems: the library proves the scalar inequalities needed by KPZ, but no assertion is made here that every derivative modulus and optimal small-deviation conclusion of these theorems is present. |
| Spin-glass applications | Outside the KPZ proof. | — | Outside the formalized scope: no Parisi/SK model application is claimed. |

## Scope

The finite-dimensional Gaussian normalized-log-MGF convexity conclusion, including negative orders and the value at zero, is proved by a different argument. The stochastic-control proof, full small-deviation theorems and spin-glass applications are outside this scope.

## Source version

[Source version](https://arxiv.org/abs/2311.08351v2). PDF SHA-256: `3778df4c767e80df293a296058193404f6114af0bbfdf02e60409a27078d7fd0`.
