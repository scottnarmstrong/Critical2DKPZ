# FMP25: scope of the formalization

Maite Fernández-Unzueta, James Melbourne, Gerardo Palafox-Castillo, *On convex functions of Gaussian variables*, preprint (2025), arXiv:2510.06676v1.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Theorem 2.1 | Ehrhard input to Gaussian convexity (KPZ Theorem 3.1). | [`Critical2DKPZ.Ehrhard.gaussian_set_ehrhard`](../../Critical2DKPZ/Ehrhard/GaussianSetInequality.lean) | Adapted: all finite-dimensional Gaussian laws, including singular ones; convex sets; finite-threshold CDF form handles masses 0 and 1 and uses outer measure. |
| Theorem 1.1; reflected Section 3 comparison, Theorem 3.1 | Convexity of the normalized log-MGF, including negative orders and the value at zero. | [`Critical2DKPZ.GaussianConvexity.convexOn_logMGFRatio_of_isEhrhardType_of_positive_moment`](../../Critical2DKPZ/GaussianConvexity/FMPComparison.lean); [`Critical2DKPZ.GaussianConvexity.convexOn_logMGFRatio_of_convex_gaussian`](../../Critical2DKPZ/GaussianConvexity/ConvexGaussian.lean) | Adapted: convex branch on the real finite exponential-moment domain with at least one finite positive exponential moment; includes constants and zero. The Gaussian-functional specialization assumes all positive exponential moments. Extended +∞ values and strictness are not asserted. See [FMP25-D1](../ERRATA-AND-DEVIATIONS.md#fmp25-d1), [FMP25-D2](../ERRATA-AND-DEVIATIONS.md#fmp25-d2), [FMP25-D3](../ERRATA-AND-DEVIATIONS.md#fmp25-d3). |
| Lemma 3.1, (convex sublevel branch) | Convex Gaussian functionals have Ehrhard-type laws. | [`Critical2DKPZ.EhrhardType.isEhrhardType_map_of_convex`](../../Critical2DKPZ/EhrhardType/GaussianImages.lean) | Adapted: finite convex real functions on arbitrary finite-dimensional Gaussian space, constants included; does not assert the printed concave superlevel codomain. |
| Theorem 4.3; quantile argument | Represent an Ehrhard law as a monotone convex image of a standard real Gaussian. | [`Critical2DKPZ.EhrhardType.isEhrhardType_iff_exists_monotone_convex`](../../Critical2DKPZ/EhrhardType/Characterization.lean); [`Critical2DKPZ.EhrhardType.map_gaussianQuantileTransport`](../../Critical2DKPZ/EhrhardType/Quantile.lean) | Adapted: equality in law, generalized inverse of strict distribution functions, endpoint atoms and constants included; not equality of random variables on the original space. See [FMP25-D4](../ERRATA-AND-DEVIATIONS.md#fmp25-d4), [FMP25-E5](../ERRATA-AND-DEVIATIONS.md#fmp25-e5). |
| Strictness clause of Theorems 1.1/3.1; Theorems 3.3–3.4 and Corollary 3.5 | Not required for the selected Gaussian-convexity interface. | — | Outside the formalized scope as these paper statements: non-strict convexity and the Ehrhard representation suffice; no Gaussian equality-case or affine-rigidity claim is made. |
| Appendix A, Lemmas A.1–A.2 | Three-exponential crossing comparison inside the Section 3 proof. | [`Critical2DKPZ.GaussianConvexity.three_exponential_factorization`](../../Critical2DKPZ/GaussianConvexity/ExponentialInterpolation.lean) | Adapted: direct three-exponential factorization and power-chord comparison replace the arbitrary-number-of-exponentials zero-counting/sign theorem. No full Appendix A theorem is claimed. See [FMP25-D5](../ERRATA-AND-DEVIATIONS.md#fmp25-d5). |

## Scope

Lean proves the convex-branch Gaussian log-MGF comparison on its finite moment domain and the adapted Ehrhard-law representation used by KPZ, including the finite-dimensional specialization with all positive exponential moments.

The strictness and equality cases, concave branch and extended-value theorem on all real orders are not formalized here.

## Source version

[Source version](https://arxiv.org/abs/2510.06676v1). PDF SHA-256: `bea06c609a52c113f71b63951be4fe5a1180858f5efa67b99e374bd82fd5763d`.
