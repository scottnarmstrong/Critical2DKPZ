# CSZ25: scope of the formalization

Francesco Caravenna, Rongfeng Sun and Nikos Zygouras, *Singularity and regularity of the critical 2D stochastic heat flow*, Probability Theory and Related Fields (to appear); arXiv:2504.06128v2 (2025).

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Theorem 1.11; Theorem 5.7 | Fourth block moments in KPZ Appendix B / geometric-block moment bounds; sixth moments for uniform integrability of polymer pairings. | [`Critical2DKPZ.MomentBounds.genMomentBound_of_ccr`](../../Critical2DKPZ/MomentBounds/CSZ25BlockMomentAssembly.lean); [`Critical2DKPZ.MomentBounds.ccrMomentBound_four_of_wordRuns`](../../Critical2DKPZ/MomentBounds/CCR25MomentBoundFour.lean); [`Critical2DKPZ.MomentBounds.wordRunsBound_four`](../../Critical2DKPZ/MomentBounds/CCR25MomentBoundFour.lean); [`Critical2DKPZ.MomentBounds.ccrMomentBound_six`](../../Critical2DKPZ/MomentBounds/CCR25MomentBoundSix.lean); [`Critical2DKPZ.Provider.blockMoments`](../../Critical2DKPZ/Provider/BlockMoments.lean); [`Critical2DKPZ.SHF.Limit.polymerMeasure_flat_sixth_moment_le`](../../Critical2DKPZ/SHF/Limit/PolymerSixthMoment.lean) | Specialized to planar nearest-neighbour simple random walk, independent standard Gaussian disorder, terminal profile 1, and orders h = 4 and 6. The supporting CCRMomentBound h and WordRunsBound 4 hypotheses are supplied for these orders. Constants depend on h. The geometric-block bounds specialize this estimate rather than restating Theorem 1.11 verbatim. See [CSZ25-D8](../ERRATA-AND-DEVIATIONS.md#csz25-d8), [CCR25-D5](../ERRATA-AND-DEVIATIONS.md#ccr25-d5). |
| Theorem 5.2 | Averaged moment estimates with terminal tests and path restrictions. | — | Outside the formalized scope in its full arbitrary terminal-test / path-restriction form: the proof uses terminal profile 1 and the h=4,6 closure above. Do not infer the full strengthened theorem from a definition named `GenMomentBound`. |
| Theorem 1.1 | Singularity in KPZ §9. | [`Critical2DKPZ.NonGaussian.shf_flatEndpoint_mutuallySingular_of`](../../Critical2DKPZ/NonGaussian/FlatEndpointSingularity.lean) | The model’s terminal marginal is proved almost surely mutually singular with each deterministic finite measure. The supporting lemma takes variance-defect, symmetry, heat-start and dense-flow assumptions, all supplied in the Gaussian model. The proof uses concentration and differentiation; it does not assert the source’s full ball-density limit or its martingale proof. |

## Scope

Gaussian-disorder planar fourth- and sixth-moment specializations of the CSZ25 moment-bound argument are implemented, with geometric-block moment bounds; the full all-orders theorem and the source singularity proof are not formalized here.


## Uses in the four further results

The note’s scale-block estimates reuse the fourth-moment bounds through [`Critical2DKPZ.Extensions.ScaleLimit.block_moments`](../../Critical2DKPZ/Extensions/ScaleLimit/BlockMoments.lean). Its tangent argument also uses positive sixth moments in estimates for ratios of entrance masses. The inverse-sixth-moment bound [`Critical2DKPZ.Extensions.GffTangent.heatStartMass_inverse_sixth_moment`](../../Critical2DKPZ/Extensions/GffTangent/LogMoments.lean) is derived instead from Gaussian convexity and the second moment, and [`Critical2DKPZ.Extensions.GffTangent.integral_inv_ratio_pow_three_le`](../../Critical2DKPZ/Extensions/GffTangent/LogMoments.lean) combines positive and inverse sixth moments by Cauchy–Schwarz. These applications do not establish the full general-order negative-moment claim cited from Theorem 1.11 in the note. The two report groups above are unchanged.

## Source version

[Source version](https://arxiv.org/abs/2504.06128v2). PDF SHA-256: `d0559f6671ce9b74d7d5cde94b2378c791d2a9ce54acd80531e2b03fecb2fb57`.
