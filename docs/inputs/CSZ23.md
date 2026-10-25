# CSZ23: what is formalized

**Citation.** F. Caravenna, R. Sun, and N. Zygouras, “The critical 2d stochastic heat flow,” *Inventiones Mathematicae* 233 (2023), doi: [10.1007/s00222-023-01184-7](https://doi.org/10.1007/s00222-023-01184-7), arXiv:2109.03766v3.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Theorems 1.1 and 9.1; recalled as Theorem A in the KPZ paper | The KPZ paper cites these for joint convergence of the rescaled polymer measures. The proof constructs a polymer-to-SHF bridge from subsequential limits and Tsai uniqueness. | [`Critical2DKPZ.SHF.Existence.exists_isCriticalSHF_isDenseSHF_of`](../../Critical2DKPZ/SHF/Existence/CriticalSHFExistence.lean) | The general-disorder convergence theorem and its coarse-graining/Lindeberg proof are not formalized. SHF existence and polymer convergence are separately proved for the Gaussian planar simple-walk model using polymer moment convergence and dense-time uniqueness. |
| Theorem 1.2 | Translation and scaling covariance of the SHF, obtained by transporting the dense-time moment axioms using the kernel symmetries. | [`Critical2DKPZ.SHF.Symmetries.isDenseSHF_map_translate`](../../Critical2DKPZ/SHF/Symmetries/DenseTransport.lean); [`Critical2DKPZ.SHF.Symmetries.isDenseSHF_scale`](../../Critical2DKPZ/SHF/Symmetries/DenseTransportScale.lean); [`Critical2DKPZ.DeltaBose.momentKernel_translate`](../../Critical2DKPZ/SHF/DeltaBose/SpatialTransport.lean); [`Critical2DKPZ.DeltaBose.momentKernel_scale`](../../Critical2DKPZ/SHF/DeltaBose/KernelScaling.lean) | The SHF symmetry and covariance statements are proved for the constructed Gaussian-model flow in KPZ’s parameter convention. Supporting symmetry transports take the dense-time SHF axioms. This does not identify the constructed flow with the general-disorder limit of the source theorem. See [CSZ23-D3](../ERRATA-AND-DEVIATIONS.md#csz23-d3). |
| Equation (3.49) | KPZ uses its exponential-moment estimate to obtain a Gaussian tail for sums of walk increments (the KPZ paper). | [`Critical2DKPZ.WalkTails.hypergeometricExpMoment_le`](../../Critical2DKPZ/WalkTails/SquaredBinomialMGF.lean); [`Critical2DKPZ.WalkTails.hypergeometricComposition_upperTail_le`](../../Critical2DKPZ/WalkTails/SquaredBinomialMGF.lean); [`Critical2DKPZ.SHF.Moments.hypergeometricIntWeight_eq_srwHeat_sq_div_return`](../../Critical2DKPZ/SHF/Moments/PairBlockCompositionVariance.lean) | **Special case:** formalized for the normalized squared-binomial/hypergeometric increments arising from the period-2 simple walk, with an explicit sufficient constant; this is the discrete target law used in the KPZ argument, not the full general source derivation from local-limit estimates. |
| Lemma 3.5 | KPZ notes that its own pointwise Gaussian renewal bound is close to this lemma, then proves the bound it needs itself (the KPZ paper). | — | **Outside the formalized scope:** the source lemma’s exponential spatial-moment estimate is not the same as KPZ’s stronger pointwise estimate, and no Lean declaration proves the source statement. |
| Lemma 6.8 | No direct use in the KPZ paper; it is an input cited in related Tsai/DHP analytic arguments. | [`Critical2DKPZ.MomentBounds.summable_abs_replicaGreen_bilinear`](../../Critical2DKPZ/MomentBounds/LZ21Absolute.lean) | **Adapted:** Lean proves absolute summability and the bilinear bound on nontrivial equality partitions with the same-pair exclusion, Hölder-conjugate exponents, and supported tests with summable p/q powers, with a sufficient h,p,q-dependent constant. `replicaGreenKernel` is `(1+replicaDistanceEnergy)^(-(h-1))`, the kernel shape in the printed inequality. This does not by itself prove the full spatially weighted operator theorem. |

## Scope

The Gaussian simple-walk SHF is constructed, with its symmetries and covariance identities. The squared-binomial exponential-moment estimate and the adapted replica-Green bilinear estimate are also proved. The source’s general-disorder convergence theorem, Lemma 3.5 and full weighted operator theorem are outside this scope.

The constructed flow exists by [`Critical2DKPZ.exists_isCriticalSHF`](../../Critical2DKPZStatements/ExistsIsCriticalSHF.lean).

## Source version

[Source version](https://arxiv.org/abs/2109.03766v3). PDF SHA-256: `82b0d247cfa96f5a6c27b50ceff97f400ea59b563d870602ac1121efd35f778b`.
