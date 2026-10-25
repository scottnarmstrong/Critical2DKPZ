# DHP26

**Citation:** Hindy Drillick, Jonathan Hou, and Shalin Parekh, “A universality result for the critical 2d stochastic heat flow,” arXiv:2609.15832v1 (2026).

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Fourth-moment limit (source label `4thmom`); partition expansions | The KPZ article cites DHP26 only as universality context. Its collision-word expansion is adapted to prove the period-two Gaussian polymer moment limits used to construct the KPZ SHF. | [`Critical2DKPZ.SHF.Moments.rescaledP2P_moment_tendsto_moving_of`](../../Critical2DKPZ/SHF/Moments/WordExpansionAssembly.lean); [`Critical2DKPZ.SHF.Moments.polymerMovingMomentLimit_of_wordStages`](../../Critical2DKPZ/SHF/Moments/WordExpansionLimitBridges.lean); [`Critical2DKPZ.SHF.Moments.polymerMomentLimit_of_wordStages`](../../Critical2DKPZ/SHF/Moments/WordExpansionLimitBridges.lean) | The moving and fixed tested moment limits through order four are proved for the Gaussian period-two polymer. The tests have product form ∏ i, φ i (x i,y i), with each φ i compactly supported and continuous on Plane × Plane; 0 ≤ s < t, the real time sequences converge to s,t, and all starting times are nonnegative. The supporting word-domination, non-pair-remainder and individual-word-limit assumptions are proved for this model. Reachable parity classes, spatial scale $\sqrt{2/N}$, cell area $4/N$ and terminal disorder are retained. Neither arbitrary configuration tests nor general-disorder universality nor the source’s third/fifth-moment analogies are asserted. See [DHP26-D5](../ERRATA-AND-DEVIATIONS.md#dhp26-d5), [DHP26-D6](../ERRATA-AND-DEVIATIONS.md#dhp26-d6), [DHP26-D7](../ERRATA-AND-DEVIATIONS.md#dhp26-d7), [DHP26-D12](../ERRATA-AND-DEVIATIONS.md#dhp26-d12), [DHP26-D13](../ERRATA-AND-DEVIATIONS.md#dhp26-d13), [DHP26-D14](../ERRATA-AND-DEVIATIONS.md#dhp26-d14), [DHP26-D15](../ERRATA-AND-DEVIATIONS.md#dhp26-d15), [DHP26-D16](../ERRATA-AND-DEVIATIONS.md#dhp26-d16). |
| Approximate composition (source label `convo`) | Composition and flow in the polymer construction; the KPZ paper does not cite this theorem directly. | [`Critical2DKPZ.SHF.Flow.smoothedProduct_approx_flow_of`](../../Critical2DKPZ/SHF/Flow/ThinSlabApproxFlow.lean); [`Critical2DKPZ.SHF.Flow.isDenseSHF_of_isPolymerSubseqLimit_of_comparisons`](../../Critical2DKPZ/SHF/Flow/DenseSHFFromSlabComparisons.lean) | Approximate composition and dense-time flow are proved for the Gaussian period-two polymer with compactly supported continuous endpoint-pair tests and smooth compactly supported nonnegative unit-integral mollifiers. The supporting moment, sixth-moment, semigroup and comparison hypotheses are supplied for the model. This is an adaptation of the composition theorem, rather than a proof under the source’s general assumptions. See [DHP26-D4](../ERRATA-AND-DEVIATIONS.md#dhp26-d4), [DHP26-D14](../ERRATA-AND-DEVIATIONS.md#dhp26-d14), [DHP26-D15](../ERRATA-AND-DEVIATIONS.md#dhp26-d15), [DHP26-D16](../ERRATA-AND-DEVIATIONS.md#dhp26-d16). |

## Scope

A parity-correct adaptation proves Gaussian polymer moment limits through order four for products of compact endpoint-pair tests, and the approximate composition and dense-flow properties used in the SHF construction. The source’s general-disorder universality theorem and arbitrary configuration-test formulation are outside this scope.

The Gaussian-model word limits and their use in SHF existence are proved in [the final construction](../../Critical2DKPZ/Assembly/Final.lean).

## Source version

[Source version](https://arxiv.org/abs/2609.15832v1). PDF SHA-256: `07efd5c71ed961bfe76a820a75e6196042c2bfae0e9b5ea06ca750b3aa2b39d8`.
