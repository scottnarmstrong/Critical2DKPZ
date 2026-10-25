# GQT21: what is formalized

**Citation.** Y. Gu, J. Quastel, and L.-C. Tsai, “Moments of the 2D SHE at criticality,” *Probability and Mathematical Physics* 2 (2021), doi: [10.2140/pmp.2021.2.179](https://doi.org/10.2140/pmp.2021.2.179), arXiv:1905.11310v2.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Theorem 1.1(a), diagram semigroup, proof; Lemma 8.8 | GQT21 supplies the critical moment-kernel/semigroup input used through Tsai’s moment axioms; KPZ also cites GQT21 for critical regularized-SHE moments in the KPZ paper. | [`Critical2DKPZ.SHF.Flow.momentKernel_two_semigroup`](../../Critical2DKPZ/SHF/Flow/MomentKernelTwoSemigroup.lean); [`Critical2DKPZ.DeltaBose.exists_formBound_momentKernel`](../../Critical2DKPZ/SHF/DeltaBose/MomentKernelFormBounds.lean); [`Critical2DKPZ.DeltaBose.momentKernel_L2_form_bounded`](../../Critical2DKPZ/SHF/DeltaBose/MomentKernelL2Interfaces.lean); [`Critical2DKPZ.SHF.Flow.twoParticleGapCollisionKernel_mul_collision_eq_crossing`](../../Critical2DKPZ/SHF/Flow/TwoParticleGapCut.lean) | The two-particle semigroup law, a positive form bound for every particle count, and real L² bilinear bounds through four particles are proved. The collision-cut identity includes the corrected 4π factor. The source’s all-particle operator-semigroup theorem is not asserted verbatim. See [GQT21-E12](../ERRATA-AND-DEVIATIONS.md#gqt21-e12). |
| Lemmas 8.1, 8.2, 8.4, 8.5 and 8.10 | These provide incoming, swapping, collision-density, and diagram-chain controls for the limiting delta-Bose kernels. | [`Critical2DKPZ.DeltaBose.incomingKernel_l2_sq_le`](../../Critical2DKPZ/SHF/DeltaBose/TraceL2.lean); [`Critical2DKPZ.DeltaBose.swappingKernel_l2_sq_le`](../../Critical2DKPZ/SHF/DeltaBose/TraceL2.lean); [`Critical2DKPZ.DeltaBose.integratedSwappingKernel_l2_sq_le`](../../Critical2DKPZ/SHF/DeltaBose/PotentialIntegratedSchur.lean); [`Critical2DKPZ.DeltaBose.exists_scalarDensity_le_envelope`](../../Critical2DKPZ/SHF/DeltaBose/ScalarEnvelope.lean); [`Critical2DKPZ.DeltaBose.exists_formBound_diagramKernel`](../../Critical2DKPZ/SHF/DeltaBose/DiagramKernelBounds.lean) | Adapted to the KPZ/Tsai planar kernel conventions, with a positive Laplace rate chosen after the real parameter. The scalar collision envelope and diagram estimate include positive exponential growth and logarithmic decay. See [GQT21-D3](../ERRATA-AND-DEVIATIONS.md#gqt21-d3), [GQT21-E7](../ERRATA-AND-DEVIATIONS.md#gqt21-e7), [GQT21-E15](../ERRATA-AND-DEVIATIONS.md#gqt21-e15), [GQT21-E16](../ERRATA-AND-DEVIATIONS.md#gqt21-e16), [GQT21-E17](../ERRATA-AND-DEVIATIONS.md#gqt21-e17), [GQT21-E18](../ERRATA-AND-DEVIATIONS.md#gqt21-e18). |
| Theorem 1.1(b), mollified-SHE moment convergence | Earlier critical mollified-SHE moment results, cited as background. | — | **Outside the formalized scope:** the selected polymer-moment construction and dense-time uniqueness proof does not construct or identify the noise-mollified SHE limit; it uses exact polymer moment limits and the limiting kernel axioms instead. |
| Lemmas 4.1–4.2 and 5.1 | These are analytic trace and off-diagonal resolvent inputs to the source’s operator proof. | [`Critical2DKPZ.DeltaBose.integratedSwappingKernel_l2_sq_le`](../../Critical2DKPZ/SHF/DeltaBose/PotentialIntegratedSchur.lean) | **Adapted:** the KPZ formalization proves the needed planar time-integrated swapping estimate directly as a positive-kernel/Schur bound; it does not formalize the source’s Fourier trace domains or cite DFT94 as a Lean premise. |

## Scope

Lean proves the explicit moment-kernel series and a positive form bound at every particle count, the two-particle semigroup law, and the finite-order (`n ≤ 4`) real `L²` kernel bounds used by the KPZ moment argument.

The full all-particle operator-semigroup theorem and mollified-SHE moment-convergence theorem are not formalized here.

## Source version

[Source version](https://arxiv.org/abs/1905.11310v2). PDF SHA-256: `b4fd12b6f046e06feb2edb1ce078ab0492e22ddf0dea68ba69addaef0520368b`.
