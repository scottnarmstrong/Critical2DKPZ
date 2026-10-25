/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BlockWeightedVariance
import Critical2DKPZ.Extensions.ScaleLimit.WeightedPartialSumCLT
import Critical2DKPZ.Extensions.ScaleLimit.SeqReduction
import Mathlib.Tactic

/-! # The finite-dimensional Gaussian limit of the bounded block sums

Every finite projection is a bounded independent triangular array with cutoff
coefficients uniformly bounded by the sum of the absolute projection weights.
The identified variance is the Brownian minimum-kernel quadratic form.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Cramér–Wold and the bounded-array CLT give the Brownian finite-dimensional
law for every positive finite collection of scale times. -/
theorem cramerWold_lindeberg (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ I : Finset ℝ≥0,
      (∀ i ∈ I, 0 < i) →
      TendstoInDistribution (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) =>
        normalizedPartialSum P Z ρ L (i.val : ℝ) ω) atTop id
        (fun _ => P) (BrownianReal.projectiveFamily I) := by
  obtain ⟨ρ₀, hρ₀, hV⟩ := weightedPartialSum_variance_tendsto ϑ P Z hZ
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ I hI
  have hρ1 : 1 < ρ := hρ₀.trans_le hρ
  have hXm (L : Set.Ioi (0 : ℝ)) : AEMeasurable
      (fun ω (i : I) => normalizedPartialSum P Z ρ L (i.val : ℝ) ω) P :=
    aemeasurable_pi_iff.mpr fun i => (memLp_normalizedPartialSum ϑ P Z hZ hρ1 L i.val).aemeasurable
  apply (tendstoInDistribution_atTop_iff_sum hXm aemeasurable_id).mpr
  intro v
  let σ : ℝ≥0 := (variance (weightedCoordinate v) (BrownianReal.projectiveFamily I)).toNNReal
  let Y := centeredLogBlock P Z ρ
  let n : Set.Ioi (0 : ℝ) → I → ℕ := fun L i => nL ρ L (i.val : ℝ)
  let a : Set.Ioi (0 : ℝ) → ℝ := fun L => Real.sqrt L
  have ha : Tendsto a atTop atTop := Real.tendsto_sqrt_atTop.comp (tendsto_Ioi_atTop.mp tendsto_id)
  have hsum (L : Set.Ioi (0 : ℝ)) (ω : Ω) :
      (∑ i : I, partialSumRange Y (n L i) ω * v i) / a L =
      weightedCoordinate v (fun i => normalizedPartialSum P Z ρ L (i.val : ℝ) ω) := by
    simp only [Y, n, a, partialSumRange_centeredLogBlock ϑ P Z hZ hρ1,
      weightedCoordinate, normalizedPartialSum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hvariance : Tendsto (fun L : Set.Ioi (0 : ℝ) => variance
      (fun ω => (∑ i : I, partialSumRange Y (n L i) ω * v i) / a L) P)
      atTop (𝓝 (σ : ℝ)) := by
    have hfun (L : Set.Ioi (0 : ℝ)) :
        (fun ω => (∑ i : I, partialSumRange Y (n L i) ω * v i) / a L) =
        (fun ω => weightedCoordinate v (fun i => normalizedPartialSum P Z ρ L (i.val : ℝ) ω)) :=
      funext (hsum L)
    have hσ : (σ : ℝ) = variance (weightedCoordinate v) (BrownianReal.projectiveFamily I) :=
      Real.coe_toNNReal _ (variance_nonneg _ _)
    rw [hσ]
    simpa only [hfun] using hV ρ hρ I hI v
  have hclt := tendstoInDistribution_weighted_partialSums P atTop Y
    (iIndepFun_centeredLogBlock ϑ P Z hZ hρ1)
    (fun j => (memLp_centeredLogBlock ϑ P Z hZ hρ1 j 2).aemeasurable)
    (integral_centeredLogBlock ϑ P Z hZ hρ1) (2 * Real.log 2)
    (fun j => Filter.Eventually.of_forall (abs_centeredLogBlock_le P Z ρ j)) n a ha v σ hvariance
  have hfamily : (fun L ω => (∑ i : I, partialSumRange Y (n L i) ω * v i) / a L) =
      (fun (L : Set.Ioi (0 : ℝ)) ω => weightedCoordinate v (fun i => normalizedPartialSum P Z ρ L (i.val : ℝ) ω)) := by
    funext L ω
    exact hsum L ω
  rw [hfamily] at hclt
  change TendstoInDistribution
    (fun (L : Set.Ioi (0 : ℝ)) ω => weightedCoordinate v (fun i => normalizedPartialSum P Z ρ L (i.val : ℝ) ω))
    atTop (weightedCoordinate v) (fun _ => P) (BrownianReal.projectiveFamily I)
  have hm : Measurable (weightedCoordinate v) := by unfold weightedCoordinate; fun_prop
  refine ⟨hclt.forall_aemeasurable, hm.aemeasurable, ?_⟩
  have hlimit : (⟨(BrownianReal.projectiveFamily I).map (weightedCoordinate v), inferInstance⟩ :
      ProbabilityMeasure ℝ) = ⟨(gaussianReal 0 σ).map id, inferInstance⟩ := by
    apply Subtype.ext
    change (BrownianReal.projectiveFamily I).map (weightedCoordinate v) = (gaussianReal 0 σ).map id
    rw [Measure.map_id]
    exact map_weightedCoordinate_projectiveFamily I v
  rw [hlimit]
  exact hclt.tendsto

end Critical2DKPZ.Extensions.ScaleLimit
