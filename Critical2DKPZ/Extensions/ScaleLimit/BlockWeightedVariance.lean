/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BlockProcess
public import Critical2DKPZ.Extensions.ScaleLimit.BrownianProjections
import Critical2DKPZ.Extensions.ScaleLimit.WeightedMoments
import Mathlib.Tactic

/-! # Covariance and projected variance limits of the normalized block process -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The covariance of the centered block process converges to the Brownian
minimum kernel at every pair of positive scale times. -/
theorem normalizedPartialSum_covariance_limit (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ s s' : ℝ, 0 < s → 0 < s' →
      Tendsto (fun L : Set.Ioi (0 : ℝ) => covariance
        (normalizedPartialSum P Z ρ L s) (normalizedPartialSum P Z ρ L s') P)
        atTop (𝓝 (min s s')) := by
  obtain ⟨ρ₀, hρ₀, hC⟩ := partialSum_covariance ϑ P Z hZ
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ s s' hs hs'
  have hρ1 : 1 < ρ := hρ₀.trans_le hρ
  by_cases hss' : s ≤ s'
  · have h := hC ρ hρ s s' hs hss'
    simpa only [covariance_normalizedPartialSum ϑ P Z hZ hρ1, min_eq_left hss'] using h
  · have hs's : s' ≤ s := le_of_not_ge hss'
    have h := hC ρ hρ s' s hs' hs's
    have h' : Tendsto (fun L : Set.Ioi (0 : ℝ) => covariance
        (normalizedPartialSum P Z ρ L s') (normalizedPartialSum P Z ρ L s) P)
        atTop (𝓝 s') := by
      simpa only [covariance_normalizedPartialSum ϑ P Z hZ hρ1] using h
    simpa only [covariance_comm, min_eq_right hs's] using h'

/-- Every finite scalar projection has the variance of the corresponding
Brownian Gaussian projection in the limit. -/
theorem weightedPartialSum_variance_tendsto (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ I : Finset ℝ≥0,
      (∀ i ∈ I, 0 < i) → ∀ v : I → ℝ,
      Tendsto (fun L : Set.Ioi (0 : ℝ) => variance
        (fun ω => weightedCoordinate v (fun i => normalizedPartialSum P Z ρ L (i.val : ℝ) ω)) P)
        atTop (𝓝 (variance (weightedCoordinate v) (BrownianReal.projectiveFamily I))) := by
  obtain ⟨ρ₀, hρ₀, hC⟩ := normalizedPartialSum_covariance_limit ϑ P Z hZ
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ I hI v
  have hρ1 : 1 < ρ := hρ₀.trans_le hρ
  have hc (i j : I) : Tendsto (fun L : Set.Ioi (0 : ℝ) => covariance
      (normalizedPartialSum P Z ρ L (i.val : ℝ)) (normalizedPartialSum P Z ρ L (j.val : ℝ)) P)
      atTop (𝓝 ((min i.val j.val : ℝ≥0) : ℝ)) := by
    simpa only [NNReal.coe_min] using hC ρ hρ (i.val : ℝ) (j.val : ℝ)
      (by exact_mod_cast hI i.val i.property) (by exact_mod_cast hI j.val j.property)
  have hlim : Tendsto (fun L : Set.Ioi (0 : ℝ) => ∑ i : I, ∑ j : I,
      covariance (normalizedPartialSum P Z ρ L (i.val : ℝ))
        (normalizedPartialSum P Z ρ L (j.val : ℝ)) P * v i * v j) atTop
      (𝓝 (∑ i : I, ∑ j : I, ((min i.val j.val : ℝ≥0) : ℝ) * v i * v j)) :=
    tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => ((hc i j).mul_const (v i)).mul_const (v j)))
  have hcalc (L : Set.Ioi (0 : ℝ)) : variance
      (fun ω => weightedCoordinate v (fun i => normalizedPartialSum P Z ρ L (i.val : ℝ) ω)) P =
      ∑ i : I, ∑ j : I, covariance (normalizedPartialSum P Z ρ L (i.val : ℝ))
        (normalizedPartialSum P Z ρ L (j.val : ℝ)) P * v i * v j := by
    exact variance_weightedCoordinate P (fun i : I => normalizedPartialSum P Z ρ L (i.val : ℝ))
      (fun i => memLp_normalizedPartialSum ϑ P Z hZ hρ1 L i.val) v
  have ht : (∑ i : I, ∑ j : I, ((min i.val j.val : ℝ≥0) : ℝ) * v i * v j) =
      variance (weightedCoordinate v) (BrownianReal.projectiveFamily I) := by
    rw [variance_weightedCoordinate_projectiveFamily]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [ht] at hlim
  exact hlim.congr (fun L => (hcalc L).symm)

end Critical2DKPZ.Extensions.ScaleLimit
