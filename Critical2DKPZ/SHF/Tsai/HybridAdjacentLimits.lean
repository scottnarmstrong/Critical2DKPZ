/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ThreeBlockMergeLimits
public import Critical2DKPZ.SHF.Tsai.Hybrid
import Critical2DKPZ.SHF.Tsai.HeatMollifier

/-! # Identifying the two interior hybrid limits

The original middle increment merges with the suffix, and the replacement
middle increment merges with the prefix. Thus the adjacent hybrid values
and the two three-block expectation families have the same respective limits.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Adjacent interior hybrid values are the limits of the original and replaced three-block nonlinear expectations. -/
theorem exists_hybrid_adjacent_joint_limits {θ : ℝ} (D : Set ℝ) {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s a b t : ℝ} (hs : s ∈ D) (ha : a ∈ D) (hb : b ∈ D) (ht : t ∈ D)
    (hsa : s < a) (hab : a < b) (hbt : b < t) {m r : ℕ}
    (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH) :
    ∃ La Lb : ℝ,
      Tendsto (fun ℓ => hybridValue P P' Z Z' s t g g' H a ℓ) atTop (𝓝 La) ∧
      Tendsto (fun ℓ => hybridValue P P' Z Z' s t g g' H b ℓ) atTop (𝓝 Lb) ∧
      Tendsto (fun q : ℕ × ℕ => ∫ ω, H (threeBlockPairing
        ![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z a b ω.2, fun ω => Z b t ω.2]
        heatMollifier g g' q.1 q.2 ω) ∂P'.prod P) atTop (𝓝 La) ∧
      Tendsto (fun q : ℕ × ℕ => ∫ ω, H (threeBlockPairing
        ![fun ω : Ω' × Ω => Z' s a ω.1, fun ω => Z' a b ω.1, fun ω => Z b t ω.2]
        heatMollifier g g' q.1 q.2 ω) ∂P'.prod P) atTop (𝓝 Lb) := by
  obtain ⟨La, hJointA, hA⟩ := exists_integral_threeBlockPairing_merge_right_limit D P P' Z hZ
    (Z' s a) (sub_pos.2 hsa) (hZ'.hasDeltaBoseMoments hs ha hsa)
    ha hb ht hab hbt heatMollifier isL2ApplicableMollifier_heatMollifier g g' H hH CH hCH
  obtain ⟨Lb, hJointB, hB⟩ := exists_integral_threeBlockPairing_merge_left_limit D P P' Z' hZ'
    (Z b t) (sub_pos.2 hbt) (hZ.hasDeltaBoseMoments hb ht hbt)
    hs ha hb hsa hab heatMollifier isL2ApplicableMollifier_heatMollifier g g' H hH CH hCH
  refine ⟨La, Lb, ?_, ?_, hJointA, hJointB⟩
  · simp only [hybridValue, ite_eq_right (ne_of_gt hsa),
      ite_eq_right (ne_of_lt (hab.trans hbt))]
    change Tendsto (fun ℓ => ∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
      ∂smoothedProductMeasure (Z' s a ω.1) (heatMollifier ℓ) (Z a t ω.2)) ∂P'.prod P) atTop (𝓝 La)
    exact hA
  · simp only [hybridValue, ite_eq_right (ne_of_gt (hsa.trans hab)),
      ite_eq_right (ne_of_lt hbt)]
    change Tendsto (fun ℓ => ∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
      ∂smoothedProductMeasure (Z' s b ω.1) (heatMollifier ℓ) (Z b t ω.2)) ∂P'.prod P) atTop (𝓝 Lb)
    exact hB

end Critical2DKPZ.SHF.Tsai

end
