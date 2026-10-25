/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Basic
public import Critical2DKPZ.SHF.Flow.KernelProductCutoffUniform
public import Critical2DKPZ.SHF.Tsai.Defs

/-! # Cutoff tails for smoothed polymer products -/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

private theorem compactKernel_gaussian_bound (k : Plane → ℝ) (hk : Continuous k)
    (hkc : HasCompactSupport k) :
    ∃ C c : ℝ, 0 < c ∧ ∀ z, |k z| ≤ C * Real.exp (-c * ‖z‖ ^ 2) := by
  obtain ⟨M, hM⟩ := hk.bounded_above_of_compact_support hkc
  have hMnonneg : 0 ≤ M := (norm_nonneg (k 0)).trans (hM 0)
  obtain ⟨B, hB⟩ := (hkc.image continuous_norm).bddAbove
  let R := max B 0
  have hRnonneg : 0 ≤ R := le_max_right _ _
  refine ⟨M * Real.exp (R ^ 2), 1, by norm_num, ?_⟩
  intro z
  by_cases hkz : k z = 0
  · rw [hkz, abs_zero]
    positivity
  · have hts : z ∈ tsupport k := subset_tsupport k (Function.mem_support.mpr hkz)
    have hnorm : ‖z‖ ≤ R := by
      calc
        ‖z‖ ≤ B := hB (Set.mem_image_of_mem _ hts)
        _ ≤ R := le_max_left _ _
    have hsq : ‖z‖ ^ 2 ≤ R ^ 2 := by
      have hprod : 0 ≤ (R - ‖z‖) * (R + ‖z‖) :=
        mul_nonneg (sub_nonneg.mpr hnorm) (by positivity)
      nlinarith
    calc
      |k z| = ‖k z‖ := by rw [Real.norm_eq_abs]
      _ ≤ M := hM z
      _ = M * 1 := by ring
      _ ≤ M * Real.exp (R ^ 2 - ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (Real.one_le_exp_iff.mpr (sub_nonneg.mpr hsq)) hMnonneg
      _ = (M * Real.exp (R ^ 2)) * Real.exp (-1 * ‖z‖ ^ 2) := by
        calc
          M * Real.exp (R ^ 2 - ‖z‖ ^ 2) =
              M * Real.exp (R ^ 2 + -‖z‖ ^ 2) := by congr 1
          _ = M * (Real.exp (R ^ 2) * Real.exp (-‖z‖ ^ 2)) := by rw [Real.exp_add]
          _ = (M * Real.exp (R ^ 2)) * Real.exp (-1 * ‖z‖ ^ 2) := by
            rw [show Real.exp (-‖z‖ ^ 2) = Real.exp (-1 * ‖z‖ ^ 2) by
              congr 1; ring]
            ring

private theorem heatKernel_gaussian_bound {v : ℝ} (hv : 0 < v) :
    ∃ C c : ℝ, 0 < c ∧ ∀ z, |heatKernel v z| ≤ C * Real.exp (-c * ‖z‖ ^ 2) := by
  refine ⟨(2 * Real.pi * v)⁻¹, (2 * v)⁻¹, inv_pos.mpr (by positivity), ?_⟩
  intro z
  rw [abs_of_nonneg (heatKernel_nonneg hv.le z), heatKernel_eq_exp]

/-- Removing the intermediate-variable cutoffs makes the smoothed-product error small in mean square for compact or positive-time Gaussian connectors. Square integrability follows from `eventually_polymerSubseq_cutoffProduct_sq_bound` and the finite cell expansion. -/
theorem smoothedProduct_cutoff_tail (ϑ : ℝ) {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (htu : t < u) (Φ : C_c(Plane × Plane, ℝ)) (k : Plane → ℝ)
    (hk : (Continuous k ∧ HasCompactSupport k ∧ ∀ x, 0 ≤ k x) ∨
      ∃ v : ℝ, 0 < v ∧ k = heatKernel v) :
    ∀ ε > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ᶠ N : ℕ in atTop,
      ∫ ω, (smoothedProductPairing (polymerMeasure ϑ N s t ω) k
          (polymerMeasure ϑ N t u ω) Φ -
        ∫ q, Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
          ballCutoff R q.1.2 * ballCutoff R q.2.1
          ∂((polymerMeasure ϑ N s t ω).prod (polymerMeasure ϑ N t u ω))) ^ 2
        ∂disorderLaw ≤ ε := by
  let κ : ℕ → Plane → Plane → ℝ := fun _ x y => k (x - y)
  have hκm : ∀ N, Measurable fun q : Plane × Plane => κ N q.1 q.2 := by
    intro N
    rcases hk with ⟨hkc, _, _⟩ | ⟨v, _, hkeq⟩
    · exact hkc.measurable.comp (measurable_fst.sub measurable_snd)
    · change Measurable (fun q : Plane × Plane => k (q.1 - q.2))
      rw [hkeq]
      exact (continuous_heatKernel v).measurable.comp
        (measurable_fst.sub measurable_snd)
  have hκ : ∃ C c : ℝ, 0 < c ∧ ∀ N x y,
      |κ N x y| ≤ C * Real.exp (-c * ‖x - y‖ ^ 2) := by
    rcases hk with ⟨hkc, hksupp, _⟩ | ⟨v, hv, hkeq⟩
    · obtain ⟨C, c, hc, hbound⟩ := compactKernel_gaussian_bound k hkc hksupp
      exact ⟨C, c, hc, fun _ x y => hbound (x - y)⟩
    · obtain ⟨C, c, hc, hbound⟩ := heatKernel_gaussian_bound hv
      refine ⟨C, c, hc, fun _ x y => ?_⟩
      change |k (x - y)| ≤ _
      rw [hkeq]
      exact hbound (x - y)
  have htail := kernelProduct_cutoff_tail ϑ hs hst le_rfl htu Φ κ hκm hκ
  simpa only [smoothedProductPairing, kernelProductPairing, κ] using htail

end Critical2DKPZ.SHF.Flow

end
