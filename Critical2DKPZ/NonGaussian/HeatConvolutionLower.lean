/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Uniform positive compact-terminal heat averages -/

@[expose] public noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace Critical2DKPZ.NonGaussian

/-- A positive-time heat average of a nonnegative nonzero compact terminal
has a positive lower bound on every compact set of starting centers.
Integrability of every average is included. -/
theorem exists_pos_heat_convolution_lower {t : ℝ} (ht : 0 < t)
    (φ : C_c(Plane, ℝ)) (hφ : ∀ y, 0 ≤ φ y) (hφ' : φ ≠ 0)
    (K : Set Plane) (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K,
      Integrable (fun y => heatKernel t (y - x) * φ y) ∧
        c ≤ ∫ y, heatKernel t (y - x) * φ y := by
  have hIntφ : Integrable (φ : Plane → ℝ) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  obtain ⟨y₀, hy₀⟩ := DFunLike.ne_iff.mp hφ'
  have hyPos : 0 < φ y₀ := lt_of_le_of_ne (hφ _) (Ne.symm hy₀)
  have hφMean : 0 < ∫ y, φ y := by
    apply (integral_pos_iff_support_of_nonneg hφ hIntφ).mpr
    have hOpen := (isOpen_lt continuous_const φ.continuous).measure_pos volume ⟨y₀, hyPos⟩
    apply hOpen.trans_le
    exact measure_mono (fun y hy => ne_of_gt hy)
  by_cases hKne : K.Nonempty
  · let S : Set (Plane × Plane) := K ×ˢ tsupport (φ : Plane → ℝ)
    have hS : IsCompact S := hK.prod φ.hasCompactSupport
    have hySupp : y₀ ∈ tsupport (φ : Plane → ℝ) := subset_tsupport _ hy₀
    have hSne : S.Nonempty := hKne.prod ⟨y₀, hySupp⟩
    have hCont : Continuous (fun p : Plane × Plane => heatKernel t (p.2 - p.1)) :=
      (continuous_heatKernel t).comp (continuous_snd.sub continuous_fst)
    obtain ⟨p₀, hp₀, hMin⟩ := hS.exists_isMinOn hSne hCont.continuousOn
    let c₀ : ℝ := heatKernel t (p₀.2 - p₀.1)
    have hc₀ : 0 < c₀ := heatKernel_pos ht _
    refine ⟨c₀ * ∫ y, φ y, mul_pos hc₀ hφMean, ?_⟩
    intro x hx
    have hHeat : AEStronglyMeasurable (fun y : Plane => heatKernel t (y - x)) volume :=
      ((continuous_heatKernel t).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    have hHeatBound : ∀ᵐ y : Plane, ‖heatKernel t (y - x)‖ ≤ (2 * Real.pi * t)⁻¹ := by
      exact Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (heatKernel_nonneg ht.le _)]
        exact heatKernel_le_at_zero ht.le _
    have hInt : Integrable (fun y => heatKernel t (y - x) * φ y) :=
      (hIntφ.mul_bdd hHeat hHeatBound).congr
        (Filter.Eventually.of_forall fun _ => mul_comm _ _)
    refine ⟨hInt, ?_⟩
    calc
      c₀ * ∫ y, φ y = ∫ y, c₀ * φ y := (integral_const_mul _ _).symm
      _ ≤ ∫ y, heatKernel t (y - x) * φ y := by
        apply integral_mono (hIntφ.const_mul c₀) hInt
        intro y
        change c₀ * φ y ≤ heatKernel t (y - x) * φ y
        by_cases hy : y ∈ tsupport (φ : Plane → ℝ)
        · exact mul_le_mul_of_nonneg_right ((isMinOn_iff.mp hMin) (x, y) ⟨hx, hy⟩) (hφ y)
        · have hy0 : φ y = 0 := by
            by_contra hne
            exact hy (subset_tsupport _ hne)
          rw [hy0, mul_zero, mul_zero]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    exact False.elim (hKne ⟨x, hx⟩)

end Critical2DKPZ.NonGaussian

end
