/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabSmoothedBridge
public import Mathlib.MeasureTheory.Function.L2Space
public import Critical2DKPZ.SHF.Tsai.Cutoff
import Mathlib.Tactic

/-! # Square integrability of bounded deterministic connector products -/

@[expose] public noncomputable section
open MeasureTheory Critical2DKPZ.SHF.Limit
open scoped CompactlySupported ENNReal
namespace Critical2DKPZ.SHF.Flow

/-- Each finite lattice coefficient of a two-block product is square integrable. -/
theorem memLp_smoothedProductSiteCoefficient_two (ϑ : ℝ) (N : ℕ) (s t r u : ℝ)
    (q : (Site × Site) × (Site × Site)) :
    MemLp (fun ω => smoothedProductSiteCoefficient ϑ N s t r u ω q) 2 disorderLaw := by
  have h₁ := Polymer.memLp_pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
    (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1.1 q.1.2
    ((2 : ENNReal) * 2) (by norm_num)
  have h₂ := Polymer.memLp_pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * r))
    (evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * r)) q.2.1 q.2.2
    ((2 : ENNReal) * 2) (by norm_num)
  exact Polymer.memLp_mul_double (2 : ℝ≥0∞)
    (h₁.const_mul ((N : ℝ) / 4)) (h₂.const_mul ((N : ℝ) / 4))

/-- A bounded measurable deterministic connector gives a square-integrable
polymer product at every lattice scale. No time separation is needed. -/
theorem memLp_kernelProductPairing_two (ϑ : ℝ) (N : ℕ) (s t r u : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) (κ : Plane × Plane → ℝ) (hκ : Measurable κ)
    (C : ℝ) (hbound : ∀ p, ‖κ p‖ ≤ C) :
    MemLp (fun ω => kernelProductPairing (polymerMeasure ϑ N s t ω)
      (fun a b => κ (a, b)) (polymerMeasure ϑ N r u ω) Φ) 2 disorderLaw := by
  classical
  by_cases hN : N = 0
  · subst N
    simp only [polymerMeasure_zero_at_zero, kernelProductPairing, Measure.zero_prod, integral_zero_measure]
    exact MemLp.zero
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  obtain ⟨M, hM⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have htest (p : (Plane × Plane) × (Plane × Plane)) :
      ‖Φ (p.1.1, p.2.2) * κ (p.1.2, p.2.1)‖ ≤ M * C := by
    rw [norm_mul]
    exact mul_le_mul (hM _) (hbound _) (norm_nonneg _) hM0
  let Q := smoothedProductBridgeSupport N s t r u Φ
  let c : ((Site × Site) × (Site × Site)) → ℝ := fun q =>
    ∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ (cell N q.2.1 ×ˢ cell N q.2.2),
      Φ (p.1.1, p.2.2) * κ (p.1.2, p.2.1)
      ∂((volume : Measure (Plane × Plane)).prod volume)
  have hsum (ω : Disorder) :
      kernelProductPairing (polymerMeasure ϑ N s t ω) (fun a b => κ (a, b))
        (polymerMeasure ϑ N r u ω) Φ =
      ∑ q ∈ Q, c q * smoothedProductSiteCoefficient ϑ N s t r u ω q := by
    apply kernelProductPairing_polymer_eq_finiteFourCellSum ϑ N hNpos s t r u ω Φ κ hκ
      (M * C) htest Q
    exact fun q hq p hp => smoothedProductBridgeSupport_right ϑ N s t r u Φ κ ω q hq p hp
  have hLp : MemLp (fun ω => ∑ q ∈ Q,
      c q * smoothedProductSiteCoefficient ϑ N s t r u ω q) 2 disorderLaw := by
    apply memLp_finsetSum
    intro q _
    exact (memLp_smoothedProductSiteCoefficient_two ϑ N s t r u q).const_mul (c q)
  exact (memLp_congr_ae (Filter.Eventually.of_forall fun ω => hsum ω)).2 hLp

/-- The same square integrability holds after the two middle spatial cutoffs. -/
theorem memLp_kernelProductCutoffPairing_two (ϑ : ℝ) (N : ℕ) (s t r u : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) (κ : Plane × Plane → ℝ) (hκ : Measurable κ)
    (C R : ℝ) (hbound : ∀ p, ‖κ p‖ ≤ C) :
    MemLp (fun ω => ∫ q, Φ (q.1.1, q.2.2) * κ (q.1.2, q.2.1) *
      Tsai.ballCutoff R q.1.2 * Tsai.ballCutoff R q.2.1 ∂
      ((polymerMeasure ϑ N s t ω).prod (polymerMeasure ϑ N r u ω))) 2 disorderLaw := by
  let κR : Plane × Plane → ℝ := fun p =>
    κ p * Tsai.ballCutoff R p.1 * Tsai.ballCutoff R p.2
  have hC : 0 ≤ C := (norm_nonneg (κ 0)).trans (hbound 0)
  have hm : Measurable κR := by
    exact (hκ.mul ((Tsai.continuous_ballCutoff R).measurable.comp measurable_fst)).mul
      ((Tsai.continuous_ballCutoff R).measurable.comp measurable_snd)
  have hb (p : Plane × Plane) : ‖κR p‖ ≤ C := by
    have h₁ := Tsai.ballCutoff_mem_Icc R p.1
    have h₂ := Tsai.ballCutoff_mem_Icc R p.2
    simp only [κR, norm_mul, Real.norm_eq_abs (Tsai.ballCutoff R p.1),
      Real.norm_eq_abs (Tsai.ballCutoff R p.2), abs_of_nonneg h₁.1, abs_of_nonneg h₂.1]
    calc
      _ ≤ C * 1 * 1 := mul_le_mul
        (mul_le_mul (hbound p) h₁.2 h₁.1 hC) h₂.2 h₂.1 (by positivity)
      _ = C := by rw [mul_one, mul_one]
  have hLp := memLp_kernelProductPairing_two ϑ N s t r u Φ κR hm C hb
  apply (memLp_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).2 hLp
  unfold kernelProductPairing
  apply integral_congr_ae
  filter_upwards [] with q
  dsimp [κR]
  ring

end Critical2DKPZ.SHF.Flow
end
