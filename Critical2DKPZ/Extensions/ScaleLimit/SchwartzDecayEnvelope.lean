/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzSpectralLp
import Mathlib.Tactic

/-! # Common decay envelopes for positive Schwartz dilations -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A common polynomial envelope for all dilations whose scale is bounded
below by a positive number. -/
theorem schwartz_scaled_decay_envelope (m : SchwartzMap Plane ℂ) (n : ℕ)
    {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, α ≤ q → ∀ ξ : Plane,
      ‖m (q • ξ)‖ ≤ C / (1 + ‖ξ‖) ^ n := by
  let c := max 1 α⁻¹
  have hc : 0 ≤ c := zero_le_one.trans (le_max_left _ _)
  let A := 2 ^ n * (Finset.Iic (n, 0)).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) m
  have hA : 0 ≤ A := mul_nonneg (by positivity) (apply_nonneg _ m)
  refine ⟨c ^ n * A, by positivity, ?_⟩
  intro q hq ξ
  have hq0 : 0 < q := hα.trans_le hq
  have hcq : 1 ≤ c * q := by
    calc
      1 = α⁻¹ * α := (inv_mul_cancel₀ hα.ne').symm
      _ ≤ c * q := mul_le_mul (le_max_right _ _) hq hα.le hc
  have hbase : 1 + ‖ξ‖ ≤ c * (1 + ‖q • ξ‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq0]
    nlinarith only [le_max_left 1 α⁻¹, hcq, norm_nonneg ξ]
  have hh := m.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (n, 0)) le_rfl le_rfl (q • ξ)
  have hdec : (1 + ‖q • ξ‖) ^ n * ‖m (q • ξ)‖ ≤ A := by
    simpa only [norm_iteratedFDeriv_zero] using hh
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖ξ‖) n)).mpr
  calc
    _ = (1 + ‖ξ‖) ^ n * ‖m (q • ξ)‖ := mul_comm _ _
    _ ≤ (c * (1 + ‖q • ξ‖)) ^ n * ‖m (q • ξ)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase n) (norm_nonneg _)
    _ = c ^ n * ((1 + ‖q • ξ‖) ^ n * ‖m (q • ξ)‖) := by rw [mul_pow]; ring
    _ ≤ c ^ n * A := mul_le_mul_of_nonneg_left hdec (by positivity)

/-- A tempered measure integrates the square of a sufficiently high common
polynomial envelope. -/
theorem integrable_polynomial_envelope_sq (ν : Measure Plane) [ν.HasTemperateGrowth]
    {C : ℝ} (hC : 0 ≤ C) :
    Integrable (fun ξ : Plane => (C / (1 + ‖ξ‖) ^ ν.integrablePower) ^ 2) ν := by
  let n := ν.integrablePower
  let B : Plane → ℝ := fun ξ => C / (1 + ‖ξ‖) ^ n
  have hB0 (ξ : Plane) : 0 ≤ B ξ := by dsimp [B]; positivity
  have hB (ξ : Plane) : B ξ ≤ C := by
    apply (div_le_iff₀ (by positivity : 0 < (1 + ‖ξ‖) ^ n)).mpr
    exact le_mul_of_one_le_right hC (one_le_pow₀ (by simp) )
  have hBn (ξ : Plane) : ‖ξ‖ ^ n * B ξ ≤ C := by
    dsimp [B]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < (1 + ‖ξ‖) ^ n)).mpr
    have hpow : ‖ξ‖ ^ n ≤ (1 + ‖ξ‖) ^ n :=
      pow_le_pow_left₀ (norm_nonneg ξ) (by linarith) n
    calc
      _ = C * ‖ξ‖ ^ n := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hC
  have hm : AEStronglyMeasurable (fun ξ : Plane => B ξ ^ 2) ν := by
    have hc : Continuous B := continuous_const.div
      ((continuous_const.add continuous_norm).pow n) (fun _ => by positivity)
    exact (hc.pow 2).aestronglyMeasurable
  have hInt : Integrable (fun ξ : Plane => ‖ξ‖ ^ 0 * ‖B ξ ^ 2‖) ν := by
    apply integrable_of_le_of_pow_mul_le (k := 0) (C₁ := C ^ 2) (C₂ := C ^ 2) _ _ hm
    · intro ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (hB0 ξ) hC).mpr (hB ξ)
    · intro ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), zero_add]
      change ‖ξ‖ ^ n * B ξ ^ 2 ≤ C ^ 2
      calc
        _ = (‖ξ‖ ^ n * B ξ) * B ξ := by ring
        _ ≤ C * C := mul_le_mul (hBn ξ) (hB ξ) (hB0 ξ) hC
        _ = _ := (pow_two _).symm
  have heq : (fun ξ : Plane => ‖ξ‖ ^ 0 * ‖B ξ ^ 2‖) = fun ξ => B ξ ^ 2 := by
    funext ξ
    rw [pow_zero, one_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (B ξ))]
  rw [heq] at hInt
  exact hInt

end Critical2DKPZ.Extensions.ScaleLimit
