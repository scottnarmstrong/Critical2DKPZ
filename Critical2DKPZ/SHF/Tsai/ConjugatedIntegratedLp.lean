/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedIntegratedRows
public import Critical2DKPZ.SHF.Tsai.ConjugatedSchur
import Mathlib.Tactic

/-! # The time-integrated distinct-pair swap on every finite `Lᵖ` space -/

@[expose] public noncomputable section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The unweighted time-integrated swapping kernel is bounded on `Lᵖ` for
all `1 < p < ∞`, using two fractional powers of the canonical Schur weight. -/
theorem exists_integratedSwappingKernel_lp_bound {n : ℕ} (α β : CollisionPair n)
    (hne : α ≠ β) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : FusedConfiguration β → ℝ≥0∞, Measurable f →
      (∫⁻ z : FusedConfiguration α,
        (∫⁻ w : FusedConfiguration β, integratedSwappingKernel α β z w * f w) ^ p) ≤
        C ^ p * ∫⁻ w : FusedConfiguration β, f w ^ p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  let b : ℝ := 1 / (2 * p)
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b < 1 := by
    dsimp [b]
    exact (div_lt_iff₀ (by positivity : 0 < 2 * p)).mpr (by linarith)
  have hb' : 0 < b * (p - 1) := mul_pos hb hpm
  have hb1' : b * (p - 1) < 1 := by
    dsimp [b]
    rw [div_mul_eq_mul_div, one_mul]
    exact (div_lt_iff₀ (by positivity : 0 < 2 * p)).mpr (by linarith)
  let K : FusedConfiguration α → FusedConfiguration β → ℝ≥0∞ := integratedSwappingKernel α β
  let v : FusedConfiguration α → ℝ≥0∞ := fun z =>
    heatPotential ((collisionEmbedding α z) β.1.2 - (collisionEmbedding α z) β.1.1) ^ b
  let w : FusedConfiguration β → ℝ≥0∞ := fun y =>
    heatPotential ((collisionEmbedding β y) α.1.1 - (collisionEmbedding β y) α.1.2) ^ b
  let A : ℝ≥0∞ := fractionalPotentialRowConstant b
  let B : ℝ≥0∞ := fractionalPotentialRowConstant (b * (p - 1))
  have hA : A ≠ ⊤ := fractionalPotentialRowConstant_ne_top hb hb1
  have hB : B ≠ ⊤ := fractionalPotentialRowConstant_ne_top hb' hb1'
  have hv : Measurable v := (measurable_heatPotential.comp
    (((measurable_pi_apply β.1.2).comp (measurable_collisionEmbedding α)).sub
      ((measurable_pi_apply β.1.1).comp (measurable_collisionEmbedding α)))).pow_const b
  have hw : Measurable w := (measurable_heatPotential.comp
    (((measurable_pi_apply α.1.1).comp (measurable_collisionEmbedding β)).sub
      ((measurable_pi_apply α.1.2).comp (measurable_collisionEmbedding β)))).pow_const b
  have hwfinite : ∀ᵐ y : FusedConfiguration β, w y ≠ 0 ∧ w y ≠ ⊤ := by
    filter_upwards [heatPotential_swappingWeight_ne_top_ae α β hne] with y hy
    exact ⟨(ENNReal.rpow_eq_zero_iff_of_pos hb).not.mpr (ne_of_gt (heatPotential_pos _)),
      ENNReal.rpow_ne_top_of_nonneg hb.le hy⟩
  have hrow (z : FusedConfiguration α) : (∫⁻ y, K z y * w y) ≤ A * v z :=
    lintegral_integratedSwapping_fractionalPotential_row_le α β hne hb hb1 z
  have hcol (y : FusedConfiguration β) :
      (∫⁻ z, K z y * v z ^ (p - 1)) ≤ B * w y ^ (p - 1) := by
    have hs (z : FusedConfiguration α) : K z y = integratedSwappingKernel β α y z := by
      unfold K integratedSwappingKernel
      apply lintegral_congr
      intro t
      exact congrArg ENNReal.ofReal (swappingKernel_symm α β t z y)
    have hvEq (z : FusedConfiguration α) : v z ^ (p - 1) =
        heatPotential ((collisionEmbedding α z) β.1.1 -
          (collisionEmbedding α z) β.1.2) ^ (b * (p - 1)) := by
      dsimp [v]
      rw [← ENNReal.rpow_mul, heatPotential_sub_swap]
    have hwEq : w y ^ (p - 1) =
        heatPotential ((collisionEmbedding β y) α.1.2 -
          (collisionEmbedding β y) α.1.1) ^ (b * (p - 1)) := by
      dsimp [w]
      rw [← ENNReal.rpow_mul, heatPotential_sub_swap]
    calc
      _ = ∫⁻ z : FusedConfiguration α, integratedSwappingKernel β α y z *
          heatPotential ((collisionEmbedding α z) β.1.1 -
            (collisionEmbedding α z) β.1.2) ^ (b * (p - 1)) := by
        apply lintegral_congr
        intro z
        rw [hs z, hvEq z]
      _ ≤ B * heatPotential ((collisionEmbedding β y) α.1.2 -
          (collisionEmbedding β y) α.1.1) ^ (b * (p - 1)) :=
        lintegral_integratedSwapping_fractionalPotential_row_le β α hne.symm hb' hb1' y
      _ = _ := by rw [hwEq]
  let M : ℝ≥0∞ := A ^ (p - 1) * B
  have hM : M ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hpm.le hA) hB
  refine ⟨M ^ (1 / p : ℝ), ENNReal.rpow_ne_top_of_nonneg (by positivity) hM, ?_⟩
  intro f hf
  have hh := lintegral_kernel_rpow_le_power_schur volume volume hp
    (measurable_integratedSwappingKernel α β) hv hw hwfinite hA hB hrow hcol hf
  simpa only [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one] using hh

end Critical2DKPZ.SHF.Tsai

end
