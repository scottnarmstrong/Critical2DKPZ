/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedPotentialOrigin
public import Critical2DKPZ.SHF.DeltaBose.PotentialFusedRows
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-! # Fractional powers of the canonical swapping Schur weight -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Hölder's inequality for a fractional moment, retaining the total mass
so that it applies directly to one Gaussian swapping row. -/
theorem lintegral_fractional_power_le {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    {f : Y → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ^ b ∂ν) ≤ (∫⁻ y, f y ∂ν) ^ b * (ν univ) ^ (1 - b) := by
  have hpq := Real.HolderConjugate.inv_one_sub_inv hb hb1
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq
    (hf.pow_const b).aemeasurable (g := fun _ => 1) measurable_const.aemeasurable
  simpa only [Pi.mul_apply, mul_one, ← ENNReal.rpow_mul, mul_inv_cancel₀ hb.ne',
    ENNReal.rpow_one, one_div, inv_inv, ENNReal.one_rpow, lintegral_one] using hh

/-- Fractional powers of the collision potential satisfy a Gaussian row bound
with the corresponding fractional half-time rate. -/
theorem lintegral_swapping_fractionalPotential_row_le {n : ℕ}
    (α β : CollisionPair n) (hne : α ≠ β) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    {t : ℝ} (ht : 0 < t) (z : FusedConfiguration α) :
    (∫⁻ w : FusedConfiguration β, ENNReal.ofReal (swappingKernel α β t z w) *
      heatPotential ((collisionEmbedding β w) α.1.1 - (collisionEmbedding β w) α.1.2) ^ b) ≤
      heatPotentialRowBound t ^ b * ENNReal.ofReal (heatKernel (2 * t)
        ((collisionEmbedding α z) β.1.2 - (collisionEmbedding α z) β.1.1)) := by
  let k : FusedConfiguration β → ℝ≥0∞ := fun w => ENNReal.ofReal (swappingKernel α β t z w)
  let W : FusedConfiguration β → ℝ≥0∞ := fun w =>
    heatPotential ((collisionEmbedding β w) α.1.1 - (collisionEmbedding β w) α.1.2)
  let G : ℝ≥0∞ := ENNReal.ofReal (heatKernel (2 * t)
    ((collisionEmbedding α z) β.1.2 - (collisionEmbedding α z) β.1.1))
  have hk : Measurable k := by
    exact (((measurable_swappingKernel α β).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).ennreal_ofReal)
  have hW : Measurable W := by
    exact measurable_heatPotential.comp
      (((measurable_pi_apply α.1.1).comp (measurable_collisionEmbedding β)).sub
        ((measurable_pi_apply α.1.2).comp (measurable_collisionEmbedding β)))
  have hmass : (∫⁻ w, k w) = G := by
    change (∫⁻ w, ENNReal.ofReal (incomingKernel β t w (collisionEmbedding α z))) = _
    exact lintegral_incomingKernel_fused β ht _
  have hrow : (∫⁻ w, k w * W w) ≤ heatPotentialRowBound t * G :=
    lintegral_swappingPotential_row_le α β hne ht z
  have hfrac := lintegral_fractional_power_le (volume.withDensity k) hb hb1 hW
  rw [lintegral_withDensity_eq_lintegral_mul volume hk (hW.pow_const b),
    lintegral_withDensity_eq_lintegral_mul volume hk hW,
    withDensity_apply k MeasurableSet.univ, setLIntegral_univ, hmass] at hfrac
  simp only [Pi.mul_apply] at hfrac
  change (∫⁻ w, k w * W w ^ b) ≤ heatPotentialRowBound t ^ b * G
  calc
    _ ≤ (∫⁻ w, k w * W w) ^ b * G ^ (1 - b) := hfrac
    _ ≤ (heatPotentialRowBound t * G) ^ b * G ^ (1 - b) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hrow hb.le) le_rfl
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hb.le, mul_assoc,
        ← ENNReal.rpow_add_of_nonneg _ _ hb.le (by linarith : 0 ≤ 1 - b)]
      simp only [add_sub_cancel, ENNReal.rpow_one]

end Critical2DKPZ.SHF.Tsai

end
