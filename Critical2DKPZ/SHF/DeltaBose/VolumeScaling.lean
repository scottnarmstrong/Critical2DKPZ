/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.CollisionScaling
public import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-! # Positive-integral Jacobians for time and collision-coordinate dilations -/

public section

open MeasureTheory Measure Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Change of variables under a positive scalar dilation, without an integrability assumption. -/
theorem lintegral_comp_smul_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsAddHaarMeasure (volume : Measure E)] {c : ℝ} (hc : 0 < c) (F : E → ℝ≥0∞) :
    (∫⁻ x : E, F (c • x)) = ENNReal.ofReal ((c ^ Module.finrank ℝ E)⁻¹) * ∫⁻ x : E, F x := by
  let e := (Homeomorph.smul (Units.mk0 c hc.ne') : E ≃ₜ E).toMeasurableEquiv
  have he : (∫⁻ x : E, F (c • x)) = ∫⁻ x : E, F x ∂Measure.map (fun x : E => c • x) volume :=
    (lintegral_map_equiv F e).symm
  rw [he, map_addHaar_smul volume hc.ne', lintegral_smul_measure]
  rw [abs_of_pos (inv_pos.mpr (pow_pos hc _)), smul_eq_mul]

/-- The time Jacobian on an arbitrary open interval. -/
theorem lintegral_Ioo_mul {a : ℝ} (ha : 0 < a) (l r : ℝ) (F : ℝ → ℝ≥0∞) :
    (∫⁻ u in Ioo (a * l) (a * r), F u) =
      ENNReal.ofReal a * ∫⁻ u in Ioo l r, F (a * u) := by
  have h := lintegral_comp_smul_pos ha ((Ioo (a * l) (a * r)).indicator F)
  have he : (fun u : ℝ => (Ioo (a * l) (a * r)).indicator F (a • u)) =
      (Ioo l r).indicator (fun u => F (a * u)) := by
    funext u
    simp only [smul_eq_mul, indicator, mem_Ioo, mul_lt_mul_iff_right₀ ha]
  rw [he, lintegral_indicator measurableSet_Ioo, lintegral_indicator measurableSet_Ioo] at h
  simp only [Module.finrank_self, pow_one] at h
  have hi : ENNReal.ofReal a * ENNReal.ofReal a⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one]
  calc (∫⁻ u in Ioo (a * l) (a * r), F u)
      = (ENNReal.ofReal a * ENNReal.ofReal a⁻¹) * ∫⁻ u in Ioo (a * l) (a * r), F u := by rw [hi, one_mul]
    _ = ENNReal.ofReal a * ∫⁻ u in Ioo l r, F (a * u) := by rw [mul_assoc, ← h]

/-- The spatial Jacobian on a collision space. -/
theorem lintegral_fused_sqrt {n : ℕ} (α : CollisionPair n) {a : ℝ} (ha : 0 < a)
    (F : FusedConfiguration α → ℝ≥0∞) :
    (∫⁻ z : FusedConfiguration α, F (mapFused (fun v => Real.sqrt a • v) z)) =
      ENNReal.ofReal ((a ^ (n - 1))⁻¹) * ∫⁻ z : FusedConfiguration α, F z := by
  have : IsAddHaarMeasure (volume : Measure Plane) := by
    rw [← (EuclideanSpace.basisFun (Fin 2) ℝ).addHaar_eq_volume]
    infer_instance
  have : IsAddHaarMeasure (volume : Measure (Spectator α → Plane)) := by infer_instance
  have : IsAddHaarMeasure (volume : Measure (FusedConfiguration α)) := by
    change IsAddHaarMeasure ((volume : Measure Plane).prod (volume : Measure (Spectator α → Plane)))
    infer_instance
  have h := lintegral_comp_smul_pos (E := FusedConfiguration α) (Real.sqrt_pos.mpr ha) F
  rw [finrank_fusedConfiguration, pow_mul, Real.sq_sqrt ha.le] at h
  exact h

/-- The equivalent forward-Jacobian form for changing spatial collision variables. -/
theorem lintegral_fused_scale {n : ℕ} (α : CollisionPair n) {a : ℝ} (ha : 0 < a)
    (F : FusedConfiguration α → ℝ≥0∞) :
    (∫⁻ z : FusedConfiguration α, F z) = ENNReal.ofReal (a ^ (n - 1)) *
      ∫⁻ z : FusedConfiguration α, F (mapFused (fun v => Real.sqrt a • v) z) := by
  have h := lintegral_fused_sqrt α ha F
  have hi : ENNReal.ofReal (a ^ (n - 1)) * ENNReal.ofReal ((a ^ (n - 1))⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_pos ha _).le, mul_inv_cancel₀ (pow_pos ha _).ne', ENNReal.ofReal_one]
  rw [h, ← mul_assoc, hi, one_mul]

/-- Positive time dilation on an interval beginning at zero. -/
theorem lintegral_Ioo_zero_mul {a : ℝ} (ha : 0 < a) (h : ℝ) (F : ℝ → ℝ≥0∞) :
    (∫⁻ u in Ioo 0 (a * h), F u) = ENNReal.ofReal a * ∫⁻ u in Ioo 0 h, F (a * u) := by
  simpa only [mul_zero] using lintegral_Ioo_mul ha 0 h F

/-- The two free collision-coordinate Jacobians, in the order used by a diagram. -/
theorem lintegral_fused_scale_pair {n : ℕ} (α : CollisionPair n) {a : ℝ} (ha : 0 < a)
    (F : FusedConfiguration α → FusedConfiguration α → ℝ≥0∞) :
    (∫⁻ z : FusedConfiguration α, ∫⁻ w : FusedConfiguration α, F z w) =
      ENNReal.ofReal (a ^ (n - 1)) * (ENNReal.ofReal (a ^ (n - 1)) *
        ∫⁻ z : FusedConfiguration α, ∫⁻ w : FusedConfiguration α,
          F (mapFused (fun v => Real.sqrt a • v) z) (mapFused (fun v => Real.sqrt a • v) w)) := by
  rw [lintegral_fused_scale α ha (fun z => ∫⁻ w : FusedConfiguration α, F z w)]
  congr 1
  calc (∫⁻ z : FusedConfiguration α, ∫⁻ w : FusedConfiguration α,
        F (mapFused (fun v => Real.sqrt a • v) z) w)
      = ∫⁻ z : FusedConfiguration α, ENNReal.ofReal (a ^ (n - 1)) *
          ∫⁻ w : FusedConfiguration α, F (mapFused (fun v => Real.sqrt a • v) z)
            (mapFused (fun v => Real.sqrt a • v) w) := by
        apply lintegral_congr
        intro z
        exact lintegral_fused_scale α ha _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Critical2DKPZ.DeltaBose
