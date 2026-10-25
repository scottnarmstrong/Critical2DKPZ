/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.WeightedRemainderControl
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith

/-! # Weighted primitive bounds with no loss in the length of the window -/

public section

open MeasureTheory Filter

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A curve given by an integral primitive obeys a bound uniform over its
whole interval. The derivative enters through weighted Cauchy–Schwarz. -/
theorem primitive_sq_le_weighted (u v g : ℝ → ℝ) {α β : ℝ}
    (hprim : ∀ r ∈ Set.Icc α β, u r = u α + ∫ t in Set.Icc α r, v t)
    (hv : IntegrableOn v (Set.Icc α β)) (hg : IntegrableOn g (Set.Icc α β))
    (hq : IntegrableOn (fun t => v t ^ 2 / g t) (Set.Icc α β))
    (hpos : ∀ᵐ t ∂volume.restrict (Set.Icc α β), 0 < g t)
    (hG : 0 < ∫ t in Set.Icc α β, g t) {r : ℝ} (hr : r ∈ Set.Icc α β) :
    u r ^ 2 ≤ 2 * u α ^ 2 + 2 * (∫ t in Set.Icc α β, g t) *
      (∫ t in Set.Icc α β, v t ^ 2 / g t) := by
  let J := ∫ t in Set.Icc α β, |v t|
  have hJ : 0 ≤ J := integral_nonneg fun _ => abs_nonneg _
  have hsub : Set.Icc α r ⊆ Set.Icc α β :=
    fun t ht => ⟨ht.1, ht.2.trans hr.2⟩
  have hi : |∫ t in Set.Icc α r, v t| ≤ J := by
    calc
      _ ≤ ∫ t in Set.Icc α r, |v t| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun t : ℝ => v t) (μ := volume.restrict (Set.Icc α r))
      _ ≤ J := setIntegral_mono_set hv.abs
        (Eventually.of_forall fun t => abs_nonneg _) (Eventually.of_forall hsub)
  have hu : |u r| ≤ |u α| + J := by
    rw [hprim r hr]
    exact (abs_add_le _ _).trans (add_le_add (le_refl _) hi)
  have hs := (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) hJ)).mpr hu
  have hcs : J ^ 2 ≤ (∫ t in Set.Icc α β, g t) *
      (∫ t in Set.Icc α β, v t ^ 2 / g t) := by
    have hq' : IntegrableOn (fun t => |v t| ^ 2 / g t) (Set.Icc α β) := by
      simpa only [sq_abs] using hq
    simpa only [sq_abs, J] using integral_sq_le_weighted
      (volume.restrict (Set.Icc α β)) (fun t => |v t|) g hv.abs hg hq' hpos hG
  nlinarith only [hs, hcs, sq_abs (u r), sq_abs (u α), sq_nonneg (|u α| - J)]

/-- The inverse-square derivative weight is integrable on the full half-line,
with total mass `a/α`, independent of the upper endpoint of a window. -/
theorem remainder_weight_integral {a α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun r : ℝ => a / r ^ 2) (Set.Ioi α) ∧
      (∫ r : ℝ in Set.Ioi α, a / r ^ 2) = a / α := by
  have hi : IntegrableOn (fun r : ℝ => (r ^ 2)⁻¹) (Set.Ioi α) := by
    simpa only [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg_natCast,
      zpow_neg, zpow_natCast] using
        integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hα
  have he : (∫ r : ℝ in Set.Ioi α, (r ^ 2)⁻¹) = α⁻¹ := by
    have hh := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hα
    norm_num [Real.rpow_neg_one] at hh
    exact hh
  refine ⟨?_, ?_⟩
  · change Integrable (fun r : ℝ => a / r ^ 2) (volume.restrict (Set.Ioi α))
    have hi' : Integrable (fun r : ℝ => a * (r ^ 2)⁻¹) (volume.restrict (Set.Ioi α)) :=
      hi.const_mul a
    simpa only [div_eq_mul_inv] using hi'
  · simp only [div_eq_mul_inv]
    rw [integral_const_mul, he]


end Critical2DKPZ.Extensions.ScaleLimit
