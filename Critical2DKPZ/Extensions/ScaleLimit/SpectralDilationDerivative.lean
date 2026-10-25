/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralDilationContinuity
public import Critical2DKPZ.Extensions.ScaleLimit.L2DominatedDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # Radius derivatives of spectral Schwartz shapes in L2 -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The scalar radial derivative after applying a fixed frequency multiplier. -/
theorem hasDerivAt_multiplied_schwartz_radial (A : Plane → ℂ)
    (m : SchwartzMap Plane ℂ) (ξ : Plane) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun t : ℝ => A ξ * m (t • ξ))
      (r⁻¹ • (A ξ * radialSchwartzDerivative m (r • ξ))) r := by
  have hh := (hasDerivAt_schwartz_radial m ξ hr).const_mul (A ξ)
  rw [mul_smul_comm] at hh
  exact hh

/-- Differentiation of a spectral Schwartz shape under a fixed measurable
contraction. The slope bound is uniform on each positive radius half-line. -/
theorem hasDerivAt_spectralMultipliedDilate (ν : Measure Plane) [ν.HasTemperateGrowth]
    (A : Plane → ℂ) (hAm : Measurable A) (hAn : ∀ ξ, ‖A ξ‖ ≤ 1)
    (m : SchwartzMap Plane ℂ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (spectralMultipliedDilate ν A hAm hAn m)
      (r⁻¹ • spectralMultipliedDilate ν A hAm hAn (radialSchwartzDerivative m) r) r := by
  let α := r / 2
  have hα : 0 < α := by dsimp [α]; positivity
  have hαr : α < r := by dsimp [α]; linarith
  let m' := radialSchwartzDerivative m
  obtain ⟨C, hC, henv⟩ := schwartz_scaled_decay_envelope m' ν.integrablePower hα
  let B : Plane → ℝ := fun ξ => C / (1 + ‖ξ‖) ^ ν.integrablePower
  let M : Plane → ℝ := fun ξ => α⁻¹ * B ξ
  have hB0 (ξ : Plane) : 0 ≤ B ξ := by dsimp [B]; positivity
  have hM0 (ξ : Plane) : 0 ≤ M ξ := mul_nonneg (inv_pos.mpr hα).le (hB0 ξ)
  have hInt : Integrable (fun ξ => 4 * M ξ ^ 2) ν := by
    have hh := (integrable_polynomial_envelope_sq ν hC).const_mul (4 * α⁻¹ ^ 2)
    convert hh using 1
    funext ξ
    dsimp [M, B]
    ring
  let f := fun (q : ℝ) (ξ : Plane) => A ξ * m (q • ξ)
  let g := fun (q : ℝ) (ξ : Plane) => q⁻¹ • (A ξ * m' (q • ξ))
  have hscalar (q : ℝ) (hq : α ≤ q) (ξ : Plane) :
      HasDerivAt (fun t => f t ξ) (g q ξ) q :=
    hasDerivAt_multiplied_schwartz_radial A m ξ (hα.trans_le hq).ne'
  have hnorm (q : ℝ) (hq : α ≤ q) (ξ : Plane) : ‖g q ξ‖ ≤ M ξ := by
    have hq0 := hα.trans_le hq
    have hn : ‖A ξ * m' (q • ξ)‖ ≤ B ξ := by
      rw [norm_mul]
      exact ((mul_le_mul_of_nonneg_right (hAn ξ) (norm_nonneg _)).trans_eq (one_mul _)).trans (henv q hq ξ)
    change ‖q⁻¹ • (A ξ * m' (q • ξ))‖ ≤ α⁻¹ * B ξ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq0)]
    exact mul_le_mul ((inv_le_inv₀ hq0 hα).mpr hq) hn (norm_nonneg _) (inv_pos.mpr hα).le
  have hG : ((r⁻¹ • spectralMultipliedDilate ν A hAm hAn m' r : Lp ℂ 2 ν) : Plane → ℂ) =ᵐ[ν]
      g r := by
    filter_upwards [Lp.coeFn_smul r⁻¹ (spectralMultipliedDilate ν A hAm hAn m' r),
      spectralMultipliedDilate_ae_eq ν A hAm hAn m' hr.ne'] with ξ hs hf
    change _ = r⁻¹ • spectralMultipliedDilate ν A hAm hAn m' r ξ at hs
    rw [hs, hf]
  apply hasDerivAt_L2_of_dominated_slope ν (spectralMultipliedDilate ν A hAm hAn m)
    (r⁻¹ • spectralMultipliedDilate ν A hAm hAn m' r) f (g r) r _
    (spectralMultipliedDilate_ae_eq ν A hAm hAn m hr.ne') hG hInt _
    (Eventually.of_forall (hscalar r hαr.le))
  · filter_upwards [eventually_ge_nhds hαr] with q hq
    exact spectralMultipliedDilate_ae_eq ν A hAm hAn m (hα.trans_le hq).ne'
  · filter_upwards [(eventually_ge_nhds hαr).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with q hq hqr
    have hqr' : q ≠ r := hqr
    exact Eventually.of_forall fun ξ => by
      have hdiff : ‖f q ξ - f r ξ‖ ≤ M ξ * ‖q - r‖ :=
        Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun t ht => (hscalar t ht ξ).hasDerivWithinAt) (fun t ht => hnorm t ht ξ)
          (convex_Ici α) hαr.le hq
      have hsl : ‖slope (fun t => f t ξ) r q‖ ≤ M ξ := by
        rw [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv]
        calc
          _ ≤ |q - r|⁻¹ * (M ξ * |q - r|) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            simpa only [Real.norm_eq_abs] using hdiff
          _ = M ξ := by field_simp [sub_ne_zero.mpr hqr']
      have hh := (norm_sub_le (slope (fun t => f t ξ) r q) (g r ξ)).trans
        (add_le_add hsl (hnorm r hαr.le ξ))
      nlinarith only [hh, norm_nonneg (slope (fun t => f t ξ) r q - g r ξ), hM0 ξ]

end Critical2DKPZ.Extensions.ScaleLimit
