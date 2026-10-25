/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.LaplaceComposition
import Mathlib.Tactic

/-! # Positive-kernel Laplace averaging on a short time interval -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A pointwise time comparison controls a kernel by its Laplace average.
The averaging interval may shrink with the rate, retaining the endpoint
power needed for a bound uniform near time zero. -/
theorem le_laplaceTimeKernel_of_local_comparison {X Y : Type*} (K : TimeKernel X Y)
    {rate t δ : ℝ} (hrate : 0 ≤ rate) (ht : 0 < t) (hδ : 0 < δ)
    {C : ℝ≥0∞} (hCt : C ≠ ⊤) (x : X) (y : Y)
    (hcomp : ∀ s : ℝ, t ≤ s → s ≤ t + δ → K (t, x, y) ≤ C * K (s, x, y)) :
    K (t, x, y) ≤
      (ENNReal.ofReal δ⁻¹ * ENNReal.ofReal (Real.exp (rate * (t + δ))) * C) *
        laplaceTimeKernel rate K x y := by
  let E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (rate * (t + δ)))
  have hEt : E * C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCt
  have hpoint {s : ℝ} (hs : s ∈ Ioo t (t + δ)) :
      K (t, x, y) ≤ (E * C) * (laplaceTimeWeight rate s * K (s, x, y)) := by
    have hreal : 1 ≤ Real.exp (rate * (t + δ)) * Real.exp (-(rate * s)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      rw [show rate * (t + δ) + -(rate * s) = rate * ((t + δ) - s) by ring]
      exact mul_nonneg hrate (sub_nonneg.mpr hs.2.le)
    have hweight : 1 ≤ E * laplaceTimeWeight rate s := by
      dsimp [E, laplaceTimeWeight]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hreal
    calc
      _ ≤ C * K (s, x, y) := hcomp s hs.1.le hs.2.le
      _ = 1 * (C * K (s, x, y)) := (one_mul _).symm
      _ ≤ (E * laplaceTimeWeight rate s) * (C * K (s, x, y)) := mul_le_mul' hweight le_rfl
      _ = _ := by ac_rfl
  have hvol : volume (Ioo t (t + δ)) = ENNReal.ofReal δ := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hlow : ENNReal.ofReal δ * K (t, x, y) ≤ (E * C) * laplaceTimeKernel rate K x y := by
    calc
      _ = ∫⁻ s in Ioo t (t + δ), K (t, x, y) := by
        rw [setLIntegral_const, hvol]
        ac_rfl
      _ ≤ ∫⁻ s in Ioo t (t + δ), (E * C) * (laplaceTimeWeight rate s * K (s, x, y)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact hpoint hs
      _ = (E * C) * ∫⁻ s in Ioo t (t + δ), laplaceTimeWeight rate s * K (s, x, y) :=
        lintegral_const_mul' _ _ hEt
      _ ≤ (E * C) * laplaceTimeKernel rate K x y :=
        mul_le_mul' le_rfl (lintegral_mono_set (fun s hs => lt_trans ht hs.1))
  have hcancel : ENNReal.ofReal δ⁻¹ * ENNReal.ofReal δ = 1 := by
    rw [← ENNReal.ofReal_mul (inv_pos.mpr hδ).le, inv_mul_cancel₀ hδ.ne', ENNReal.ofReal_one]
  have hh := mul_le_mul' (le_refl (ENNReal.ofReal δ⁻¹)) hlow
  simpa only [← mul_assoc, hcancel, one_mul] using hh

end Critical2DKPZ.SHF.Tsai

end
