/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.LogKernelIdentities
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! # Exact addition of heat forms over a finite time partition -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- The spatial heat energy is integrable on every finite positive time interval. -/
theorem integrableOn_fixedHorizon_heat_energy (f : TestFn) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t => ∫ p : Plane × Plane,
      f p.1 * f p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume)) (Ioo 0 T) := by
  have h := (integrable_truncated_heat_pairing f f T hT).integral_prod_right
  apply (h.mono_measure (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl)).congr
  filter_upwards [] with t
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    dsimp only
    rw [show p.2 - p.1 = -(p.1 - p.2) by abel, heatKernel_neg]

/-- Finite adjacent intervals recover the whole integrable time form exactly. -/
theorem sum_integral_fixedHorizon_partition {T : ℝ} (hT : 0 < T)
    {M : ℕ} (hM : 0 < M) (H : ℝ → ℝ) (hH : IntegrableOn H (Ioo 0 T)) :
    (∑ i : Fin M, ∫ t in Ioo (T * ((i : ℕ) : ℝ) / M)
      (T * (((i : ℕ) : ℝ) + 1) / M), H t) = ∫ t in Ioo 0 T, H t := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let a : ℕ → ℝ := fun i => T * (i : ℝ) / M
  have ha (i : ℕ) : a i ≤ a (i + 1) := by
    apply (div_le_div_iff_of_pos_right hMr).mpr
    apply mul_le_mul_of_nonneg_left _ hT.le
    exact_mod_cast Nat.le_succ i
  have hi (i : ℕ) (hi : i < M) : IntervalIntegrable H volume (a i) (a (i + 1)) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (ha i), integrableOn_Ioc_iff_integrableOn_Ioo]
    apply hH.mono_set
    intro t ht
    have hlower : 0 ≤ a i := by dsimp [a]; positivity
    have hupper : a (i + 1) ≤ T := by
      dsimp [a]
      rw [div_le_iff₀ hMr]
      apply mul_le_mul_of_nonneg_left _ hT.le
      exact_mod_cast (show i + 1 ≤ M by omega)
    exact ⟨hlower.trans_lt ht.1, ht.2.trans_le hupper⟩
  have hadd := intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := M) hi
  have he (i : ℕ) : (∫ t in a i..a (i + 1), H t) =
      ∫ t in Ioo (a i) (a (i + 1)), H t := by
    rw [intervalIntegral.integral_of_le (ha i), integral_Ioc_eq_integral_Ioo]
  simp_rw [he] at hadd
  have hlast : a M = T := by dsimp [a]; field_simp
  rw [show a 0 = 0 by simp [a], hlast, intervalIntegral.integral_of_le hT.le,
    integral_Ioc_eq_integral_Ioo, Finset.sum_range] at hadd
  simpa only [a, Nat.cast_add, Nat.cast_one] using hadd

end Critical2DKPZ.Extensions.GffTangent
