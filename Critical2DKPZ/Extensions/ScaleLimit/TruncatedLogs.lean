/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BlockIndependence
public import Critical2DKPZ.Extensions.ScaleLimit.ArrayMoments
import Mathlib.Tactic

/-! # Bounded logarithms of independent block masses -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The scalar truncation used by each block. -/
def truncatedLog (z : ℝ) : ℝ := if |z - 1| ≤ 1 / 2 then Real.log z else 0

/-- Truncating to a closed interval preserves measurability. -/
theorem measurable_truncatedLog : Measurable truncatedLog := by
  unfold truncatedLog
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    Real.measurable_log measurable_const

/-- On the truncation interval, the logarithm is bounded by `log 2`.
The same elementary estimate occurs privately in the main lattice CLT. -/
theorem abs_log_le_log_two {z : ℝ} (hclose : |z - 1| ≤ 1 / 2) :
    |Real.log z| ≤ Real.log 2 := by
  have hb := abs_le.mp hclose
  have hlo : 1 / 2 ≤ z := by linarith
  have hhi : z ≤ 2 := by linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hlo
  have hu := Real.log_le_log (by linarith : 0 < z) hhi
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv] at hl
  exact abs_le.mpr ⟨hl, hu⟩

/-- The local logarithm is Lipschitz relative to its value at one. -/
theorem abs_log_le_two_mul_abs_sub_one {z : ℝ} (hclose : |z - 1| ≤ 1 / 2) :
    |Real.log z| ≤ 2 * |z - 1| := by
  have hb := abs_le.mp hclose
  have hz : 0 < z := by linarith
  have hi : z⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hz).mpr (by linarith)
  have hu := Real.log_le_sub_one_of_pos hz
  have hl := Real.one_sub_inv_le_log_of_pos hz
  have hid : (z - 1) * z⁻¹ = 1 - z⁻¹ := by field_simp
  have hmul := mul_le_mul_of_nonneg_right (neg_abs_le (z - 1)) (inv_nonneg.mpr hz.le)
  have hmul' := mul_le_mul_of_nonneg_left hi (abs_nonneg (z - 1))
  rw [hid] at hmul
  apply abs_le.mpr
  constructor <;> nlinarith [le_abs_self (z - 1), abs_nonneg (z - 1)]

/-- The scalar truncated logarithm is globally bounded. -/
theorem abs_truncatedLog_le (z : ℝ) : |truncatedLog z| ≤ Real.log 2 := by
  unfold truncatedLog
  split_ifs with h
  · exact abs_log_le_log_two h
  · simpa only [abs_zero] using (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))

/-- Its square is controlled by the squared mass fluctuation. -/
theorem truncatedLog_sq_le (z : ℝ) : truncatedLog z ^ 2 ≤ 4 * (z - 1) ^ 2 := by
  unfold truncatedLog
  split_ifs with h
  · have hl := abs_log_le_two_mul_abs_sub_one h
    calc
      Real.log z ^ 2 = |Real.log z| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * |z - 1|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hl 2
      _ = 4 * (z - 1) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  · simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    positivity

/-- Positive-index truncated block logarithms are measurable. -/
theorem measurable_logTrunc (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (j : ℕ) : Measurable (logTrunc Z ρ (j + 1)) := by
  change Measurable (truncatedLog ∘ blockMass Z ρ (j + 1))
  exact measurable_truncatedLog.comp (measurable_blockMass ϑ P Z hZ hρ j)

/-- The logarithmic block summands remain independent after truncation. -/
theorem iIndepFun_logTrunc (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) : iIndepFun (fun j => logTrunc Z ρ (j + 1)) P := by
  exact (iIndepFun_blockMass ϑ P Z hZ hρ).comp (fun _ => truncatedLog)
    (fun _ => measurable_truncatedLog)

/-- Every block summand is bounded pointwise, without any flow assumptions. -/
theorem abs_logTrunc_le {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ρ : ℝ) (j : ℕ) (ω : Ω) : |logTrunc Z ρ j ω| ≤ Real.log 2 :=
  abs_truncatedLog_le _

/-- Positive-index summands have every finite moment. -/
theorem memLp_logTrunc (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (j : ℕ) (p : ℝ≥0∞) : MemLp (logTrunc Z ρ (j + 1)) p P :=
  memLp_of_ae_abs_le P (measurable_logTrunc ϑ P Z hZ hρ j).aemeasurable
    (Real.log 2) (Filter.Eventually.of_forall (abs_logTrunc_le Z ρ (j + 1))) p

end Critical2DKPZ.Extensions.ScaleLimit
