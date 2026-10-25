/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzSpectralLp
import Critical2DKPZ.Spectral.BochnerSchwartzSchwartzExtension
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Spectral L² convergence of bounded Schwartz families -/

public section

noncomputable section

open MeasureTheory Filter Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A bounded Schwartz sequence admits a common spectral L² envelope. -/
theorem schwartz_sequence_envelope (ν : Measure Plane) [ν.HasTemperateGrowth]
    (F : ℕ → SchwartzMap Plane ℂ)
    (hb : Bornology.IsVonNBounded ℝ (Set.range F)) :
    ∃ b : Plane → ℝ, MemLp b 2 ν ∧ (∀ x, 0 ≤ b x) ∧ ∀ n x, ‖F n x‖ ≤ b x := by
  obtain ⟨k, hk⟩ := (inferInstance : ν.HasTemperateGrowth).exists_eLpNorm_lt_top 2
  have hsem := (schwartz_withSeminorms ℝ Plane ℂ).isVonNBounded_iff_seminorm_bounded.mp hb
  obtain ⟨B0, hB0, h0⟩ := hsem (0, 0)
  obtain ⟨Bk, hBk, hK⟩ := hsem (k, 0)
  let C : ℝ := 2 ^ (k - 1) * (B0 + Bk)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let w : Plane → ℝ := fun x => (1 + ‖x‖) ^ (-(k : ℝ))
  have hw : MemLp w 2 ν := hk
  refine ⟨fun x => C * w x, hw.const_mul C, fun x => mul_nonneg hC (by dsimp [w]; positivity), ?_⟩
  intro n x
  have h := Spectral.one_add_norm_pow_mul_norm_le_of_seminorm_bounds (F n) k B0 Bk
    (h0 _ ⟨n, rfl⟩).le (hK _ ⟨n, rfl⟩).le x
  have hx : 0 < (1 + ‖x‖) ^ k := by positivity
  dsimp [w]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ hx).mpr (by simpa only [C, mul_comm] using h)

/-- Pointwise convergence and boundedness in Schwartz space imply convergence in spectral L². -/
theorem tendsto_schwartz_toLp_of_bounded_pointwise (ν : Measure Plane) [ν.HasTemperateGrowth]
    (F : ℕ → SchwartzMap Plane ℂ) (f : SchwartzMap Plane ℂ)
    (hb : Bornology.IsVonNBounded ℝ (Set.range F))
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (F n).toLp 2 ν) atTop (𝓝 (f.toLp 2 ν)) := by
  obtain ⟨b, hbLp, hb0, hbF⟩ := schwartz_sequence_envelope ν F hb
  have hbf (x : Plane) : ‖f x‖ ≤ b x :=
    le_of_tendsto ((hlim x).norm) (Eventually.of_forall fun n => hbF n x)
  have hbound : Integrable (fun x => ‖(2 : ℝ) * b x‖ ^ 2) ν :=
    (hbLp.const_mul 2).integrable_norm_pow (by norm_num)
  have hInt : Tendsto (fun n => ∫ x, ‖(F n - f) x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) (fun x => ‖(2 : ℝ) * b x‖ ^ 2)
      (fun n => ((F n - f).continuous.norm.pow 2).aestronglyMeasurable) hbound
      (fun n => ae_of_all ν fun x => ?_) (ae_of_all ν fun x => ?_)
    · simpa using h
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        ‖(F n - f) x‖ ≤ ‖F n x‖ + ‖f x‖ := norm_sub_le _ _
        _ ≤ b x + b x := add_le_add (hbF n x) (hbf x)
        _ = ‖(2 : ℝ) * b x‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) (hb0 x))]; ring
    · simpa using (((hlim x).sub_const (f x)).norm.pow 2)
  rw [tendsto_iff_dist_tendsto_zero]
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hInt
  convert hsqrt using 1
  · ext n
    rw [dist_eq_norm]
    change ‖SchwartzMap.toLpCLM ℝ ℂ 2 ν (F n) - SchwartzMap.toLpCLM ℝ ℂ 2 ν f‖ = _
    rw [← map_sub]
    rw [SchwartzMap.toLpCLM_apply, SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    norm_num [Real.sqrt_eq_rpow, Real.rpow_two]
  · norm_num

end Critical2DKPZ.Extensions.ScaleLimit
