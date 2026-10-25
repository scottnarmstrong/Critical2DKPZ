/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.SlowVariation

/-! # Tail integral asymptotics for slowly varying functions -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Critical2DKPZ.CovarianceKernel

private theorem tail_log_power_bound {u : ℝ} (hu : 1 ≤ u) :
    u ^ (-(3 : ℝ) / 2) * (1 + Real.log u) ≤ 5 * u ^ (-(5 : ℝ) / 4) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hlog := Real.log_le_rpow_div hu0.le (by norm_num : (0 : ℝ) < 1 / 4)
  have hp : 1 ≤ u ^ ((1 : ℝ) / 4) := Real.one_le_rpow hu (by norm_num)
  calc
    u ^ (-(3 : ℝ) / 2) * (1 + Real.log u) ≤
        u ^ (-(3 : ℝ) / 2) * (5 * u ^ ((1 : ℝ) / 4)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu0.le _)
      linarith
    _ = 5 * u ^ (-(5 : ℝ) / 4) := by
      rw [mul_left_comm, ← Real.rpow_add hu0]
      norm_num

private theorem normalized_tail_bound (M : ℝ → ℝ) (hM : Monotone M)
    {R A : ℝ} (hR : 0 < R) (hMR : 0 < M R)
    (hA : ∀ u : ℝ, 1 ≤ u → M (R * u) ≤ A * (1 + Real.log u) * M R) :
    ∀ᵐ u ∂volume.restrict (Ioi (1 : ℝ)),
      ‖u ^ (-(3 : ℝ) / 2) * (M (R * u) / M R)‖ ≤
        (5 * |A|) * u ^ (-(5 : ℝ) / 4) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hratio0 : 0 ≤ M (R * u) / M R :=
    div_nonneg (hMR.le.trans (hM (by simpa using
      (mul_le_mul_of_nonneg_left hu.le hR.le)))) hMR.le
  have hratio : M (R * u) / M R ≤ |A| * (1 + Real.log u) := by
    apply (div_le_iff₀ hMR).2
    exact (hA u hu.le).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self A)
        (by positivity [Real.log_nonneg hu.le])) hMR.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hu0.le _) hratio0)]
  calc
    _ ≤ u ^ (-(3 : ℝ) / 2) * (|A| * (1 + Real.log u)) :=
      mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hu0.le _)
    _ = |A| * (u ^ (-(3 : ℝ) / 2) * (1 + Real.log u)) := by ring
    _ ≤ |A| * (5 * u ^ (-(5 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left (tail_log_power_bound hu.le) (abs_nonneg A)
    _ = _ := by ring


private theorem tail_rescale (M : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ a in Ioi R, a ^ (-(3 : ℝ) / 2) * M a) =
      (R * R ^ (-(3 : ℝ) / 2)) *
        (∫ u in Ioi (1 : ℝ), u ^ (-(3 : ℝ) / 2) * M (R * u)) := by
  have h := integral_comp_mul_left_Ioi' (fun a : ℝ => a ^ (-(3 : ℝ) / 2) * M a) 1 hR
  simp only [smul_eq_mul, mul_one] at h
  rw [← h, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [Real.mul_rpow hR.le (le_of_lt (zero_lt_one.trans hu))]
  ring


/-- Under the logarithmic dilation bound, the inverse-three-halves weighted tail of a monotone slowly varying function is asymptotic to twice its value divided by the square root of the cutoff. Tail integrability follows from `tail_log_power_bound` and `integrableOn_Ioi_rpow_of_lt`. -/
theorem tendsto_integral_rpow_div_of_slowlyVarying (M : ℝ → ℝ) (hM : Monotone M)
    (hpos : ∀ᶠ R in atTop, 0 < M R)
    (hslow : ∀ u : ℝ, 0 < u → Tendsto (fun R => M (R * u) / M R) atTop (𝓝 1))
    (hdom : ∃ A : ℝ, ∀ᶠ R in atTop, ∀ u : ℝ, 1 ≤ u →
      M (R * u) ≤ A * (1 + Real.log u) * M R) :
    Tendsto (fun R => Real.sqrt R / 2 *
      (∫ a in Set.Ioi R, a ^ (-(3 : ℝ) / 2) * M a) / M R) atTop (𝓝 1) := by
  obtain ⟨A, hA⟩ := hdom
  let F : ℝ → ℝ → ℝ := fun R u => u ^ (-(3 : ℝ) / 2) * (M (R * u) / M R)
  have hmeas : ∀ R, AEStronglyMeasurable (F R) (volume.restrict (Ioi (1 : ℝ))) := by
    intro R
    exact ((measurable_id.pow_const _).mul
      ((hM.measurable.comp (measurable_const.mul measurable_id)).div_const _)).aestronglyMeasurable
  have hbound : ∀ᶠ R in atTop, ∀ᵐ u ∂volume.restrict (Ioi (1 : ℝ)),
      ‖F R u‖ ≤ (5 * |A|) * u ^ (-(5 : ℝ) / 4) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hpos, hA] with R hR hMR hAR
    exact normalized_tail_bound M hM hR hMR hAR
  have hlim : ∀ᵐ u ∂volume.restrict (Ioi (1 : ℝ)),
      Tendsto (fun R => F R u) atTop (𝓝 (u ^ (-(3 : ℝ) / 2))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simpa [F] using (hslow u (zero_lt_one.trans hu)).const_mul (u ^ (-(3 : ℝ) / 2))
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (1 : ℝ))) (fun u => (5 * |A|) * u ^ (-(5 : ℝ) / 4))
    (Eventually.of_forall hmeas) hbound
    ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(5 : ℝ) / 4 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul (5 * |A|)) hlim
  have hval : (∫ u in Ioi (1 : ℝ), u ^ (-(3 : ℝ) / 2)) = 2 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : -(3 : ℝ) / 2 < -1) (by norm_num)]
    norm_num
  rw [hval] at hconv
  have hhalf := hconv.const_mul (1 / 2 : ℝ)
  norm_num only [one_div, invOf_eq_inv, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)] at hhalf
  apply hhalf.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hpos] with R hR hMR
  rw [tail_rescale M hR]
  have hpow : Real.sqrt R * (R * R ^ (-(3 : ℝ) / 2)) = 1 := by
    calc
      _ = R ^ ((1 : ℝ) / 2) * (R ^ (1 : ℝ) * R ^ (-(3 : ℝ) / 2)) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_one]
      _ = R ^ ((1 : ℝ) / 2 + (1 - 3 / 2)) := by
        rw [← Real.rpow_add hR, ← Real.rpow_add hR]
        congr 1
        ring
      _ = 1 := by norm_num
  dsimp [F]
  simp only [← mul_div_assoc]
  rw [integral_div]
  calc
    _ = (Real.sqrt R * (R * R ^ (-(3 : ℝ) / 2))) / 2 *
        (∫ u in Ioi (1 : ℝ), u ^ (-(3 : ℝ) / 2) * M (R * u)) / M R := by rw [hpow]; ring
    _ = _ := by ring

end Critical2DKPZ.CovarianceKernel
