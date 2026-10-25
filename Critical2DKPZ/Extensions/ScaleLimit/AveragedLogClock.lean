/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.LogClockEstimates

/-! # The averaged double-logarithmic expansion of Proposition 5.1 -/

public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The averaged logarithmic clock error is uniform in the relative width. -/
theorem loglog_expansion (φ ψ : TestFn) (hφ : ∀ u, 0 ≤ φ u) (hψ : ∀ v, 0 ≤ ψ v)
    (hφmass : (∫ u, φ u) = 1) (hψmass : (∫ v, ψ v) = 1) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ < 1 ∧ ∃ M : ℝ,
      ∀ a ∈ Set.Ioc (0 : ℝ) a₀, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
        Integrable (fun p : Plane × Plane => φ p.1 * ψ p.2 *
          Real.log (Real.log (a * ‖p.1 - ρ • p.2‖)⁻¹)) (volume.prod volume) ∧
        |(∫ u, ∫ v, φ u * ψ v * Real.log (Real.log (a * ‖u - ρ • v‖)⁻¹)) -
          Real.log (Real.log a⁻¹)| ≤ M / Real.log a⁻¹ := by
  obtain ⟨K, _hK, hs⟩ := exists_difference_support_radius φ ψ
  obtain ⟨N, hN⟩ := exists_sup_integral_posLog φ ψ hψ
  let B := max 0 (Real.log K)
  let a₀ := Real.exp (-(2 * B + 2))
  have hB : 0 ≤ B := le_max_left _ _
  have ha₀pos : 0 < a₀ := Real.exp_pos _
  have ha₀one : a₀ < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hB])
  refine ⟨a₀, ha₀pos, ha₀one, 2 * (B + N), ?_⟩
  intro a ha ρ hρ
  let A := Real.log a⁻¹
  let F : Plane → ℝ := fun w => Real.log (Real.log (a * ‖w‖)⁻¹)
  let D : Plane → ℝ := subDensity φ ψ ρ
  let J : Plane → ℝ := fun w => max 0 (Real.log ‖w‖⁻¹)
  have hsmall : 2 * B + 2 ≤ A := by
    have hh := Real.log_le_log ha.1 ha.2
    change Real.log a ≤ Real.log (Real.exp (-(2 * B + 2))) at hh
    rw [Real.log_exp] at hh
    dsimp [A]
    rw [Real.log_inv]
    linarith only [hh]
  have hA : 0 < A := by linarith only [hsmall, hB]
  have hsρ : ∀ w v : Plane, φ (w + ρ • v) * ψ v ≠ 0 → w ∈ Metric.ball 0 K := by
    intro w v hfg
    exact mem_ball_zero_iff.mpr (hs ρ hρ w v hfg)
  have hFa : IntegrableOn F (Metric.ball 0 K) volume := integrableOn_loglog_of_small ha.1 hsmall
  obtain ⟨hraw, hDF, hpair⟩ := difference_kernel_integral_of_support φ ψ hρ hsρ F hFa
  refine ⟨hraw, ?_⟩
  have hD : Integrable D := (integrable_subDensity_product φ ψ ρ).integral_prod_left
  have hmass : (∫ w, D w) = 1 := by
    change (∫ w, subDensity φ ψ ρ w) = 1
    rw [integral_subDensity, hφmass, hψmass, one_mul]
  have hJloc : ∀ r : ℝ, 0 < r → IntegrableOn J (Metric.ball 0 r) volume :=
    fun r _ => integrableOn_posLog_inv_norm_ball r
  have hDJ : Integrable (fun w => D w * J w) := by
    have hp := integrable_subDensity_kernel_product φ ψ hρ J hJloc
    simpa only [D, subDensity, integral_mul_const] using hp.integral_prod_left
  have hJbound : (∫ w, D w * J w) ≤ N := by
    rw [integral_subDensity_mul φ ψ hρ J hJloc]
    exact (hN ρ hρ).2
  have herror : Integrable (fun w => D w * (F w - Real.log A)) := by
    apply (hDF.sub (hD.mul_const (Real.log A))).congr
    exact Eventually.of_forall fun w => (mul_sub (D w) (F w) (Real.log A)).symm
  have hmajor : Integrable (fun w => (2 / A) * (B * D w + D w * J w)) :=
    ((hD.const_mul B).add hDJ).const_mul _
  have hbound : ∀ᵐ w : Plane ∂volume,
      ‖D w * (F w - Real.log A)‖ ≤ (2 / A) * (B * D w + D w * J w) := by
    filter_upwards [volume.ae_ne (0 : Plane)] with w hw0
    by_cases hw : w ∈ Metric.ball (0 : Plane) K
    · have hDnonneg : 0 ≤ D w := subDensity_nonneg φ ψ hφ hψ ρ w
      rw [norm_mul, Real.norm_of_nonneg hDnonneg, Real.norm_eq_abs]
      have hh := loglog_pointwise_bound ha.1 hsmall hw0 (mem_ball_zero_iff.mp hw).le
      calc
        _ ≤ D w * (2 * (B + J w) / A) := mul_le_mul_of_nonneg_left hh hDnonneg
        _ = _ := by ring
    · have hz : D w = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [] with v
        by_contra hfg
        exact hw (hsρ w v hfg)
      rw [hz, zero_mul, norm_zero, mul_zero, zero_mul, add_zero, mul_zero]
  have herror_integral : (∫ w, D w * (F w - Real.log A)) =
      (∫ w, D w * F w) - Real.log A := by
    simp_rw [mul_sub]
    rw [integral_sub hDF (hD.mul_const _), integral_mul_const, hmass, one_mul]
  have hresult : |(∫ w, D w * F w) - Real.log A| ≤ 2 * (B + N) / A := by
    calc
      _ = ‖∫ w, D w * (F w - Real.log A)‖ := by
        rw [herror_integral, Real.norm_eq_abs]
      _ ≤ ∫ w, ‖D w * (F w - Real.log A)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ w, (2 / A) * (B * D w + D w * J w) :=
        integral_mono_ae herror.norm hmajor hbound
      _ = (2 / A) * (B + ∫ w, D w * J w) := by
        rw [integral_const_mul, integral_add (hD.const_mul B) hDJ,
          integral_const_mul, hmass, mul_one]
      _ ≤ (2 / A) * (B + N) := mul_le_mul_of_nonneg_left
        (add_le_add_right hJbound B) (div_nonneg (by norm_num) hA.le)
      _ = 2 * (B + N) / A := by ring
  rw [← hpair]
  exact hresult

end Critical2DKPZ.Extensions.ScaleLimit
