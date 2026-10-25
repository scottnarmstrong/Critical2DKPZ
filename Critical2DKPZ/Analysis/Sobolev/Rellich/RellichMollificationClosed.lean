/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichMollify
public import Critical2DKPZ.Analysis.Sobolev.Rellich.HighFrequency
public import Critical2DKPZ.Analysis.Sobolev.Rellich.FourierCharPhase
public import Critical2DKPZ.Analysis.Sobolev.Rellich.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform approximation of stronger Sobolev unit balls by a fixed smooth mollifier.

Adapted from work of A. Bou-Rabee, licensed under Apache 2.0. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology Convolution

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- Integrating a character bound against a nonnegative probability kernel preserves the bound. -/
private theorem norm_one_sub_fourier_kernel_le {d : ℕ} (ρ : Space d → ℝ)
    (hi : Integrable ρ) (hm : ∫ y, ρ y = 1) (hp : ∀ y, 0 ≤ ρ y) (ξ : Space d)
    {c : ℝ} (hc : ∀ y, ρ y ≠ 0 → ‖(1 : ℂ) - (𝐞 (-inner ℝ y ξ) : ℂ)‖ ≤ c) :
    ‖1 - 𝓕 (fun y => (ρ y : ℂ)) ξ‖ ≤ c := by
  have hchar : Integrable (fun y : Space d => 𝐞 (-inner ℝ y ξ) • (ρ y : ℂ)) :=
    (Real.fourierIntegral_convergent_iff ξ).mpr hi.ofReal
  have hone : (∫ y : Space d, (ρ y : ℂ)) = 1 := by
    rw [_root_.integral_complex_ofReal, hm]
    norm_num
  have heq : 1 - 𝓕 (fun y => (ρ y : ℂ)) ξ
      = ∫ y : Space d, (ρ y : ℂ) * (1 - (𝐞 (-inner ℝ y ξ) : ℂ)) := by
    calc
      1 - 𝓕 (fun y => (ρ y : ℂ)) ξ =
          (∫ y : Space d, (ρ y : ℂ)) - 𝓕 (fun y => (ρ y : ℂ)) ξ := by rw [hone]
      _ = ∫ y : Space d, (ρ y : ℂ) - 𝐞 (-inner ℝ y ξ) • (ρ y : ℂ) :=
        (congrArg (fun z => (∫ y : Space d, (ρ y : ℂ)) - z)
          (Real.fourier_eq (fun y => (ρ y : ℂ)) ξ)).trans
          (integral_sub hi.ofReal hchar).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun y => by
        simp only [Circle.smul_def, smul_eq_mul]
        ring)
  rw [heq]
  have hbound : ∀ y : Space d,
      ‖(ρ y : ℂ) * (1 - (𝐞 (-inner ℝ y ξ) : ℂ))‖ ≤ ρ y * c := by
    intro y
    by_cases hz : ρ y = 0
    · simp [hz]
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp y)]
      exact mul_le_mul_of_nonneg_left (hc y hz) (hp y)
  calc ‖∫ y : Space d, (ρ y : ℂ) * (1 - (𝐞 (-inner ℝ y ξ) : ℂ))‖
      ≤ ∫ y : Space d, ρ y * c := norm_integral_le_of_norm_le (hi.mul_const c)
          (Filter.Eventually.of_forall hbound)
    _ = c := by rw [integral_mul_const, hm, one_mul]

/-- A single positive smooth mollifier approximates the entire test-function unit ball. -/
theorem exists_uniform_testFn_mollifier {d : ℕ} {s₀ s : ℝ} (hss : s₀ < s)
    (η : ℝ) (hη : 0 < η) :
    ∃ ρ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      (∫ y, ρ y = 1) ∧ (∀ y, 0 ≤ ρ y) ∧
      ∀ (φ : Space d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        sobolevNormSq d s φ ≤ 1 →
          sobolevNormSq d s₀ (fun x => φ x - convReal φ ρ x) ≤ ENNReal.ofReal η := by
  have hev : ∀ᶠ R : ℝ in atTop,
      (1 + (2 * Real.pi * R) ^ 2) ^ (s₀ - s) < η / 4 :=
    (tendsto_weight_atTop_zero hss).eventually (Iio_mem_nhds (by positivity))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨R₀, hR₀⟩ := hev
  let R : ℝ := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hratio : (1 + (2 * Real.pi * R) ^ 2) ^ (s₀ - s) ≤ η / 4 :=
    (hR₀ R (le_max_left _ _)).le
  let δ : ℝ := min (1 / (2 * Real.pi * R)) (Real.sqrt η / (4 * Real.pi * R))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  let b : ContDiffBump (0 : Space d) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let ρ : Space d → ℝ := b.normed volume
  have hi : Integrable ρ := b.integrable_normed
  have hm : ∫ y, ρ y = 1 := b.integral_normed
  have hp : ∀ y, 0 ≤ ρ y := fun y => b.nonneg_normed y
  have hphase : 2 * Real.pi * R * δ ≤ 1 := by
    have hd := (le_div_iff₀ (by positivity : 0 < 2 * Real.pi * R)).mp
      (min_le_left (1 / (2 * Real.pi * R)) (Real.sqrt η / (4 * Real.pi * R)))
    nlinarith
  have hsmall : 4 * Real.pi * R * δ ≤ Real.sqrt η := by
    have hd := (le_div_iff₀ (by positivity : 0 < 4 * Real.pi * R)).mp
      (min_le_right (1 / (2 * Real.pi * R)) (Real.sqrt η / (4 * Real.pi * R)))
    nlinarith
  have hcoef : (4 * Real.pi * R * δ) ^ 2 ≤ η := by
    have hsqrt := Real.sq_sqrt hη.le
    have hnonneg : 0 ≤ 4 * Real.pi * R * δ := by positivity
    nlinarith [Real.sqrt_nonneg η]
  have hall : ∀ ξ : Space d, ‖1 - 𝓕 (fun y => (ρ y : ℂ)) ξ‖ ≤ 2 := by
    intro ξ
    refine norm_one_sub_fourier_kernel_le ρ hi hm hp ξ ?_
    intro y _
    rw [norm_sub_rev]
    exact norm_fourierChar_sub_one_le_two _
  have hlow : ∀ ξ : Space d, ‖ξ‖ ≤ R →
      ‖1 - 𝓕 (fun y => (ρ y : ℂ)) ξ‖ ≤ 4 * Real.pi * R * δ := by
    intro ξ hξ
    refine norm_one_sub_fourier_kernel_le ρ hi hm hp ξ ?_
    intro y hy
    have hyball : y ∈ Metric.ball (0 : Space d) δ := by
      have hyS : y ∈ Function.support ρ := hy
      rwa [b.support_normed_eq] at hyS
    have hynorm : ‖y‖ ≤ δ := by
      rw [Metric.mem_ball, dist_zero_right] at hyball
      exact hyball.le
    have hinner : |inner ℝ y ξ| ≤ R * δ := by
      calc |inner ℝ y ξ| ≤ ‖y‖ * ‖ξ‖ := abs_real_inner_le_norm y ξ
        _ ≤ δ * R := mul_le_mul hynorm hξ (norm_nonneg ξ) hδ.le
        _ = R * δ := mul_comm _ _
    have hph : 2 * Real.pi * |-inner ℝ y ξ| ≤ 1 := by
      rw [abs_neg]
      exact (mul_le_mul_of_nonneg_left hinner (by positivity)).trans
        (by simpa only [mul_assoc] using hphase)
    rw [norm_sub_rev]
    refine (norm_fourierChar_sub_one_le hph).trans ?_
    rw [abs_neg]
    calc 4 * Real.pi * |inner ℝ y ξ| ≤ 4 * Real.pi * (R * δ) := by gcongr
      _ = 4 * Real.pi * R * δ := by ring
  have hmult : ∀ ξ : Space d,
      ‖1 - 𝓕 (fun y => (ρ y : ℂ)) ξ‖ ^ 2
        * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s) ≤ η := by
    intro ξ
    have hwpos : 0 ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s) := by positivity
    by_cases hξ : ‖ξ‖ ≤ R
    · have hwle : (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg (2 * Real.pi * ‖ξ‖)])
          (by linarith)
      have hsquare : ‖1 - 𝓕 (fun y => (ρ y : ℂ)) ξ‖ ^ 2
          ≤ (4 * Real.pi * R * δ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hlow ξ hξ) 2
      calc ‖1 - 𝓕 (fun y => (ρ y : ℂ)) ξ‖ ^ 2
            * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s)
          ≤ (4 * Real.pi * R * δ) ^ 2 * 1 :=
            mul_le_mul hsquare hwle hwpos (sq_nonneg _)
        _ ≤ η := by simpa using hcoef
    · have hnorm : R ≤ ‖ξ‖ := (not_le.mp hξ).le
      have hb : 1 + (2 * Real.pi * R) ^ 2 ≤ 1 + (2 * Real.pi * ‖ξ‖) ^ 2 := by
        have hmul : 2 * Real.pi * R ≤ 2 * Real.pi * ‖ξ‖ := by gcongr
        exact add_le_add_right (pow_le_pow_left₀ (by positivity) hmul 2) 1
      have hwle : (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s) ≤ η / 4 :=
        (Real.rpow_le_rpow_of_nonpos (by positivity) hb (by linarith)).trans hratio
      have hsquare : ‖1 - 𝓕 (fun y => (ρ y : ℂ)) ξ‖ ^ 2 ≤ 4 := by
        nlinarith [hall ξ, norm_nonneg (1 - 𝓕 (fun y => (ρ y : ℂ)) ξ)]
      calc ‖1 - 𝓕 (fun y => (ρ y : ℂ)) ξ‖ ^ 2
            * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s)
          ≤ 4 * (η / 4) := mul_le_mul hsquare hwle hwpos (by norm_num)
        _ = η := by ring
  refine ⟨ρ, b.contDiff_normed, b.hasCompactSupport_normed, hm, hp, ?_⟩
  intro φ hc hk hn
  have hb := sobolevNormSq_sub_convolution_le φ ρ hc b.contDiff_normed hk
    b.hasCompactSupport_normed hη.le hmult
  have heq : (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) = convReal φ ρ := by
    funext x
    simp only [convReal, convolution_def, ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.lsmul_apply,
      smul_eq_mul]
  rw [heq] at hb
  exact hb.trans (by
    simpa only [mul_one] using (mul_le_mul_right hn (ENNReal.ofReal η)))

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
