/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.AveragedLogClock
import Critical2DKPZ.Spectral.BochnerSchwartz
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # From the kernel asymptotic to uniform averaged covariance asymptotics -/

public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Dilating a locally square-integrable kernel preserves integrability on bounded balls. -/
theorem integrableOn_kernel_comp_smul (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    {a : ℝ} (ha : 0 < a) (R : ℝ) :
    IntegrableOn (fun w : Plane => C (a • w)) (Metric.ball 0 R) volume := by
  let K := Metric.closedBall (0 : Plane) (a * R)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hc : IntegrableOn C K volume :=
    (Spectral.locallyIntegrable_of_compactMemLp_two C hC).integrableOn_isCompact hK
  have hcut : Integrable (K.indicator C) := hc.integrable_indicator hK.measurableSet
  apply (hcut.comp_smul ha.ne').integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  have hmem : a • w ∈ K := by
    change a • w ∈ Metric.closedBall (0 : Plane) (a * R)
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hw).le ha.le
  exact Set.indicator_of_mem hmem _

/-- Small-width double logarithms are positive on the punctured support ball. -/
theorem loglog_pos_of_small {a K : ℝ} (ha : 0 < a)
    (hsmall : 2 * max 0 (Real.log K) + 2 ≤ Real.log a⁻¹)
    {w : Plane} (hw : w ≠ 0) (hwK : ‖w‖ ≤ K) :
    0 < Real.log (Real.log (a * ‖w‖)⁻¹) := by
  have hB : 0 ≤ max 0 (Real.log K) := le_max_left _ _
  have hlogw := (Real.log_le_log (norm_pos_iff.mpr hw) hwK).trans
    (le_max_right 0 (Real.log K))
  have hA : Real.log a⁻¹ = -Real.log a := Real.log_inv a
  apply Real.log_pos
  rw [Real.log_inv, Real.log_mul ha.ne' (norm_pos_iff.mpr hw).ne']
  linarith only [hsmall, hB, hlogw, hA]

/-- Multiplicative and additive errors combine after division by a positive clock. -/
theorem clock_ratio_error {q m z δ : ℝ} (hq : 0 < q) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hm : |m / q - 1| ≤ δ) (hz : |z - m| ≤ δ * m) : |z / q - 1| ≤ 3 * δ := by
  have hmr : m / q ≤ 2 := by linarith only [(abs_le.mp hm).2, hδone]
  have hzm : |z / q - m / q| ≤ 2 * δ := by
    calc
      _ = |z - m| / q := by rw [← sub_div, abs_div, abs_of_pos hq]
      _ ≤ (δ * m) / q := div_le_div_of_nonneg_right hz hq.le
      _ = δ * (m / q) := mul_div_assoc _ _ _
      _ ≤ δ * 2 := mul_le_mul_of_nonneg_left hmr hδ
      _ = 2 * δ := mul_comm _ _
  calc
    _ = |(z / q - m / q) + (m / q - 1)| := by congr 1; ring
    _ ≤ |z / q - m / q| + |m / q - 1| := abs_add_le _ _
    _ ≤ 2 * δ + δ := add_le_add hzm hm
    _ = 3 * δ := by ring

/-- An almost-everywhere relative kernel bound passes through an integrable density. -/
theorem integral_density_relative_error (D C F : Plane → ℝ) (δ : ℝ)
    (hC : Integrable (fun w => D w * C w)) (hF : Integrable (fun w => D w * F w))
    (hb : ∀ᵐ w : Plane ∂volume, ‖D w * (C w - F w)‖ ≤ δ * (D w * F w)) :
    |(∫ w, D w * C w) - (∫ w, D w * F w)| ≤ δ * (∫ w, D w * F w) := by
  have hi : Integrable (fun w => D w * (C w - F w)) := by
    apply (hC.sub hF).congr
    exact Eventually.of_forall fun w => (mul_sub _ _ _).symm
  have heq : (∫ w, D w * (C w - F w)) =
      (∫ w, D w * C w) - (∫ w, D w * F w) := by
    simp_rw [mul_sub]
    exact integral_sub hC hF
  calc
    _ = ‖∫ w, D w * (C w - F w)‖ := by rw [heq, Real.norm_eq_abs]
    _ ≤ ∫ w, ‖D w * (C w - F w)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ w, δ * (D w * F w) := integral_mono_ae hi.norm (hF.const_mul δ) hb
    _ = δ * (∫ w, D w * F w) := integral_const_mul _ _

/-- A kernel with the diagonal double-logarithmic asymptotic has the uniform averaged clock. -/
theorem kernel_clock_diagonal_asymptotic (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hlim : Tendsto (fun z => C z / Real.log (Real.log ‖z‖⁻¹))
      (nhdsWithin 0 {0}ᶜ) (𝓝 1))
    (φ ψ : TestFn) (hφ : ∀ u, 0 ≤ φ u) (hψ : ∀ v, 0 ≤ ψ v)
    (hφmass : (∫ u, φ u) = 1) (hψmass : (∫ v, ψ v) = 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Set.Ioc (0 : ℝ) a₀, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
      |(∫ u, ∫ v, φ u * ψ v * C (a • (u - ρ • v))) /
        Real.log (Real.log a⁻¹) - 1| ≤ η := by
  obtain ⟨K, hK, hs⟩ := exists_difference_support_radius φ ψ
  obtain ⟨a₁, ha₁, _ha₁one, N, hN⟩ := loglog_expansion φ ψ hφ hψ hφmass hψmass
  let δ := min (η / 3) 1
  have hδ : 0 < δ := lt_min (div_pos hη (by norm_num)) zero_lt_one
  have hδone : δ ≤ 1 := min_le_right _ _
  have hδη : 3 * δ ≤ η := by have hh := min_le_left (η / 3) (1 : ℝ); dsimp [δ]; linarith only [hh]
  have hevent : ∀ᶠ z : Plane in nhdsWithin 0 {0}ᶜ,
      |C z / Real.log (Real.log ‖z‖⁻¹) - 1| < δ := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      hlim.eventually (Metric.ball_mem_nhds (1 : ℝ) hδ)
  obtain ⟨r, hr, hrbound⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  let B := max 0 (Real.log K)
  let Q := max (2 * B + 2) (max (Real.exp 1) (|N| / δ + 1))
  let a₀ := min a₁ (min (Real.exp (-Q)) (r / (2 * K)))
  have ha₀ : 0 < a₀ := lt_min ha₁ (lt_min (Real.exp_pos _)
    (div_pos hr (mul_pos (by norm_num) hK)))
  refine ⟨a₀, ha₀, ?_⟩
  intro a ha ρ hρ
  have haa₁ : a ≤ a₁ := ha.2.trans (min_le_left _ _)
  have hasmall : a ≤ Real.exp (-Q) :=
    ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have har : a ≤ r / (2 * K) :=
    ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  let A := Real.log a⁻¹
  let q := Real.log A
  let F : Plane → ℝ := fun w => Real.log (Real.log (a * ‖w‖)⁻¹)
  let D : Plane → ℝ := subDensity φ ψ ρ
  let G : Plane → ℝ := fun w => C (a • w)
  have hQA : Q ≤ A := by
    have hh := Real.log_le_log ha.1 hasmall
    rw [Real.log_exp] at hh
    dsimp [A]
    rw [Real.log_inv]
    linarith only [hh]
  have hsmall : 2 * B + 2 ≤ A := (le_max_left _ _).trans hQA
  have hAexp : Real.exp 1 ≤ A := (le_max_left _ _).trans ((le_max_right _ _).trans hQA)
  have hA : 0 < A := (Real.exp_pos 1).trans_le hAexp
  have hqone : 1 ≤ q := by
    have hh := Real.log_le_log (Real.exp_pos 1) hAexp
    rwa [Real.log_exp] at hh
  have hq : 0 < q := zero_lt_one.trans_le hqone
  have hNle : N / A ≤ δ := by
    have hthreshold : |N| / δ ≤ A :=
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans hQA))
    apply (div_le_iff₀ hA).mpr
    have hh := (div_le_iff₀ hδ).mp hthreshold
    simpa only [mul_comm] using (le_abs_self N).trans hh
  have hsρ : ∀ w v : Plane, φ (w + ρ • v) * ψ v ≠ 0 → w ∈ Metric.ball 0 K := by
    intro w v hfg
    exact mem_ball_zero_iff.mpr (hs ρ hρ w v hfg)
  obtain ⟨_hrawC, hDC, hpairC⟩ := difference_kernel_integral_of_support φ ψ hρ hsρ G
    (integrableOn_kernel_comp_smul C hC ha.1 K)
  obtain ⟨_hrawF, hDF, hpairF⟩ := difference_kernel_integral_of_support φ ψ hρ hsρ F
    (integrableOn_loglog_of_small ha.1 hsmall)
  have hmean : |(∫ w, D w * F w) / q - 1| ≤ δ := by
    have hh : |(∫ w, D w * F w) - q| ≤ δ := by
      rw [hpairF]
      exact ((hN a ⟨ha.1, haa₁⟩ ρ hρ).2).trans hNle
    calc
      _ = |(∫ w, D w * F w) - q| / q := by
        rw [show (∫ w, D w * F w) / q - 1 = ((∫ w, D w * F w) - q) / q by field_simp,
          abs_div, abs_of_pos hq]
      _ ≤ δ / q := div_le_div_of_nonneg_right hh hq.le
      _ ≤ δ := div_le_self hδ.le hqone
  have hpoint : ∀ᵐ w : Plane ∂volume, ‖D w * (G w - F w)‖ ≤ δ * (D w * F w) := by
    filter_upwards [volume.ae_ne (0 : Plane)] with w hw0
    by_cases hw : w ∈ Metric.ball (0 : Plane) K
    · have hFpos : 0 < F w := loglog_pos_of_small ha.1 hsmall hw0 (mem_ball_zero_iff.mp hw).le
      have hz0 : a • w ≠ 0 := smul_ne_zero ha.1.ne' hw0
      have hnorm : ‖a • w‖ < r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha.1]
        calc
          a * ‖w‖ ≤ a * K := mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hw).le ha.1.le
          _ ≤ (r / (2 * K)) * K := mul_le_mul_of_nonneg_right har hK.le
          _ = r / 2 := by field_simp
          _ < r := half_lt_self hr
      have hratio : |G w / F w - 1| ≤ δ := by
        have hh := hrbound ⟨mem_ball_zero_iff.mpr hnorm, by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz0⟩
        change |C (a • w) / Real.log (Real.log ‖a • w‖⁻¹) - 1| < δ at hh
        simpa only [G, F, norm_smul, Real.norm_eq_abs, abs_of_pos ha.1] using hh.le
      have herr : |G w - F w| ≤ δ * F w := by
        calc
          _ = |G w / F w - 1| * F w := by
            have halg : G w - F w = (G w / F w - 1) * F w := by field_simp
            rw [halg, abs_mul, abs_of_pos hFpos]
          _ ≤ δ * F w := mul_le_mul_of_nonneg_right hratio hFpos.le
      have hDnonneg : 0 ≤ D w := subDensity_nonneg φ ψ hφ hψ ρ w
      rw [norm_mul, Real.norm_of_nonneg hDnonneg, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left herr hDnonneg).trans_eq (by ring)
    · have hz : D w = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [] with v
        by_contra hfg
        exact hw (hsρ w v hfg)
      rw [hz, zero_mul, norm_zero, zero_mul, mul_zero]
  have herr := integral_density_relative_error D G F δ hDC hDF hpoint
  have hfinal := (clock_ratio_error hq hδ.le hδone hmean herr).trans hδη
  rw [hpairC] at hfinal
  exact hfinal

end Critical2DKPZ.Extensions.ScaleLimit
