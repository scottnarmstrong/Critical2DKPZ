/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.LocNegSobolevFourierCompactness
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Frequency truncation for bounded local negative Sobolev energies -/

@[expose] public section

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology FourierTransform

namespace Critical2DKPZ.Analysis.Sobolev

/-- Uniform bounds at the countable localizers control the energy at any fixed smooth cutoff. -/
theorem exists_uniform_localEnergy_bound_of_localizer_bounds
    {a : ℝ} (ha : 0 ≤ a) (T : ℕ → Distr)
    (hT : ∀ m, ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
      ∀ n, localNegSobolevSq a (T n) (localizer m) ≤ B) (χ : TestFn) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ n, localNegSobolevSq a (T n) χ ≤ B := by
  obtain ⟨m, hm⟩ := exists_testFnMul_localizer_eq χ
  obtain ⟨B, hB, hbound⟩ := hT m
  let C : ℝ≥0∞ := ENNReal.ofReal ((∫ η : Plane,
    ‖(𝓕 (testFnSchwartz χ)) η‖ *
      Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a)) ^ 2)
  refine ⟨C * B, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB, fun n => ?_⟩
  have hmul : testFnMul χ (localizer m) = χ := by
    rw [testFnMul_comm]
    exact hm m le_rfl
  have h := (localNegSobolevSq_testFnMul_le ha (T n) (localizer m) χ
    ((hbound n).trans_lt (lt_top_iff_ne_top.mpr hB))).2
  rw [hmul] at h
  exact h.trans (mul_le_mul' le_rfl (hbound n))

/-- The normalized Fourier density defining the localized negative Sobolev energy. -/
def localEnergyDensity (a : ℝ) (T : Distr) (χ : TestFn) (ξ : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 * Real.pi)⁻¹ ^ 2) *
    ((1 + ‖ξ‖ ^ 2) ^ (-a) * ‖localizedFourier T χ ξ‖ ^ 2))

/-- Integrating the nonnegative local Fourier density gives the localized Sobolev energy. -/
theorem lintegral_localEnergyDensity (a : ℝ) (T : Distr) (χ : TestFn) :
    ∫⁻ ξ, localEnergyDensity a T χ ξ = localNegSobolevSq a T χ := by
  rw [localNegSobolevSq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro ξ
  rw [localEnergyDensity, ← ENNReal.ofReal_mul (by positivity :
    0 ≤ (2 * Real.pi)⁻¹ ^ 2), norm_localizedFourier_sq]

/-- The local Fourier energy density is measurable in frequency. -/
theorem measurable_localEnergyDensity (a : ℝ) (T : Distr) (χ : TestFn) :
    Measurable (localEnergyDensity a T χ) := by
  unfold localEnergyDensity
  exact (continuous_const.mul
    (((continuous_const.add (continuous_norm.pow 2)).rpow_const
      (fun ξ => Or.inl (by positivity : (1 : ℝ) + ‖ξ‖ ^ 2 ≠ 0))).mul
      ((continuous_localizedFourier T χ).norm.pow 2))).measurable.ennreal_ofReal

/-- Outside a frequency ball, the weaker energy density is bounded by the stronger density
times a scalar that vanishes as the radius tends to infinity. -/
theorem localEnergyDensity_le_tail_factor {a b R : ℝ} (hab : a ≤ b) (hR : 0 ≤ R)
    (T : Distr) (χ : TestFn) (ξ : Plane) (hξ : R ≤ ‖ξ‖) :
    localEnergyDensity b T χ ξ ≤
      ENNReal.ofReal ((1 + R ^ 2) ^ (a - b)) * localEnergyDensity a T χ ξ := by
  rw [localEnergyDensity, localEnergyDensity, ← ENNReal.ofReal_mul
    (Real.rpow_nonneg (by positivity) _)]
  apply ENNReal.ofReal_le_ofReal
  have hw : (1 + ‖ξ‖ ^ 2) ^ (a - b) ≤ (1 + R ^ 2) ^ (a - b) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (by nlinarith [sq_nonneg (‖ξ‖ - R)]) (sub_nonpos.mpr hab)
  have heq : (1 + ‖ξ‖ ^ 2) ^ (-b) =
      (1 + ‖ξ‖ ^ 2) ^ (a - b) * (1 + ‖ξ‖ ^ 2) ^ (-a) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  rw [heq]
  calc
    _ = (1 + ‖ξ‖ ^ 2) ^ (a - b) *
        (((2 * Real.pi)⁻¹ ^ 2) * ((1 + ‖ξ‖ ^ 2) ^ (-a) *
          ‖localizedFourier T χ ξ‖ ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hw (by positivity)

/-- On a bounded frequency ball, convergence of all pairings and uniform local energy bounds
imply convergence of the Fourier energy integral. -/
theorem tendsto_setLIntegral_localEnergyDensity_zero
    (a b : ℝ) (hb : 0 ≤ b) (T : ℕ → Distr) (χ : TestFn) (R : ℝ)
    (hpair : ∀ φ : TestFn, Tendsto (fun n => T n φ) atTop (𝓝 0))
    (hT : ∀ m, ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
      ∀ n, localNegSobolevSq a (T n) (localizer m) ≤ B) :
    Tendsto (fun n => ∫⁻ ξ in Metric.closedBall (0 : Plane) R,
      localEnergyDensity b (T n) χ ξ) atTop (𝓝 0) := by
  let A := Metric.closedBall (0 : Plane) R
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_localizedFourier_bound a T χ A (isCompact_closedBall 0 R) hT
  let D : ℝ≥0∞ := ENNReal.ofReal (((2 * Real.pi)⁻¹ ^ 2) * B ^ 2)
  have hfinite : ∫⁻ _ : Plane, D ∂volume.restrict A ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by simpa [A] using ((isCompact_closedBall (0 : Plane) R).measure_lt_top
        (μ := volume)).ne)
  have hdom (n : ℕ) : localEnergyDensity b (T n) χ ≤ᵐ[volume.restrict A] fun _ => D := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with ξ hξ
    apply ENNReal.ofReal_le_ofReal
    have hsq : ‖localizedFourier (T n) χ ξ‖ ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hbound n ξ hξ) 2
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right (negSobolev_weight_le_one hb ξ) (sq_nonneg _)).trans
        (by simpa only [one_mul] using hsq)) (sq_nonneg _)
  have hpoint (ξ : Plane) :
      Tendsto (fun n => localEnergyDensity b (T n) χ ξ) atTop (𝓝 0) := by
    have hfourier : Tendsto (fun n => localizedFourier (T n) χ ξ) atTop (𝓝 0) := by
      simpa [localizedFourier] using
        (LocalSobolev.tendsto_localizedFourier_of_pairings
          (Tlim := (0 : Distr)) (fun φ => by simpa using hpair φ) χ ξ)
    have hnorm := ((hfourier.norm.pow 2).const_mul
      ((1 + ‖ξ‖ ^ 2) ^ (-b))).const_mul ((2 * Real.pi)⁻¹ ^ 2)
    simpa only [localEnergyDensity, Function.comp_def, norm_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto _).comp hnorm
  simpa using tendsto_lintegral_of_dominated_convergence (fun _ => D)
    (fun n => measurable_localEnergyDensity b (T n) χ) hdom hfinite
    (Filter.Eventually.of_forall hpoint)

/-- A uniformly bounded stronger local energy and convergence of test pairings force every
strictly weaker local energy to vanish. -/
theorem tendsto_localEnergy_zero_of_pairings_zero
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (T : ℕ → Distr)
    (hpair : ∀ φ : TestFn, Tendsto (fun n => T n φ) atTop (𝓝 0))
    (hT : ∀ m, ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
      ∀ n, localNegSobolevSq a (T n) (localizer m) ≤ B) (χ : TestFn) :
    Tendsto (fun n => localNegSobolevSq b (T n) χ) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_localEnergy_bound_of_localizer_bounds ha T hT χ
  have hbase : Tendsto (fun R : ℝ => 1 + R ^ 2) atTop atTop := by
    simpa only [add_comm] using
      tendsto_atTop_add_const_right atTop 1 (tendsto_pow_atTop (by decide : 2 ≠ 0))
  have hratio : Tendsto (fun R : ℝ => (1 + R ^ 2) ^ (a - b)) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp hbase
  have htail : Tendsto (fun R : ℝ =>
      ENNReal.ofReal ((1 + R ^ 2) ^ (a - b)) * B) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const
      ((ENNReal.continuous_ofReal.tendsto _).comp hratio) (Or.inr hB)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hhalf : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) / 2 :=
    ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨R, hR, hsmall⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    ((ENNReal.tendsto_nhds_zero.mp htail) _ hhalf)).exists
  let A := Metric.closedBall (0 : Plane) R
  have hlow := tendsto_setLIntegral_localEnergyDensity_zero a b (ha.trans hab.le)
    T χ R hpair hT
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hlow) _ hhalf] with n hn
  have hhigh : ∫⁻ ξ in Aᶜ, localEnergyDensity b (T n) χ ξ ≤
      ENNReal.ofReal ((1 + R ^ 2) ^ (a - b)) * B := by
    calc
      _ ≤ ∫⁻ ξ in Aᶜ, ENNReal.ofReal ((1 + R ^ 2) ^ (a - b)) *
          localEnergyDensity a (T n) χ ξ := by
        apply setLIntegral_mono' measurableSet_closedBall.compl
        intro ξ hξ
        apply localEnergyDensity_le_tail_factor hab.le hR
        exact le_of_lt (by simpa [A, Metric.mem_closedBall, dist_zero_right]
          using hξ)
      _ = ENNReal.ofReal ((1 + R ^ 2) ^ (a - b)) *
          ∫⁻ ξ in Aᶜ, localEnergyDensity a (T n) χ ξ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((1 + R ^ 2) ^ (a - b)) * B :=
        mul_le_mul' le_rfl ((setLIntegral_le_lintegral _ _).trans
          (by rw [lintegral_localEnergyDensity]; exact hbound n))
  calc
    localNegSobolevSq b (T n) χ =
        (∫⁻ ξ in A, localEnergyDensity b (T n) χ ξ) +
          ∫⁻ ξ in Aᶜ, localEnergyDensity b (T n) χ ξ := by
      rw [lintegral_add_compl _ measurableSet_closedBall, lintegral_localEnergyDensity]
    _ ≤ (δ : ℝ≥0∞) / 2 + (δ : ℝ≥0∞) / 2 := add_le_add hn (hhigh.trans hsmall)
    _ = (δ : ℝ≥0∞) := ENNReal.add_halves _
    _ ≤ ε := hδε.le

end Critical2DKPZ.Analysis.Sobolev

end
