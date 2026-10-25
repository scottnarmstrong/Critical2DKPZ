/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.ClockConvergence

/-! # Second moments and changes of width and mollifier -/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The normalized canonical clock is constant in the large parameter. -/
theorem tendsto_scaleRadius_clock (s : ℝ) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      (L : ℝ)⁻¹ * Real.log (Real.log (scaleRadius L s)⁻¹)) atTop (𝓝 s) := by
  have heq : (fun L : Set.Ioi (0 : ℝ) =>
      (L : ℝ)⁻¹ * Real.log (Real.log (scaleRadius L s)⁻¹)) = fun _ => s := by
    funext L
    rw [log_log_inv_scaleRadius, ← mul_assoc, inv_mul_cancel₀ L.property.ne', one_mul]
  rw [heq]
  exact tendsto_const_nhds

/-- The increment covariance of Brownian motion gives its usual absolute-distance variance. -/
theorem add_sub_two_mul_min (s s' : ℝ) : s + s' - 2 * min s s' = |s - s'| := by
  rcases le_total s s' with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

variable (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
  (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
  (t : ℝ) (ht : 0 < t)

include hZ hH ht

/-- Expanding a squared tested increment gives two variances and a cross covariance. -/
theorem integral_increment_sq_eq_covariance (f g : TestFn) :
    (∫ ω, (H t 0 ω f - H t 0 ω g) ^ 2 ∂P) =
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω f; P] +
      cov[fun ω => H t 0 ω g, fun ω => H t 0 ω g; P] -
      2 * cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] := by
  have hf := memLp_kpz_two ϑ P Z hZ H hH t ht f
  have hg := memLp_kpz_two ϑ P Z hZ H hH t ht g
  have hfg : Integrable (fun ω => H t 0 ω f * H t 0 ω g) P := hf.integrable_mul hg
  have heq : (fun ω => (H t 0 ω f - H t 0 ω g) ^ 2) =
      fun ω => (H t 0 ω f) ^ 2 + (H t 0 ω g) ^ 2 - 2 * (H t 0 ω f * H t 0 ω g) := by
    funext ω
    ring
  have hsum : Integrable (fun ω => (H t 0 ω f) ^ 2 + (H t 0 ω g) ^ 2) P :=
    hf.integrable_sq.add hg.integrable_sq
  rw [heq, integral_sub hsum (hfg.const_mul 2),
    integral_add hf.integrable_sq hg.integrable_sq, integral_const_mul]
  simp_rw [pow_two, integral_mul_kpz_eq_covariance ϑ P Z hZ H hH t ht]

/-- Canonical widths have the Brownian covariance clock. -/
theorem covariance_clock_scaleRadius (φ ψ : TestFn)
    (hφ : ∀ u, 0 ≤ φ u) (hψ : ∀ v, 0 ≤ ψ v)
    (hφmass : (∫ u, φ u) = 1) (hψmass : (∫ v, ψ v) = 1)
    (x : Plane) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)⁻¹ *
      cov[fun ω => H t 0 ω (φ.dilate (scaleRadius L s) x),
        fun ω => H t 0 ω (ψ.dilate (scaleRadius L s') x); P]) atTop (𝓝 (min s s')) :=
  covariance_clock ϑ P Z hZ H hH t ht φ ψ hφ hψ hφmass hψmass x
    (fun L => scaleRadius_pos L s) (fun L => scaleRadius_pos L s')
    (Eventually.of_forall fun L => scaleRadius_lt_one L s)
    (Eventually.of_forall fun L => scaleRadius_lt_one L s') hs hs'
    (tendsto_scaleRadius_clock s) (tendsto_scaleRadius_clock s')

/-- The second moment at a fixed positive scale time converges to that time. -/
theorem tendsto_second_moment_scaled (φ : TestFn) (hφ : ∀ u, 0 ≤ φ u)
    (hφmass : (∫ u, φ u) = 1) (x : Plane) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => ∫ ω, (scaledPairing (H t 0 ω) φ x L s) ^ 2 ∂P)
      atTop (𝓝 s) := by
  have hc := covariance_clock_scaleRadius ϑ P Z hZ H hH t ht φ φ hφ hφ hφmass hφmass x hs hs
  simp only [min_self] at hc
  apply hc.congr
  intro L
  simp_rw [scaledPairing, div_pow]
  rw [integral_div, Real.sq_sqrt L.property.le]
  simp_rw [pow_two, integral_mul_kpz_eq_covariance ϑ P Z hZ H hH t ht]
  rw [div_eq_mul_inv, mul_comm]

/-- Canonical scaled increments have the second moments of Brownian increments. -/
theorem tendsto_second_moment_increment (φ : TestFn) (hφ : ∀ u, 0 ≤ φ u)
    (hφmass : (∫ u, φ u) = 1) (x : Plane) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => ∫ ω,
      (scaledPairing (H t 0 ω) φ x L s - scaledPairing (H t 0 ω) φ x L s') ^ 2 ∂P)
      atTop (𝓝 |s - s'|) := by
  have hss := covariance_clock_scaleRadius ϑ P Z hZ H hH t ht φ φ hφ hφ hφmass hφmass x hs hs
  have htt := covariance_clock_scaleRadius ϑ P Z hZ H hH t ht φ φ hφ hφ hφmass hφmass x hs' hs'
  have hst := covariance_clock_scaleRadius ϑ P Z hZ H hH t ht φ φ hφ hφ hφmass hφmass x hs hs'
  have hl := (hss.add htt).sub (hst.const_mul 2)
  rw [min_self, min_self, add_sub_two_mul_min] at hl
  apply hl.congr
  intro L
  simp_rw [scaledPairing, ← sub_div, div_pow]
  rw [integral_div, Real.sq_sqrt L.property.le,
    integral_increment_sq_eq_covariance ϑ P Z hZ H hH t ht]
  ring

/-- Equal positive clocks allow changing both the mollifier and the width in L². -/
theorem tendsto_replacement_sq (φ ψ : TestFn)
    (hφ : ∀ u, 0 ≤ φ u) (hψ : ∀ v, 0 ≤ ψ v)
    (hφmass : (∫ u, φ u) = 1) (hψmass : (∫ v, ψ v) = 1) (x : Plane)
    {a b : Set.Ioi (0 : ℝ) → ℝ} {s : ℝ}
    (ha : ∀ L, 0 < a L) (hb : ∀ L, 0 < b L)
    (haone : ∀ᶠ L in atTop, a L < 1) (hbone : ∀ᶠ L in atTop, b L < 1) (hs : 0 < s)
    (hclocka : Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      (L : ℝ)⁻¹ * Real.log (Real.log (a L)⁻¹)) atTop (𝓝 s))
    (hclockb : Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      (L : ℝ)⁻¹ * Real.log (Real.log (b L)⁻¹)) atTop (𝓝 s)) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)⁻¹ * ∫ ω,
      (H t 0 ω (φ.dilate (a L) x) - H t 0 ω (ψ.dilate (b L) x)) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hss := covariance_clock ϑ P Z hZ H hH t ht φ φ hφ hφ hφmass hφmass x
    ha ha haone haone hs hs hclocka hclocka
  have htt := covariance_clock ϑ P Z hZ H hH t ht ψ ψ hψ hψ hψmass hψmass x
    hb hb hbone hbone hs hs hclockb hclockb
  have hst := covariance_clock ϑ P Z hZ H hH t ht φ ψ hφ hψ hφmass hψmass x
    ha hb haone hbone hs hs hclocka hclockb
  have hl := (hss.add htt).sub (hst.const_mul 2)
  have hzero : min s s + min s s - 2 * min s s = 0 := by ring
  rw [hzero] at hl
  apply hl.congr
  intro L
  rw [integral_increment_sq_eq_covariance ϑ P Z hZ H hH t ht]
  ring

end Critical2DKPZ.Extensions.ScaleLimit
