/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.RadialInversionAsymptotic
public import Critical2DKPZ.CovarianceKernel.Envelope

/-! # Local square integrability of the Bessel inversion -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.CovarianceKernel

/-- The compensated inversion is nonnegative at the origin: its Bessel factor is one there, so
the remaining integrand is the indicator of the complement of the unit ball. -/
theorem besselInversion_nonneg_at_zero (ν : Measure Plane) :
    0 ≤ besselInversion ν 0 := by
  have hJ : Spectral.besselJ0Angular 0 = 1 := by
    unfold Spectral.besselJ0Angular
    have hf : (fun z : ℂ => Real.cos (0 * z.re)) = fun _ => (1 : ℝ) := by
      funext z
      simp
    rw [hf, Real.circleAverage_const]
  have hterm : ∀ ξ : Plane, 0 ≤
      Spectral.besselJ0Angular (‖ξ‖ * ‖(0 : Plane)‖) -
        (Metric.closedBall (0 : Plane) 1).indicator 1 ξ := by
    intro ξ
    by_cases hξ : ξ ∈ Metric.closedBall (0 : Plane) 1
    · simp [hξ, hJ]
    · simp [hξ, hJ]
  unfold besselInversion
  exact add_nonneg ENNReal.toReal_nonneg (integral_nonneg hterm)

/-- The diagonal asymptotic controls the inversion near the origin; continuity controls it on the
remaining part of every compact set. -/
theorem besselInversion_memLp_two_on_compact_of_ballMass (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν]
    (hM : Tendsto (fun R => spectralBallMass ν R / Real.log (Real.log R)) atTop (𝓝 1))
    (K : Set Plane) (hK : IsCompact K) :
    MemLp (besselInversion ν) 2 (volume.restrict K) := by
  let F : Plane → ℝ := besselInversion ν
  let L : Plane → ℝ := covarianceLogEnvelope
  obtain ⟨A, hA, hGrowth⟩ := spectralBallMass_logGrowth_of_tendsto ν hM
  have hdiag := besselInversion_diagonal_asymptotic_of_ballMass ν hM
  have hcont := continuousOn_besselInversion_of_logGrowth ν hA hGrowth
  have hFmeas : Measurable F := by
    dsimp [F]
    apply hcont.measurable_of_countable_compl
    simp
  have hFae : AEStronglyMeasurable F (volume.restrict K) :=
    hFmeas.aestronglyMeasurable.restrict
  have hLmem : MemLp L 2 (volume.restrict K) := by
    simpa [L] using covarianceLogEnvelope_memLp_two_on_compact K hK
  have hratioEvent : ∀ᶠ z : Plane in nhdsWithin 0 {0}ᶜ,
      F z / Real.log (Real.log ‖z‖⁻¹) ∈ Set.Ioo (1 / 2) 2 := by
    simpa only [F, Set.mem_Ioo] using hdiag.eventually
      (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨δ, hδ, hδsubset⟩ := Metric.mem_nhdsWithin_iff.mp hratioEvent
  have hδpos : 0 < δ := hδ
  let δ₀ : ℝ := Real.exp (-Real.exp 1)
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  let ρ : ℝ := min δ δ₀
  have hρ : 0 < ρ := lt_min hδpos hδ₀
  let Kfar : Set Plane := K \ Metric.ball (0 : Plane) ρ
  have hKfar : IsCompact Kfar := by
    dsimp [Kfar]
    exact hK.diff Metric.isOpen_ball
  have hfarNonzero : ∀ z ∈ Kfar, z ≠ 0 := by
    intro z hzKfar hz
    subst z
    have hzeroBall : (0 : Plane) ∈ Metric.ball (0 : Plane) ρ := by
      simpa [Metric.mem_ball, dist_self] using hρ
    exact hzKfar.2 hzeroBall
  have hFabsCont : ContinuousOn (fun z : Plane => |F z|) Kfar := by
    have hFabs : ContinuousOn (fun z : Plane => |F z|) ({0}ᶜ : Set Plane) := by
      simpa only [F] using hcont.abs
    exact hFabs.mono (by intro z hz; exact hfarNonzero z hz)
  obtain ⟨B₀, hB₀⟩ := hKfar.bddAbove_image hFabsCont
  change ∀ y ∈ (fun z : Plane => |F z|) '' Kfar, y ≤ B₀ at hB₀
  let B : ℝ := max B₀ 0
  let C : ℝ := max 2 B
  have hB : 0 ≤ B := le_max_right _ _
  have hC : 0 ≤ C := le_trans (by norm_num) (le_max_left _ _)
  have hC2 : 2 ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  have hEnvOne : ∀ z : Plane, 1 ≤ L z := by
    intro z
    have hmax : 0 ≤ max 0 (Real.log ‖z‖⁻¹) := le_max_left _ _
    have hlog : 0 ≤ Real.log (1 + max 0 (Real.log ‖z‖⁻¹)) :=
      Real.log_nonneg (by linarith)
    dsimp [L, covarianceLogEnvelope]
    linarith
  have hpoint : ∀ z ∈ K, z ≠ 0 → |F z| ≤ C * L z := by
    intro z hzK hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    by_cases hnear : ‖z‖ < ρ
    · have hzδ : ‖z‖ < δ := lt_of_lt_of_le hnear (min_le_left _ _)
      have hzδ₀ : ‖z‖ < δ₀ := lt_of_lt_of_le hnear (min_le_right _ _)
      have hzball : z ∈ Metric.ball (0 : Plane) δ := by
        simpa [Metric.mem_ball, dist_zero_right] using hzδ
      have hratio : F z / Real.log (Real.log ‖z‖⁻¹) ∈ Set.Ioo (1 / 2) 2 :=
        hδsubset ⟨hzball, by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz⟩
      have hinv : Real.exp (Real.exp 1) < ‖z‖⁻¹ := by
        have h := one_div_lt_one_div_of_lt hzpos hzδ₀
        simpa [δ₀, Real.exp_neg] using h
      have hlog1 : Real.exp 1 < Real.log ‖z‖⁻¹ :=
        (Real.lt_log_iff_exp_lt (inv_pos.mpr hzpos)).2 hinv
      have hloglog : 1 < Real.log (Real.log ‖z‖⁻¹) := by
        have h := Real.log_lt_log (by positivity : 0 < Real.exp 1) hlog1
        simpa using h
      have hloglogPos : 0 < Real.log (Real.log ‖z‖⁻¹) := hloglog.trans_le' (by norm_num)
      have hFpos : 0 < F z := by
        have hmul := (lt_div_iff₀ hloglogPos).1 hratio.1
        nlinarith
      have hFupper : F z ≤ 2 * Real.log (Real.log ‖z‖⁻¹) := by
        exact (div_lt_iff₀ hloglogPos).1 hratio.2 |>.le
      have hEnvLog : Real.log (Real.log ‖z‖⁻¹) ≤ L z := by
        have hmax : max 0 (Real.log ‖z‖⁻¹) = Real.log ‖z‖⁻¹ :=
          max_eq_right (le_of_lt (lt_trans (by positivity) hlog1))
        have hloginvPos : 0 < Real.log ‖z‖⁻¹ :=
          lt_trans (by positivity : (0 : ℝ) < Real.exp 1) hlog1
        have hlogadd : Real.log ‖z‖⁻¹ ≤ 1 + Real.log ‖z‖⁻¹ := by linarith
        have hlog : Real.log (Real.log ‖z‖⁻¹) ≤
            Real.log (1 + Real.log ‖z‖⁻¹) := Real.log_le_log hloginvPos hlogadd
        dsimp [L, covarianceLogEnvelope]
        rw [hmax]
        linarith
      have habs : |F z| = F z := abs_of_pos hFpos
      rw [habs]
      calc
        F z ≤ 2 * Real.log (Real.log ‖z‖⁻¹) := hFupper
        _ ≤ 2 * L z := mul_le_mul_of_nonneg_left hEnvLog (by norm_num)
        _ ≤ C * L z := mul_le_mul_of_nonneg_right hC2 (le_of_lt (covarianceLogEnvelope_pos z))
    · have hzfar : z ∈ Kfar := by
        refine ⟨hzK, ?_⟩
        intro hzball
        have hzlt : ‖z‖ < ρ := by
          simpa [Metric.mem_ball, dist_zero_right] using hzball
        exact (not_lt_of_ge (le_of_not_gt hnear)) hzlt
      have hbound : |F z| ≤ B₀ := hB₀ _ ⟨z, hzfar, rfl⟩
      have hBbound : |F z| ≤ B := hbound.trans (le_max_left _ _)
      calc
        |F z| ≤ B := hBbound
        _ ≤ B * L z := by
          calc
            B = B * 1 := by ring
            _ ≤ B * L z := mul_le_mul_of_nonneg_left (hEnvOne z) hB
        _ ≤ C * L z := mul_le_mul_of_nonneg_right hBC (le_of_lt (covarianceLogEnvelope_pos z))
  have hboundAE : ∀ᵐ z : Plane ∂volume.restrict K,
      ‖F z‖ ≤ C * ‖L z‖ := by
    filter_upwards [ae_restrict_mem hK.measurableSet,
      ae_restrict_of_ae (volume.ae_ne (0 : Plane))] with z hzK hz
    have h := hpoint z hzK hz
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (covarianceLogEnvelope_pos z))]
    exact h
  exact MemLp.of_le_mul hLmem hFae hboundAE

end Critical2DKPZ.CovarianceKernel

end
