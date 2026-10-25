/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralSmoothField
public import Critical2DKPZ.Extensions.ScaleLimit.BandKernelScaling
public import Critical2DKPZ.Extensions.ScaleLimit.SpectralContraction
public import Critical2DKPZ.Extensions.ScaleLimit.CompactFourierPhase
public import Critical2DKPZ.Extensions.ScaleLimit.CompactSpectralEmbedding
import Mathlib.Tactic

/-! # Smoothness and sharp derivative bounds for band pairings in `L²`

The band pairing factors through the exponential family in the Banach algebra
of continuous functions on the compact frequency ball. The spectral isometry
provides a contraction from spectral `L²` into random `L²`.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A band pairing is a bounded linear image of its phase on the frequency ball. -/
theorem exists_band_phase_factorization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure Plane) [IsLocallyFiniteMeasure ν] [ν.HasTemperateGrowth]
    (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P)
    (hE : ∀ f g, (∫ ω, E f ω * E g ω ∂P) =
      ∫ ξ, (Spectral.fourierKPZ f ξ * star (Spectral.fourierKPZ g ξ)).re ∂ν)
    (a : ℝ) (ha : 0 < a) :
    ∃ S : C(Metric.closedBall (0 : Plane) (2 / a), ℂ) →L[ℝ] Lp ℝ 2 P,
      ‖S‖ ≤ Real.sqrt (specMass ν (2 / a)) ∧
      ∀ y, E (zetaScaled a y) = S (compactPhase (2 / a) (by positivity) y) := by
  obtain ⟨T, hT, hTagree⟩ := exists_spectral_contraction P ν E hE
  let R : ℝ := 2 / a
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let c : C(Metric.closedBall (0 : Plane) R, ℂ) :=
    ⟨fun ξ => (chi (a • (ξ : Plane)) : ℂ), by fun_prop⟩
  have hc : ‖c‖ ≤ 1 := by
    apply (ContinuousMap.norm_le c zero_le_one).mpr
    intro ξ
    change ‖(chi (a • (ξ : Plane)) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (chi_bounds _).1]
    exact (chi_bounds _).2
  let M : C(Metric.closedBall (0 : Plane) R, ℂ) →L[ℝ] C(Metric.closedBall (0 : Plane) R, ℂ) :=
    ContinuousLinearMap.mul ℝ _ c
  have hM : ‖M‖ ≤ 1 := (ContinuousLinearMap.opNorm_mul_apply_le ℝ _ c).trans hc
  let J := compactSpectralEmbedding ν R
  let S := T.comp (J.comp M)
  have hJ : ‖J‖ ≤ Real.sqrt (specMass ν R) := norm_compactSpectralEmbedding_le ν R
  have hJM : ‖J.comp M‖ ≤ Real.sqrt (specMass ν R) := by
    calc
      ‖J.comp M‖ ≤ ‖J‖ * ‖M‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖J‖ * 1 := mul_le_mul_of_nonneg_left hM (norm_nonneg J)
      _ ≤ Real.sqrt (specMass ν R) := by simpa only [mul_one] using hJ
  refine ⟨S, ?_, ?_⟩
  · calc
      ‖S‖ ≤ ‖T‖ * ‖J.comp M‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖J.comp M‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg (J.comp M))
      _ ≤ Real.sqrt (specMass ν R) := by simpa only [one_mul] using hJM
  · intro y
    have heq : spectralLp (ν := ν) (zetaScaled a y) = J (M (compactPhase R hR y)) := by
      apply Lp.ext
      filter_upwards [spectralLp_ae_eq (ν := ν) (zetaScaled a y),
        compactSpectralEmbedding_ae_eq ν R (M (compactPhase R hR y))] with ξ hf hJf
      rw [hf, hJf, fourierKPZ_zetaScaled a ha]
      classical
      by_cases hξ : ξ ∈ Metric.closedBall (0 : Plane) R
      · simp only [compactSpectralFun, hξ, dite_true]
        change _ = (chi (a • ξ) : ℂ) * compactPhase R hR y ⟨ξ, hξ⟩
        rw [compactPhase_apply, mul_comm]
      · simp only [compactSpectralFun, hξ, dite_false]
        have hn : 2 ≤ ‖a • ξ‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
          have hh : R < ‖ξ‖ := lt_of_not_ge (fun h => hξ (mem_closedBall_zero_iff.mpr h))
          exact (div_le_iff₀ ha).mp hh.le |>.trans_eq (mul_comm _ _)
        rw [chi_eq_zero hn, Complex.ofReal_zero, mul_zero]
    rw [← hTagree (zetaScaled a y), heq]
    rfl

/-- Smoothness of the band pairing in the random `L²` norm, at every positive scale. -/
theorem contDiff_bandPairing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → Distr) (ν : Measure Plane)
    (hD : StationarySpectralData P D ν) (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P)
    (hE : SchwartzExtensionSpec P D ν E) (a : ℝ) (ha : 0 < a) :
    ContDiff ℝ ⊤ (fun y => E (zetaScaled a y)) := by
  let : IsLocallyFiniteMeasure ν := hD.locFin
  let : ν.HasTemperateGrowth := temperateGrowth_of_spectralData P D ν hD
  obtain ⟨S, _, hS⟩ := exists_band_phase_factorization P ν E hE.2.1 a ha
  have heq : (fun y => E (zetaScaled a y)) = S ∘ compactPhase (2 / a) (by positivity) := funext hS
  rw [heq]
  exact S.contDiff.comp (contDiff_compactPhase _ _)


end Critical2DKPZ.Extensions.ScaleLimit
