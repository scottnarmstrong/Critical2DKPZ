/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BandAverageBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

/-! # Radius derivatives of band averages in random L2 -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The first derivative bound remains valid at every positive band scale,
including the large coarse bands in the first window. -/
theorem norm_fderiv_bandPairing_le (hD : StationarySpectralData P D ν)
    {a : ℝ} (ha : 0 < a) (y : Plane) :
    ‖fderiv ℝ (fun y => schwartzExt hD (zetaScaled a y)) y‖ ≤
      Real.sqrt (specMass ν (2 / a)) * (2 / a) := by
  let : IsLocallyFiniteMeasure ν := hD.locFin
  let : ν.HasTemperateGrowth := temperateGrowth_of_spectralData P D ν hD
  obtain ⟨S, hSn, hS⟩ := exists_band_phase_factorization P ν
    (schwartzExt hD) (schwartzExt_covariance hD) a ha
  have heq : (fun y => schwartzExt hD (zetaScaled a y)) =
      S ∘ compactPhase (2 / a) (by positivity) := funext hS
  have hd : ‖iteratedFDeriv ℝ 1 (fun y => schwartzExt hD (zetaScaled a y)) y‖ ≤
      Real.sqrt (specMass ν (2 / a)) * (2 / a) := by
    rw [heq, S.iteratedFDeriv_comp_left (contDiff_compactPhase _ _).contDiffAt (by simp)]
    exact (S.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul hSn (by simpa only [pow_one] using
        norm_iteratedFDeriv_compactPhase (2 / a) (by positivity) 1 y)
        (norm_nonneg _) (Real.sqrt_nonneg _))
  simpa only [norm_iteratedFDeriv_one] using hd

/-- The radius derivative before spatial integration. -/
def bandAverageDerivativeIntegrand (hD : StationarySpectralData P D ν)
    (a : ℝ) (φ : TestFn) (x : Plane) (r : ℝ) (z : Plane) : Lp ℝ 2 P :=
  φ z • fderiv ℝ (fun y => schwartzExt hD (zetaScaled a y)) (x + r • z) z

/-- Differentiation of a band average in its radius. -/
def bandAverageDerivative (hD : StationarySpectralData P D ν)
    (a : ℝ) (φ : TestFn) (x : Plane) (r : ℝ) : Lp ℝ 2 P :=
  ∫ z : Plane, bandAverageDerivativeIntegrand hD a φ x r z

/-- Joint continuity of the differentiated integrand. -/
theorem continuous_bandAverageDerivativeIntegrand (hD : StationarySpectralData P D ν)
    {a : ℝ} (ha : 0 < a) (φ : TestFn) (x : Plane) :
    Continuous (fun p : ℝ × Plane => bandAverageDerivativeIntegrand hD a φ x p.1 p.2) := by
  have hc := contDiff_bandPairing P D ν hD (schwartzExt hD) (schwartzExt_fieldSpec hD) a ha
  have hd : Continuous (fderiv ℝ (fun y => schwartzExt hD (zetaScaled a y))) :=
    (hc.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  exact (φ.continuous.comp continuous_snd).smul
    ((hd.comp (continuous_const.add (continuous_fst.smul continuous_snd))).clm_apply continuous_snd)

/-- A common integrable bound for radius derivatives, independent of the radius. -/
theorem norm_bandAverageDerivativeIntegrand_le (hD : StationarySpectralData P D ν)
    {a : ℝ} (ha : 0 < a) (φ : TestFn) (x : Plane) (r : ℝ) (z : Plane) :
    ‖bandAverageDerivativeIntegrand hD a φ x r z‖ ≤
      (Real.sqrt (specMass ν (2 / a)) * (2 / a)) * (|φ z| * ‖z‖) := by
  rw [bandAverageDerivativeIntegrand, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |φ z| * (‖fderiv ℝ (fun y => schwartzExt hD (zetaScaled a y)) (x + r • z)‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (abs_nonneg _)
    _ ≤ |φ z| * ((Real.sqrt (specMass ν (2 / a)) * (2 / a)) * ‖z‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (norm_fderiv_bandPairing_le hD ha _) (norm_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

/-- Radius differentiation under the compact spatial integral, in random L2. -/
theorem hasDerivAt_bandAverage (hD : StationarySpectralData P D ν)
    {a : ℝ} (ha : 0 < a) (φ : TestFn) (x : Plane) (r : ℝ) :
    HasDerivAt (bandAverage hD a φ x) (bandAverageDerivative hD a φ x r) r := by
  have hc := contDiff_bandPairing P D ν hD (schwartzExt hD) (schwartzExt_fieldSpec hD) a ha
  have hm (q : ℝ) : AEStronglyMeasurable
      (fun z : Plane => φ z • schwartzExt hD (zetaScaled a (x + q • z))) volume := by
    exact ((φ.continuous).smul (hc.continuous.comp
      (continuous_const.add (continuous_const_smul q)))).aestronglyMeasurable
  have hi : Integrable (fun z : Plane => φ z • schwartzExt hD (zetaScaled a (x + r • z))) := by
    have hh := (schwartzField_average_ae_eq hD (zetaScaled a 0) φ x r).1
    have heq : (fun z : Plane => φ z • schwartzExt hD
        (translateSchwartz (x + r • z) (zetaScaled a 0))) =
        (fun z : Plane => φ z • schwartzExt hD (zetaScaled a (x + r • z))) := by
      funext z
      rw [← zetaScaled_eq_translate]
    rw [heq] at hh
    exact hh
  have hdm (q : ℝ) : AEStronglyMeasurable (bandAverageDerivativeIntegrand hD a φ x q) volume :=
    ((continuous_bandAverageDerivativeIntegrand hD ha φ x).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hdiff (z : Plane) (q : ℝ) : HasDerivAt
      (fun t : ℝ => φ z • schwartzExt hD (zetaScaled a (x + t • z)))
      (bandAverageDerivativeIntegrand hD a φ x q z) q := by
    have hs : HasDerivAt (fun t : ℝ => x + t • z) z q := by
      convert ((hasDerivAt_id q).smul_const z).const_add x using 1 <;> simp only [id_eq, one_smul]
    exact ((hc.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt q hs).const_smul (φ z)
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) univ_mem
    (Eventually.of_forall hm) hi (hdm r)
    (Eventually.of_forall (fun z q _ => norm_bandAverageDerivativeIntegrand_le hD ha φ x q z))
    ((integrable_testFirstMoment φ).const_mul _) (Eventually.of_forall (fun z q _ => hdiff z q))).2
  convert hh using 1
  · funext q
    unfold bandAverage smoothSchwartzAverage
    apply integral_congr_ae
    filter_upwards [] with z
    rw [← zetaScaled_eq_translate]
  · rfl

/-- The derivative norm is bounded by the first absolute spatial moment. -/
theorem norm_bandAverageDerivative_le (hD : StationarySpectralData P D ν)
    {a : ℝ} (ha : 0 < a) (φ : TestFn) (x : Plane) (r : ℝ) :
    ‖bandAverageDerivative hD a φ x r‖ ≤
      (Real.sqrt (specMass ν (2 / a)) * (2 / a)) * testFirstMoment φ := by
  calc
    _ ≤ ∫ z : Plane, (Real.sqrt (specMass ν (2 / a)) * (2 / a)) * (|φ z| * ‖z‖) := by
      apply norm_integral_le_of_norm_le ((integrable_testFirstMoment φ).const_mul _)
      exact Eventually.of_forall (norm_bandAverageDerivativeIntegrand_le hD ha φ x r)
    _ = _ := by rw [integral_const_mul]; rfl

/-- The L2 radius derivative is continuous, enabling primitive versions. -/
theorem continuous_bandAverageDerivative (hD : StationarySpectralData P D ν)
    {a : ℝ} (ha : 0 < a) (φ : TestFn) (x : Plane) :
    Continuous (bandAverageDerivative hD a φ x) := by
  apply continuous_of_dominated
    (fun r => ((continuous_bandAverageDerivativeIntegrand hD ha φ x).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (fun r => Eventually.of_forall (norm_bandAverageDerivativeIntegrand_le hD ha φ x r))
    ((integrable_testFirstMoment φ).const_mul _)
  exact Eventually.of_forall fun z =>
    (continuous_bandAverageDerivativeIntegrand hD ha φ x).comp
      (continuous_id.prodMk continuous_const)

end Critical2DKPZ.Extensions.ScaleLimit
