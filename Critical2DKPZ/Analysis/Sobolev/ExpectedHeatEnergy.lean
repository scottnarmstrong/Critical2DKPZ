/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.GammaMixture
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Tactic.FunProp

/-!
# Expected negative Sobolev energies

Weak measurability of real distribution evaluations implies joint measurability of the localized
Fourier transform. All nonnegative expectation/heat-time interchanges then follow from Tonelli.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ

/-- A weakly measurable random distribution has a jointly measurable localized Fourier transform. -/
theorem measurable_localizedFourier_uncurry {Ω : Type*} [MeasurableSpace Ω] {T : Ω → Distr}
    (hT : ∀ φ : TestFn, Measurable (fun ω => T ω φ)) (χ : TestFn) :
    Measurable (fun p : Ω × Plane => localizedFourier (T p.1) χ p.2) := by
  have hm : Measurable (fun p : Plane × Ω => localizedFourier (T p.2) χ p.1) := by
    apply measurable_uncurry_of_continuous_of_measurable
      (fun ω => continuous_localizedFourier (T ω) χ)
    intro ξ
    exact (Complex.measurable_ofReal.comp (hT (χ.mulCos ξ))).sub
      (measurable_const.mul (Complex.measurable_ofReal.comp (hT (χ.mulSin ξ))))
  exact hm.comp measurable_swap

/-- The localized negative Sobolev energy of a weakly measurable distribution family is measurable. -/
theorem measurable_localNegSobolevSq {Ω : Type*} [MeasurableSpace Ω] {T : Ω → Distr}
    (hT : ∀ φ : TestFn, Measurable (fun ω => T ω φ)) (a : ℝ) (χ : TestFn) :
    Measurable (fun ω => localNegSobolevSq a (T ω) χ) := by
  have hF := measurable_localizedFourier_uncurry hT χ
  have hw : Measurable (fun ξ : Plane => (1 + ‖ξ‖ ^ 2) ^ (-a)) := by fun_prop
  have hm : Measurable (fun p : Ω × Plane => ENNReal.ofReal
      ((1 + ‖p.2‖ ^ 2) ^ (-a) * ‖localizedFourier (T p.1) χ p.2‖ ^ 2)) :=
    ((hw.comp measurable_snd).mul (hF.norm.pow_const 2)).ennreal_ofReal
  have hi := hm.lintegral_prod_right' (ν := volume)
  simpa only [localNegSobolevSq, norm_localizedFourier_sq] using hi.const_mul
    (ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2))

/-- Joint measurability includes the heat-time parameter. -/
theorem measurable_heatDampedFourierEnergy_uncurry {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Distr} (hT : ∀ φ : TestFn, Measurable (fun ω => T ω φ)) (χ : TestFn) :
    Measurable (fun p : Ω × ℝ => heatDampedFourierEnergy p.2 (T p.1) χ) := by
  have hF := (measurable_localizedFourier_uncurry hT χ).comp
    (measurable_fst.fst.prodMk measurable_snd :
      Measurable (fun p : (Ω × ℝ) × Plane => (p.1.1, p.2)))
  have hk : Measurable (fun p : (Ω × ℝ) × Plane =>
      ENNReal.ofReal (Real.exp (-p.1.2 * ‖p.2‖ ^ 2))) := by fun_prop
  have hm := hk.mul (hF.norm.pow_const 2).ennreal_ofReal
  exact hm.lintegral_prod_right'.const_mul (ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2))

/-- The expected local negative Sobolev energy is the Gamma mixture of expected heat-damped energies, with both sides interpreted as extended nonnegative integrals. -/
theorem lintegral_localNegSobolevSq_eq_gamma_mixture {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {T : Ω → Distr}
    (hT : ∀ φ : TestFn, Measurable (fun ω => T ω φ)) {a : ℝ} (ha : 0 < a) (χ : TestFn) :
    ∫⁻ ω, localNegSobolevSq a (T ω) χ ∂μ =
      ENNReal.ofReal (Real.Gamma a)⁻¹ *
        ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u)) *
          ∫⁻ ω, heatDampedFourierEnergy u (T ω) χ ∂μ := by
  have hw : Measurable (fun p : Ω × ℝ =>
      ENNReal.ofReal (p.2 ^ (a - 1) * Real.exp (-p.2))) := by fun_prop
  have hm := hw.mul (measurable_heatDampedFourierEnergy_uncurry hT χ)
  simp_rw [localNegSobolevSq_eq_gamma_mixture ha]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_lintegral_swap hm.aemeasurable]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [] with u
  exact lintegral_const_mul _ ((measurable_heatDampedFourierEnergy_uncurry hT χ).comp
    (measurable_id.prodMk measurable_const))

end Critical2DKPZ

end
