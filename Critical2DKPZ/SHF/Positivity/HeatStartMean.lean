/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.FlatBound
public import Critical2DKPZ.SHF.Limit.Marginal
public import Critical2DKPZ.Analysis.Heat.Semigroup
public import Critical2DKPZ.SHF.Limit.LocalFinite
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Exact annealed means for integrable heat-start profiles -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Positivity

open Critical2DKPZ.SHF.Limit

/-- At positive lattice scale, pairing a Lebesgue-integrable profile with the polymer first marginal gives an integrable random variable whose expectation is the Lebesgue integral of the profile. -/
theorem integral_flat_polymerMeasure_pairing_eq (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s t : ℝ) (f : Plane → ℝ) (hf : Integrable f volume) :
    Integrable (fun ω => ∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) disorderLaw ∧
    (∫ ω, ∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst) ∂disorderLaw) = ∫ x, f x := by
  let G : Plane × Disorder → ℝ := fun q => f q.1 * rescaledP2Plane ϑ N s t q.1 q.2
  have hG : Integrable G (volume.prod disorderLaw) := by
    exact integrable_flatPairingProduct ϑ N s t hf
  have hGswap : Integrable (fun q : Disorder × Plane => G (q.2, q.1))
      (disorderLaw.prod volume) := hG.swap
  have hRand : Integrable (fun ω : Disorder => ∫ x, G (x, ω) ∂volume) disorderLaw := by
    simpa only [G, Prod.fst, Prod.snd] using hGswap.integral_prod_left
  have hEq : (fun ω : Disorder =>
      ∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) =ᵐ[disorderLaw]
      (fun ω => ∫ x, G (x, ω) ∂volume) := by
    filter_upwards [] with ω
    exact integral_map_fst_polymerMeasure ϑ hN s t ω f
  constructor
  · exact hRand.congr hEq.symm
  · calc
      (∫ ω, ∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst) ∂disorderLaw)
          = ∫ ω, ∫ x, G (x, ω) ∂volume ∂disorderLaw := integral_congr_ae hEq
      _ = ∫ x, ∫ ω, G (x, ω) ∂disorderLaw ∂volume := integral_integral_swap hGswap
      _ = ∫ x, f x := by
          apply integral_congr_ae
          filter_upwards [] with x
          simp_rw [G, integral_const_mul, integral_rescaledP2Plane, mul_one]

/-- At positive lattice scale, the polymer heat-start pairing has expectation one. -/
theorem integral_polymer_heat_start_eq_one (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s t δ : ℝ) (hδ : 0 < δ) (x : Plane) :
    Integrable (fun ω => ∫ y, heatKernel δ (y - x)
      ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) disorderLaw ∧
    (∫ ω, ∫ y, heatKernel δ (y - x)
      ∂((polymerMeasure ϑ N s t ω).map Prod.fst) ∂disorderLaw) = 1 := by
  have hf : Integrable (fun y : Plane => heatKernel δ (y - x)) volume :=
    (integrable_heatKernel hδ).comp_sub_right x
  have hm := integral_flat_polymerMeasure_pairing_eq ϑ hN s t
    (fun y => heatKernel δ (y - x)) hf
  simpa only [integral_heatKernel_sub hδ x] using hm

/-- For almost every disorder, a positive heat-start profile is integrable against the complete
polymer pair measure. -/
theorem ae_integrable_polymer_heat_start (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s t δ : ℝ) (hδ : 0 < δ) (x : Plane) :
    ∀ᵐ ω ∂disorderLaw,
      Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x))
        (polymerMeasure ϑ N s t ω) := by
  have hf : Integrable (fun y : Plane => heatKernel δ (y - x)) volume :=
    (integrable_heatKernel hδ).comp_sub_right x
  have hG : Integrable (fun q : Plane × Disorder =>
      heatKernel δ (q.1 - x) * rescaledP2Plane ϑ N s t q.1 q.2)
      (volume.prod disorderLaw) := by
    exact integrable_flatPairingProduct ϑ N s t hf
  have hswap := hG.swap
  have hslice := hswap.prod_right_ae
  filter_upwards [hslice] with ω hω
  have hDensityMeas : Measurable (fun y : Plane =>
      ENNReal.ofReal (rescaledP2Plane ϑ N s t y ω)) := by
    exact (measurable_uncurry_rescaledP2Plane ϑ N s t).of_uncurry_right.ennreal_ofReal
  have hMapIntegrable : Integrable (fun y : Plane => heatKernel δ (y - x))
      ((polymerMeasure ϑ N s t ω).map Prod.fst) := by
    rw [map_fst_polymerMeasure ϑ hN s t ω]
    apply (integrable_withDensity_iff hDensityMeas
      (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)).2
    have hslice' : Integrable (fun y : Plane =>
        heatKernel δ (y - x) * rescaledP2Plane ϑ N s t y ω) volume := by
      simpa only [Function.comp_apply, Prod.swap_prod_mk] using hω
    simpa only [ENNReal.toReal_ofReal (rescaledP2Plane_nonneg ϑ N s t _ _)]
      using hslice'
  exact (integrable_map_measure
      ((measurable_heatKernel δ).comp (measurable_id.sub_const x)).aestronglyMeasurable
    measurable_fst.aemeasurable).mp hMapIntegrable

/-- The complete polymer heat-start pairing is integrable in disorder and has exact mean one. -/
theorem integral_polymer_heat_start_pairing_eq_one (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s t δ : ℝ) (hδ : 0 < δ) (x : Plane) :
    Integrable (fun ω => ∫ p, heatKernel δ (p.1 - x) ∂(polymerMeasure ϑ N s t ω)) disorderLaw ∧
    (∫ ω, ∫ p, heatKernel δ (p.1 - x) ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw) = 1 := by
  have hMarg := integral_polymer_heat_start_eq_one ϑ hN s t δ hδ x
  have hae := ae_integrable_polymer_heat_start ϑ hN s t δ hδ x
  have hPairEq : (fun ω =>
      ∫ p, heatKernel δ (p.1 - x) ∂(polymerMeasure ϑ N s t ω)) =ᵐ[disorderLaw]
      (fun ω => ∫ y, heatKernel δ (y - x)
        ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) := by
    filter_upwards [hae] with ω hω
    exact (integral_map measurable_fst.aemeasurable
      ((measurable_heatKernel δ).comp (measurable_id.sub_const x)).aestronglyMeasurable).symm
  constructor
  · exact hMarg.1.congr hPairEq.symm
  · calc
      (∫ ω, ∫ p, heatKernel δ (p.1 - x) ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw)
          = ∫ ω, ∫ y, heatKernel δ (y - x)
              ∂((polymerMeasure ϑ N s t ω).map Prod.fst) ∂disorderLaw :=
                integral_congr_ae hPairEq
      _ = 1 := hMarg.2

end Critical2DKPZ.SHF.Positivity

end
