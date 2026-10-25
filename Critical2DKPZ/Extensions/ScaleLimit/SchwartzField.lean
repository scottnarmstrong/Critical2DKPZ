/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BandFieldDerivatives
public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzRandomPairing
import Critical2DKPZ.Extensions.ScaleLimit.StationaryFubini
import Critical2DKPZ.Extensions.ScaleLimit.MaximalDomination
import Mathlib.Tactic

/-! # Stationary Schwartz and band fields

The stationary field is constructed from the selected stochastic Schwartz extension.
All specifications are statements about measurable versions at fixed spatial points.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The stochastic Schwartz extension satisfies the stationary field hypotheses. -/
theorem schwartzExt_fieldSpec (hD : StationarySpectralData P D ν) :
    SchwartzExtensionSpec P D ν (schwartzExt hD) :=
  ⟨schwartzExt_test hD, schwartzExt_covariance hD, schwartzExt_stationary hD⟩

/-- A selected jointly measurable stationary version of the extended Schwartz pairing. -/
def schwartzField (hD : StationarySpectralData P D ν) (ψ : SchwartzMap Plane ℝ) : Plane → Ω → ℝ :=
  schwartzFieldOfExtension P D ν hD (schwartzExt hD) (schwartzExt_fieldSpec hD) ψ

/-- Joint measurability of the selected Schwartz field. -/
theorem schwartzField_measurable (hD : StationarySpectralData P D ν) (ψ : SchwartzMap Plane ℝ) :
    Measurable (Function.uncurry (schwartzField hD ψ)) :=
  measurable_schwartzFieldOfExtension P D ν hD _ (schwartzExt_fieldSpec hD) ψ

/-- At each spatial point the field represents the translated extended pairing. -/
theorem schwartzField_ae_eq (hD : StationarySpectralData P D ν) (ψ : SchwartzMap Plane ℝ) (y : Plane) :
    schwartzField hD ψ y =ᵐ[P] fun ω => schwartzExt hD (translateSchwartz y ψ) ω :=
  schwartzFieldOfExtension_ae_eq P D ν hD _ (schwartzExt_fieldSpec hD) ψ y

/-- Every spatial value is square integrable. -/
theorem schwartzField_memLp (hD : StationarySpectralData P D ν) (ψ : SchwartzMap Plane ℝ) (y : Plane) :
    MemLp (schwartzField hD ψ y) 2 P :=
  (Lp.memLp _).ae_eq (schwartzField_ae_eq hD ψ y).symm

/-- Full finite-family stationarity, not merely stationarity of one-point laws. -/
theorem schwartzField_stationary (hD : StationarySpectralData P D ν) (ψ : SchwartzMap Plane ℝ)
    (n : ℕ) (y : Fin n → Plane) (z : Plane) :
    IdentDistrib (fun ω i => schwartzField hD ψ (y i + z) ω)
      (fun ω i => schwartzField hD ψ (y i) ω) P P :=
  schwartzFieldOfExtension_stationary P D ν hD _ (schwartzExt_fieldSpec hD) ψ n y z

/-- Continuity in probability, the regularity premise needed by the maximal inequality. -/
theorem schwartzField_tendstoInMeasure (hD : StationarySpectralData P D ν)
    (ψ : SchwartzMap Plane ℝ) (y₀ : Plane) :
    TendstoInMeasure P (schwartzField hD ψ) (𝓝 y₀) (schwartzField hD ψ y₀) :=
  schwartzFieldOfExtension_tendstoInMeasure P D ν hD _ (schwartzExt_fieldSpec hD) ψ y₀

/-- The band field at scale `a`, chosen through the general Schwartz field. -/
def bandField (hD : StationarySpectralData P D ν) (a : ℝ) : Plane → Ω → ℝ :=
  schwartzField hD (zetaScaled a 0)


/-- Each band value is the corresponding extended scaled pairing almost surely. -/
theorem bandField_ae_eq (hD : StationarySpectralData P D ν) (a : ℝ) (y : Plane) :
    bandField hD a y =ᵐ[P] fun ω => schwartzExt hD (zetaScaled a y) ω :=
  bandFieldOfExtension_ae_eq P D ν hD _ (schwartzExt_fieldSpec hD) a y

/-- Every band value is square integrable. -/
theorem bandField_memLp (hD : StationarySpectralData P D ν) (a : ℝ) (y : Plane) :
    MemLp (bandField hD a y) 2 P := schwartzField_memLp hD _ y



/-- Linearity of the version at each spatial point; no common event for every test is claimed. -/
theorem schwartzField_sub_ae_eq (hD : StationarySpectralData P D ν)
    (ψ φ : SchwartzMap Plane ℝ) (y : Plane) :
    schwartzField hD (ψ - φ) y =ᵐ[P] fun ω => schwartzField hD ψ y ω - schwartzField hD φ y ω := by
  have htrans : translateSchwartz y (ψ - φ) = translateSchwartz y ψ - translateSchwartz y φ := by
    ext x
    simp only [translateSchwartz_apply, sub_apply]
  have hid := Lp.coeFn_sub (schwartzExt hD (translateSchwartz y ψ))
    (schwartzExt hD (translateSchwartz y φ))
  filter_upwards [schwartzField_ae_eq hD (ψ - φ) y, schwartzField_ae_eq hD ψ y,
    schwartzField_ae_eq hD φ y, hid] with ω hsub hψ hφ hLp
  rw [hsub, hψ, hφ, htrans, map_sub]
  exact hLp

/-- The jointly stationary field for a difference of band kernels represents the band difference. -/
theorem bandField_difference_ae_eq (hD : StationarySpectralData P D ν) (a b : ℝ) (y : Plane) :
    schwartzField hD (zetaScaled a 0 - zetaScaled b 0) y =ᵐ[P]
      fun ω => bandField hD a y ω - bandField hD b y ω :=
  schwartzField_sub_ae_eq hD _ _ y

/-- One-point stationarity, as a consequence of the full finite-family laws. -/
theorem schwartzField_identDistrib (hD : StationarySpectralData P D ν)
    (ψ : SchwartzMap Plane ℝ) (y : Plane) :
    IdentDistrib (schwartzField hD ψ y) (schwartzField hD ψ 0) P P := by
  have hs := (schwartzField_stationary hD ψ 1 (fun _ => 0) y).comp
    (measurable_pi_apply (0 : Fin 1))
  convert hs using 1 <;> funext ω <;> simp only [Function.comp_apply, zero_add]




end Critical2DKPZ.Extensions.ScaleLimit
