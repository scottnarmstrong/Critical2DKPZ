/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzSpectralLp
public import Critical2DKPZ.Spectral.BochnerSchwartzSquareCone
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Test pairings as real Hilbert space maps -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The value-preserving linear inclusion of tests into real Schwartz space. -/
def testSchwartzLinear : TestFn →ₗ[ℝ] SchwartzMap Plane ℝ where
  toFun := Spectral.testFnToRealSchwartz
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

/-- The Fourier map on the full Schwartz space, with values in spectral L². -/
def schwartzSpectralLp (ν : Measure Plane) [ν.HasTemperateGrowth] :
    SchwartzMap Plane ℝ →L[ℝ] Lp ℂ 2 ν :=
  (SchwartzMap.toLpCLM ℝ ℂ 2 ν).comp schwartzFourier

/-- The Fourier embedding of the original compact tests. -/
def testSpectralLp (ν : Measure Plane) [ν.HasTemperateGrowth] : TestFn →ₗ[ℝ] Lp ℂ 2 ν :=
  (schwartzSpectralLp ν).toLinearMap.comp testSchwartzLinear

/-- The original stochastic distribution, as a linear map into L². -/
def testRandomLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {D : Ω → Distr} {ν : Measure Plane} (hD : StationarySpectralData P D ν) :
    TestFn →ₗ[ℝ] Lp ℝ 2 P where
  toFun f := (hD.memLp f).toLp (fun ω => D ω f)
  map_add' f g := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
    exact ae_of_all P fun ω => map_add (D ω) f g
  map_smul' c f := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
    exact ae_of_all P fun ω => map_smul (D ω) c f

/-- The L² representative agrees with the original distribution on each test. -/
theorem testRandomLp_coe {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Ω → Distr} {ν : Measure Plane}
    (hD : StationarySpectralData P D ν) (f : TestFn) :
    (testRandomLp hD f : Ω → ℝ) =ᵐ[P] fun ω => D ω f :=
  (hD.memLp f).coeFn_toLp

/-- The spectral representative is the angular Fourier transform almost everywhere. -/
theorem schwartzSpectralLp_coe (ν : Measure Plane) [ν.HasTemperateGrowth]
    (f : SchwartzMap Plane ℝ) :
    (schwartzSpectralLp ν f : Plane → ℂ) =ᵐ[ν] Spectral.fourierKPZ f := by
  exact ((schwartzFourier f).coeFn_toLp 2 ν).trans
    (ae_of_all ν fun ξ => schwartzFourier_apply f ξ)

end Critical2DKPZ.Extensions.ScaleLimit
