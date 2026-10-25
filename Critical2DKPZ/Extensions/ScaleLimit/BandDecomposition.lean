/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzFubini
public import Critical2DKPZ.Extensions.ScaleLimit.TestPairingLp

/-! # The exact band decomposition as random L2 classes -/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- A compact spatial average of extended translated Schwartz pairings. -/
def smoothSchwartzAverage (hD : StationarySpectralData P D ν)
    (ψ : SchwartzMap Plane ℝ) (φ : TestFn) (x : Plane) (r : ℝ) : Lp ℝ 2 P :=
  ∫ z : Plane, φ z • schwartzExt hD (translateSchwartz (x + r • z) ψ)

/-- The averaged difference equals the difference of the averaged L2 classes. -/
theorem smoothSchwartzAverage_sub (hD : StationarySpectralData P D ν)
    (ψ χ : SchwartzMap Plane ℝ) (φ : TestFn) (x : Plane) (r : ℝ) :
    smoothSchwartzAverage hD (ψ - χ) φ x r =
      smoothSchwartzAverage hD ψ φ x r - smoothSchwartzAverage hD χ φ x r := by
  have hsub (z : Plane) : translateSchwartz z (ψ - χ) =
      translateSchwartz z ψ - translateSchwartz z χ := by
    ext y
    rfl
  simp only [smoothSchwartzAverage, hsub, map_sub, smul_sub]
  exact integral_sub (schwartzField_average_ae_eq hD ψ φ x r).1
    (schwartzField_average_ae_eq hD χ φ x r).1

/-- Stochastic Fubini identifies the Bochner average with the actual field average. -/
theorem smoothSchwartzAverage_ae_eq (hD : StationarySpectralData P D ν)
    (ψ : SchwartzMap Plane ℝ) (φ : TestFn) (x : Plane) (r : ℝ) :
    (smoothSchwartzAverage hD ψ φ x r : Ω → ℝ) =ᵐ[P]
      fun ω => ∫ z, φ z * schwartzField hD ψ (x + r • z) ω :=
  (schwartzField_average_ae_eq hD ψ φ x r).2.symm

/-- The smooth average of the band at scale `a`, as an L2 class. -/
def bandAverage (hD : StationarySpectralData P D ν)
    (a : ℝ) (φ : TestFn) (x : Plane) (r : ℝ) : Lp ℝ 2 P :=
  smoothSchwartzAverage hD (zetaScaled a 0) φ x r

/-- The low-frequency remainder subtracts the constant band value from its average. -/
def bandLowRemainder (hD : StationarySpectralData P D ν)
    (b : ℝ) (φ : TestFn) (x : Plane) (r : ℝ) : Lp ℝ 2 P :=
  bandAverage hD b φ x r - schwartzExt hD (zetaScaled b x)

/-- The high-frequency remainder is what is left after smoothing the fine band. -/
def bandHighRemainder (hD : StationarySpectralData P D ν)
    (a : ℝ) (φ : TestFn) (x : Plane) (r : ℝ) : Lp ℝ 2 P :=
  testRandomLp hD (φ.dilate r x) - bandAverage hD a φ x r

/-- The field for the difference of band kernels averages to the difference
of the two band-average classes, on a full-measure event at each fixed radius. -/
theorem bandAverage_difference_ae_eq (hD : StationarySpectralData P D ν)
    (a b : ℝ) (φ : TestFn) (x : Plane) (r : ℝ) :
    (fun ω => ∫ z, φ z * schwartzField hD
      (zetaScaled a 0 - zetaScaled b 0) (x + r • z) ω) =ᵐ[P]
      fun ω => bandAverage hD a φ x r ω - bandAverage hD b φ x r ω := by
  have hh := (smoothSchwartzAverage_ae_eq hD (zetaScaled a 0 - zetaScaled b 0) φ x r).symm
  rw [smoothSchwartzAverage_sub] at hh
  exact hh.trans (Lp.coeFn_sub _ _)

/-- The exact band decomposition, with no uncountable intersection of null
sets. The low band is independent of the averaging radius and cancels from
oscillations. The selected difference field has the required stationarity properties. -/
theorem band_decomposition (hD : StationarySpectralData P D ν)
    (a b : ℝ) (φ : TestFn) (x : Plane) (r : ℝ) :
    ∀ᵐ ω ∂P, D ω (φ.dilate r x) =
      (∫ z, φ z * schwartzField hD (zetaScaled a 0 - zetaScaled b 0) (x + r • z) ω) +
        bandField hD b x ω + bandLowRemainder hD b φ x r ω + bandHighRemainder hD a φ x r ω := by
  have hU := Lp.coeFn_sub (bandAverage hD b φ x r) (schwartzExt hD (zetaScaled b x))
  have hW := Lp.coeFn_sub (testRandomLp hD (φ.dilate r x)) (bandAverage hD a φ x r)
  filter_upwards [bandAverage_difference_ae_eq hD a b φ x r,
    bandField_ae_eq hD b x, testRandomLp_coe hD (φ.dilate r x), hU, hW]
    with ω hav hband htest hU hW
  change _ = bandAverage hD b φ x r ω - schwartzExt hD (zetaScaled b x) ω at hU
  change _ = testRandomLp hD (φ.dilate r x) ω - bandAverage hD a φ x r ω at hW
  rw [hav, hband, show bandLowRemainder hD b φ x r ω = _ from hU,
    show bandHighRemainder hD a φ x r ω = _ from hW, htest]
  ring

end Critical2DKPZ.Extensions.ScaleLimit
