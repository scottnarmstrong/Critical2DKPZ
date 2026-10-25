/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Distr
public import Critical2DKPZ.Definitions.TestFnDilate
public import Critical2DKPZ.Spectral.FourierConvention

/-! # Stationary spectral data

The hypotheses of Proposition 5.5 of the extension note, together with its spectral
mass and scale envelope. Finite families, rather than only one-point laws, are
required to be stationary.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

/-- Spectral hypotheses of Proposition 5.5, with measurable finite-family laws. -/
structure StationarySpectralData {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → Distr)
    (ν : Measure Plane) : Prop where
  memLp : ∀ f : TestFn, MemLp (fun ω => D ω f) 2 P
  mean : ∀ f : TestFn, (∫ ω, D ω f ∂P) = 0
  stationary : ∀ (n : ℕ) (f : Fin n → TestFn) (z : Plane),
    IdentDistrib (fun ω i => D ω ((f i).dilate 1 z)) (fun ω i => D ω (f i)) P P
  locFin : IsLocallyFiniteMeasure ν
  fourier_memLp : ∀ f : TestFn, MemLp (Spectral.fourierKPZ f) 2 ν
  isometry : ∀ f g : TestFn, (∫ ω, D ω f * D ω g ∂P) =
    ∫ ξ, (Spectral.fourierKPZ f ξ * star (Spectral.fourierKPZ g ξ)).re ∂ν
  ballAsymp : Tendsto (fun R : ℝ => (ν (Metric.closedBall (0 : Plane) R)).toReal /
    Real.log (Real.log R)) atTop (𝓝 1)

/-- Mass of a closed spectral ball, as a real number. -/
def specMass (ν : Measure Plane) (R : ℝ) : ℝ :=
  (ν (Metric.closedBall 0 R)).toReal


end Critical2DKPZ.Extensions.ScaleLimit

end
