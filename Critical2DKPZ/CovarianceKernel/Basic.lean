/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.KpzRegularized
public import Critical2DKPZ.Spectral.RadialBessel

/-! # Covariance kernels and Bessel inversion -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.CovarianceKernel

/-- `Cδ(z) = Cov(ℋ⁽ᵟ⁾(0), ℋ⁽ᵟ⁾(z))`, the covariance kernel of the regularized flat field. -/
def regCovKernel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ) (z : Plane) : ℝ :=
  cov[kpzRegularized P Z t δ 0 0, kpzRegularized P Z t δ 0 z; P]

/-- The compensated Bessel inversion from equation (8.17) is the mass of the closed unit ball plus the integral of `J₀(|ξ||z|) − 1_{|ξ| ≤ 1}`. The Bochner integral is assigned zero when its integrand is not integrable. -/
def besselInversion (ν : Measure Plane) (z : Plane) : ℝ :=
  (ν (Metric.closedBall 0 1)).toReal +
    ∫ ξ, (Critical2DKPZ.Spectral.besselJ0Angular (‖ξ‖ * ‖z‖) -
      (Metric.closedBall (0 : Plane) 1).indicator 1 ξ) ∂ν

/-- The Bessel inversion depends on its spatial argument only through its norm. -/
theorem besselInversion_eq_of_norm (ν : Measure Plane) {z w : Plane}
    (h : ‖z‖ = ‖w‖) : besselInversion ν z = besselInversion ν w := by
  simp [besselInversion, h]

end Critical2DKPZ.CovarianceKernel

end
