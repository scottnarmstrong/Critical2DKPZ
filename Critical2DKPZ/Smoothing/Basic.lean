/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.KpzLatticeReversed
public import Critical2DKPZ.Definitions.KpzLatticeReversedReg
public import Critical2DKPZ.Definitions.SmoothedP2Plane
public import Critical2DKPZ.Definitions.EndpointDist
public import Critical2DKPZ.Definitions.SmoothedEndpointDist
public import Critical2DKPZ.Analysis.Heat.Basic

/-! # Local and global logarithmic smoothing errors -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.Smoothing

/-- The spatially tested, mean-centered local logarithmic error from equation (2.28). -/
def localLogError (β : ℝ) (N m n : ℕ) (φ : Plane → ℝ) (ω : Disorder) : ℝ :=
  ∫ x, φ x * ((Real.log (pointToPlane β 0 n (latticePoint N x) ω) -
      Real.log (smoothedP2Plane β m n (latticePoint N x) ω)) -
    ∫ ω', (Real.log (pointToPlane β 0 n (latticePoint N x) ω') -
      Real.log (smoothedP2Plane β m n (latticePoint N x) ω')) ∂disorderLaw)

/-- The difference of future profile logarithms for point-started and smoothed endpoint laws, as in equation (4.38). -/
def globalLogError (β : ℝ) (m n N : ℕ) (f : Site → ℝ) (z : Site) (ω : Disorder) : ℝ :=
  Real.log (profileP2Fun β n N (endpointDist β n z ω) f ω) -
    Real.log (profileP2Fun β n N (smoothedEndpointDist β m n z ω) f ω)

/-- The tested difference of the point-started and smoothed lattice fields on `[0, M]` (cells at scale
`N`, disorder removed until `k`, smoothing kernel `q_j`, terminal weight the cell average of `e^{h₀}`). -/
def latticeSmoothingError (β : ℝ) (N M k j : ℕ) (h₀ : Plane →ᵇ ℝ) (φ : Plane → ℝ) (ω : Disorder) : ℝ :=
  ∫ x, φ x *
    ((Real.log (profileP2Fun β 0 M (fun w => if w = latticePoint N x then 1 else 0)
          (cellAverage N fun y => Real.exp (h₀ y)) ω) -
      ∫ ω', Real.log (profileP2Fun β 0 M (fun w => if w = latticePoint N x then 1 else 0)
          (fun _ => 1) ω') ∂disorderLaw) -
     (Real.log (profileP2Fun β k M (fun w => srwKernel j (w - latticePoint N x))
          (cellAverage N fun y => Real.exp (h₀ y)) ω) -
      ∫ ω', Real.log (profileP2Fun β k M (fun w => srwKernel j (w - latticePoint N x))
          (fun _ => 1) ω') ∂disorderLaw))

/-- The heat energy from equation (4.22), defined by integrating the absolute test pair against the time-integrated heat kernel. -/
def heatEnergy (s : ℝ) (φ : Plane → ℝ) : ℝ :=
  ∫ p : Plane × Plane, |φ p.1| * |φ p.2| * (4 * ∫ r in (0 : ℝ)..s, heatKernel (2 * r) (p.1 - p.2))

end Critical2DKPZ.Smoothing

end
