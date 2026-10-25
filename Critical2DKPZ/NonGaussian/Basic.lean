/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.ShfPairing
public import Critical2DKPZ.Analysis.Heat.Basic

/-! # Endpoint pairings and centered averaged logarithmic fields -/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.NonGaussian

/-- The endpoint pairing `μ(f) = Z_{r,t}(g_r^{(x)}, f) / Z_{r,t}(g_r^{(x)}, 1)`
on the interval `[r,t]`; compare KPZ (9.3). -/
def endpointPairing {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r t : ℝ) (x : Plane)
    (f : Plane → ℝ) (ω : Ω) : ℝ :=
  shfPairing Z r t (fun y => heatKernel r (y - x)) f ω /
    shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω

/-- The spatial `ψ`-average of `log Z_{r,t}(g_r^{(x)}, f)`, centered at each point
by its Bochner mean; compare KPZ (9.4). -/
def avgLogField {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r t : ℝ) (ψ : Plane → ℝ) (f : Plane → ℝ) (ω : Ω) : ℝ :=
  ∫ x, ψ x * (Real.log (shfPairing Z r t (fun y => heatKernel r (y - x)) f ω) -
    ∫ ω', Real.log (shfPairing Z r t (fun y => heatKernel r (y - x)) f ω') ∂P)

end Critical2DKPZ.NonGaussian

end
