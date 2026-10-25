/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.FirstMoment

/-! # Annealed polymer density on a time slab -/

@[expose] public section

open MeasureTheory

noncomputable section

namespace Critical2DKPZ.SHF.Limit

/-- The mean density of the polymer measure on the slab `(t, t']`: the rescaled walk kernel. -/
def slabMeanKernel (ϑ : ℝ) (N : ℕ) (t t' : ℝ) (w y : Plane) : ℝ :=
  ∫ ω, rescaledP2P ϑ N t t' (w, y) ω ∂disorderLaw

/-- The slab mean is the rescaled simple-random-walk transition kernel. -/
theorem slabMeanKernel_eq_srwKernel (ϑ : ℝ) (N : ℕ) (t t' : ℝ) (w y : Plane) :
    slabMeanKernel ϑ N t t' w y =
      (N : ℝ) / 4 * srwKernel (evenCeil ((N : ℝ) * t') - evenCeil ((N : ℝ) * t))
        (latticePoint N y - latticePoint N w) := by
  exact SHF.Moments.integral_rescaledP2P ϑ N t t' (w, y)

end Critical2DKPZ.SHF.Limit

end
