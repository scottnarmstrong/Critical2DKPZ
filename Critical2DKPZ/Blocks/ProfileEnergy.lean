/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.ResetProfiles
public import Critical2DKPZ.Blocks.FiniteProfileMoments
import Mathlib.Tactic

/-! # First-last collision energies of centered terminal profiles -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Blocks

/-- The nonempty collision contribution for an incoming reset profile. -/
def resetProfileCollisionEnergy (β : ℝ) (a n b : ℕ) (y : Site) (f : Site → ℝ) : ℝ :=
  Polymer.sigmaSq β * ∑ s ∈ Finset.Icc 1 n, ∑' x,
    discrepancyHeatKernel b (a + s) y x ^ 2 *
      (∑ r : Fin (n - s + 1), ∑' z,
        Collision.spatialRenewal (Polymer.sigmaSq β) r.val (z - x) *
          (Collision.terminalWalkMean (n - s - r.val) z f -
            Collision.terminalWalkMean (a + n) 0 f) ^ 2)

/-- The free propagation term and the nonempty collision contribution. -/
def resetProfileEnergy (β : ℝ) (a n b : ℕ) (y : Site) (f : Site → ℝ) : ℝ :=
  (Collision.terminalWalkMean (a - b + n) y f - Collision.terminalWalkMean (a + n) 0 f) ^ 2 +
    resetProfileCollisionEnergy β a n b y f

/-- The collision contribution when the initial profile is the incoming absolute heat kernel. -/
def heatStartProfileEnergy (β : ℝ) (a n : ℕ) (f : Site → ℝ) : ℝ :=
  Polymer.sigmaSq β * ∑ s ∈ Finset.Icc 1 n, ∑' x,
    srwKernel (a + s) x ^ 2 *
      (∑ r : Fin (n - s + 1), ∑' z,
        Collision.spatialRenewal (Polymer.sigmaSq β) r.val (z - x) *
          (Collision.terminalWalkMean (n - s - r.val) z f -
            Collision.terminalWalkMean (a + n) 0 f) ^ 2)

/-- The exact centered slab moment with a finite incoming reset profile. -/
theorem finite_resetProfile_sq_integral (β : ℝ) (a n b : ℕ) (hb : b ≤ a)
    (y : Site) (f : Site → ℝ) :
    (∫ ω, (∑ w ∈ resetStartSupport b a y, discrepancyHeatKernel b a y w *
      (∑' z, pointToPoint β a n w z ω *
        (f z - Collision.terminalWalkMean (a + n) 0 f))) ^ 2 ∂disorderLaw) =
      resetProfileEnergy β a n b y f := by
  have h := finite_terminalProfile_sq_integral_firstLastCollision β a n
    (resetStartSupport b a y) (fun w => discrepancyHeatKernel b a y w)
    (fun z => f z - Collision.terminalWalkMean (a + n) 0 f)
  rw [sum_resetProfile_centered_terminalWalkMean] at h
  simpa only [heatEvolveFinite_resetProfile hb, terminalWalkMean_sub_const,
    resetProfileEnergy, resetProfileCollisionEnergy] using h

/-- The incoming heat profile cancels the free term of the centered slab moment. -/
theorem finite_heatStartProfile_sq_integral (β : ℝ) (a n : ℕ) (f : Site → ℝ) :
    (∫ ω, (∑ w ∈ Polymer.endpoints 0 a, srwKernel a w *
      (∑' z, pointToPoint β a n w z ω *
        (f z - Collision.terminalWalkMean (a + n) 0 f))) ^ 2 ∂disorderLaw) =
      heatStartProfileEnergy β a n f := by
  have h := finite_terminalProfile_sq_integral_firstLastCollision β a n
    (Polymer.endpoints 0 a) (srwKernel a)
    (fun z => f z - Collision.terminalWalkMean (a + n) 0 f)
  rw [sum_heatStart_centered_terminalWalkMean] at h
  simpa only [heatEvolveFinite_heatStart,
    terminalWalkMean_sub_const, zero_pow (by omega : 2 ≠ 0), zero_add,
    heatStartProfileEnergy] using h

end Critical2DKPZ.Blocks
