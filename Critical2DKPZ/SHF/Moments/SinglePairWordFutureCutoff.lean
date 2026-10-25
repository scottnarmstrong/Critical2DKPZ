/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureSampling
import Mathlib.Tactic

/-! # Compact collision cutoffs for the two-particle future approximation -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported Topology

/-- Multiplication by an interior collision cutoff gives a globally continuous
future test, despite possible endpoint singularities outside its support. -/
theorem continuous_pairTwoContinuumFuture_cutoff
    (θ T : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane)
    (η : C_c(ℝ × Plane, ℝ))
    (hη : ∀ p ∈ tsupport η, p.1 < T) :
    Continuous (fun p : ℝ × Plane => η p * pairTwoContinuumFuture θ (T - p.1) φ a p.2) := by
  apply continuous_of_tsupport
  intro p hp
  have hpη : p ∈ tsupport η := tsupport_mul_subset_left hp
  have hc := continuousAt_pairTwoContinuumFuture θ φ (T - p.1, a, p.2)
    (sub_pos.mpr (hη p hpη))
  have harg : ContinuousAt (fun p' : ℝ × Plane => (T - p'.1, a, p'.2)) p :=
    (continuousAt_const.sub continuousAt_fst).prodMk
      (continuousAt_const.prodMk continuousAt_snd)
  exact η.continuous.continuousAt.mul (ContinuousAt.comp'
    (f := fun p' : ℝ × Plane => (T - p'.1, a, p'.2))
    (g := fun q : ℝ × (Fin 2 → Plane) × Plane => pairTwoContinuumFuture θ q.1 φ q.2.1 q.2.2)
    hc harg)


end Critical2DKPZ.SHF.Moments
