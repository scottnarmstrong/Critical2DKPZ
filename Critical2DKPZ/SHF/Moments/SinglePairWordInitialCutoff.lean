/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureCutoff
public import Critical2DKPZ.SHF.Moments.EntranceUniform
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Moments.SinglePairWordInitialZero
public import Critical2DKPZ.SHF.Moments.SinglePairWordInitialSupport
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # Integrating the cutoff two-particle entrance over incoming locations -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported Topology

/-- The exact sampled cutoff entrance, viewed as a step function of the two
macroscopic incoming locations. -/
def pairTwoCutoffInitialStep (ϑ : ℝ) (N L lo hi : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : ℝ × Plane → ℝ) (p : Plane × Plane) : ℝ :=
  let x : Fin 2 → Site := ![latticePoint N p.1, latticePoint N p.2]
  collisionEntrance N lo hi (x 0) (x 1)
    (fun q => η q * pairTwoFutureSampleProfile ϑ N L φ x q)

/-- The continuum entrance integral includes a compact collision cutoff and its normalization coefficient. -/
def pairTwoContinuumCutoffEntrance (θ T s t : ℝ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : ℝ × Plane → ℝ) (p : Plane × Plane) : ℝ :=
  4 * ∫ u in s..t, heatKernelPairProfileIntegral u p.1 p.2
    (fun q => η q * pairTwoContinuumFuture θ (T - q.1) φ ![p.1, p.2] q.2)

/-- The incoming sampled cutoff entrance is a measurable lattice step function. -/
theorem measurable_pairTwoCutoffInitialStep (ϑ : ℝ) (N L lo hi : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : C_c(ℝ × Plane, ℝ)) :
    Measurable (pairTwoCutoffInitialStep ϑ N L lo hi φ η) := by
  let G : Site × Site → ℝ := fun p => collisionEntrance N lo hi p.1 p.2
    (fun q => η q * pairTwoFutureSampleProfile ϑ N L φ ![p.1, p.2] q)
  have hmap : Measurable (fun p : Plane × Plane => (latticePoint N p.1, latticePoint N p.2)) :=
    (((measurable_latticePoint N).comp measurable_fst).prodMk
      ((measurable_latticePoint N).comp measurable_snd))
  change Measurable (G ∘ (fun p : Plane × Plane => (latticePoint N p.1, latticePoint N p.2)))
  exact (measurable_of_countable G).comp hmap





end Critical2DKPZ.SHF.Moments
