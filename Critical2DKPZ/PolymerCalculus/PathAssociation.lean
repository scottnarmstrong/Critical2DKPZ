/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.Association
import Mathlib.Tactic

/-! Logarithms of positive finite-profile polymer masses at nonnegative inverse temperatures have nonnegative covariance in the same Gaussian environment. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Function Set
open scoped BigOperators NNReal

namespace Critical2DKPZ.PolymerCalculus

/-- All space-time coordinates that can occur in a finite-start path family. -/
def finitePathCoordinates {ι : Type*} [Fintype ι] (a n : ℕ) (w : ι → Site) :
    Finset (ℕ × Site) :=
  Finset.univ.biUnion (fun p : ι × (Fin n → Fin 4) =>
    (Finset.Icc 1 n).image (fun j => (a + j, walkPosition (w p.1) p.2 j)))

/-- The finite path mass depends only on the specified finite disorder coordinates. -/
theorem dependsOn_finitePathMass {ι : Type*} [Fintype ι] (β : ℝ) (a n : ℕ)
    (w : ι → Site) (c : ι × (Fin n → Fin 4) → ℝ) :
    DependsOn (finitePathMass β a n w c) (finitePathCoordinates a n w : Set (ℕ × Site)) := by
  intro x y hxy
  unfold finitePathMass
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  congr 1
  unfold pathEnergy
  apply Finset.sum_congr rfl
  intro j hj
  rw [hxy (a + j, walkPosition (w p.1) p.2 j) (by
    apply Finset.mem_biUnion.mpr
    exact ⟨p, Finset.mem_univ _, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩)]

/-- The logarithm of the finite path mass depends only on the specified disorder coordinates. -/
theorem dependsOn_log_finitePathMass {ι : Type*} [Fintype ι] (β : ℝ) (a n : ℕ)
    (w : ι → Site) (c : ι × (Fin n → Fin 4) → ℝ) :
    DependsOn (fun ω => Real.log (finitePathMass β a n w c ω))
      (finitePathCoordinates a n w : Set (ℕ × Site)) := by
  intro x y hxy
  exact congrArg Real.log (dependsOn_finitePathMass β a n w c hxy)

/-- Every finite absolute moment of a positive finite-profile log mass exists. -/
theorem memLp_log_finitePathMass {ι : Type*} [Fintype ι]
    (β : ℝ) (a n : ℕ) (w : ι → Site) {c : ι × (Fin n → Fin 4) → ℝ}
    (hc : ∀ j, 0 ≤ c j) (hpos : ∃ j, 0 < c j) (q : ℝ≥0) :
    MemLp (fun ω => Real.log (finitePathMass β a n w c ω)) q disorderLaw := by
  apply memLp_of_mem_interior_integrableExpSet
  rw [integrableExpSet_log_finitePathMass β a n w hc hpos, interior_univ]
  trivial

/-- For nonnegative inverse temperatures, log masses with nonnegative deterministic coefficients and at least one positive coefficient have nonnegative covariance in the same disorder. -/
theorem covariance_log_finitePathMass_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ] {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (a n b m : ℕ) (w : ι → Site) (v : κ → Site)
    {c : ι × (Fin n → Fin 4) → ℝ} {d : κ × (Fin m → Fin 4) → ℝ}
    (hc : ∀ j, 0 ≤ c j) (hposc : ∃ j, 0 < c j)
    (hd : ∀ j, 0 ≤ d j) (hposd : ∃ j, 0 < d j) :
    0 ≤ cov[fun ω => Real.log (finitePathMass β a n w c ω),
      fun ω => Real.log (finitePathMass γ b m v d ω); disorderLaw] :=
  covariance_nonneg_disorder_dependsOn (finitePathCoordinates a n w) (finitePathCoordinates b m v)
    (monotone_log_finitePathMass hβ a n w hc hposc)
    (monotone_log_finitePathMass hγ b m v hd hposd)
    (measurable_log_finitePathMass β a n w c) (measurable_log_finitePathMass γ b m v d)
    (dependsOn_log_finitePathMass β a n w c) (dependsOn_log_finitePathMass γ b m v d)
    (memLp_log_finitePathMass β a n w hc hposc 2)
    (memLp_log_finitePathMass γ b m v hd hposd 2)

end Critical2DKPZ.PolymerCalculus
