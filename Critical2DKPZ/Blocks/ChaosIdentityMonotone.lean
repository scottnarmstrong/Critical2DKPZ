/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.MomentRecurrence
public import Critical2DKPZ.Blocks.OccupiedExpansion
import Mathlib.Tactic

/-! # The closed-discrepancy chaos identity on monotone grids -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Blocks

/-- Iterating the moment recurrence sums over every occupied subset of the intermediate blocks. -/
theorem resetTailMass_sq_integral_eq_occupiedTailSum (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    {u v : ℕ} (huv : u ≤ v) (b : ℕ) (y : Site) (hb : b ≤ t (u - 1)) :
    (∫ ω, resetTailMass β t b y u v ω ^ 2 ∂disorderLaw) =
      occupiedTailSum (Polymer.sigmaSq β) t u v b y := by
  generalize hk : v - u = k
  induction k generalizing u b y with
  | zero =>
    have huv' : u = v := by omega
    subst u
    rw [resetTailMass_sq_integral_self β t ht b y v hb, occupiedTailSum_self]
  | succ k ih =>
    have huv' : u < v := by omega
    have hnext (c : ℕ) (z : Site) (hc : c ≤ t u) :
        (∫ ω, resetTailMass β t c z (u + 1) v ω ^ 2 ∂disorderLaw) =
          occupiedTailSum (Polymer.sigmaSq β) t (u + 1) v c z := by
      exact ih (u := u + 1) (b := c) (y := z) (huv := by omega)
        (hb := by simpa only [Nat.add_sub_cancel] using hc) (hk := by omega)
    rw [resetTailMass_sq_integral_recursion β t ht b y huv' hb,
      occupiedTailSum_recursion β t huv' b y,
      hnext b y (hb.trans (ht (by omega)))]
    apply congrArg (fun q : ℝ => occupiedTailSum (Polymer.sigmaSq β) t (u + 1) v b y + q)
    exact collisionCellSum_congr (Polymer.sigmaSq β) (t (u - 1)) (t u)
      (fun a x => discrepancyHeatKernel b a y x ^ 2) (fun c hc z => hnext c z hc)

/-- The exact closed-string chaos identity on a globally monotone time grid. -/
theorem closedDiscrepancy_sq_integral_eq_monotone (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    {u v : ℕ} (huv : u < v) :
    (∫ ω, closedDiscrepancy β t u v ω ^ 2 ∂disorderLaw) =
      closedStringSum (Polymer.sigmaSq β) t u v := by
  rw [closedDiscrepancy_sq_integral_firstCell β t ht huv]
  have hcont : collisionCellSum (Polymer.sigmaSq β) (t (u - 1)) (t u)
      (fun a x => srwKernel a x ^ 2)
      (fun c z => ∫ ω, resetTailMass β t c z (u + 1) v ω ^ 2 ∂disorderLaw) =
      collisionCellSum (Polymer.sigmaSq β) (t (u - 1)) (t u) (fun a x => srwKernel a x ^ 2)
        (fun c z => occupiedTailSum (Polymer.sigmaSq β) t (u + 1) v c z) := by
    apply collisionCellSum_congr
    intro c hc z
    exact resetTailMass_sq_integral_eq_occupiedTailSum β t ht (by omega) c z
      (by simpa only [Nat.add_sub_cancel] using hc)
  rw [hcont]
  let S : ℕ → Finset Site := fun a => Polymer.endpoints 0 a
  have hW (a : ℕ) (x : Site) (hx : x ∉ S a) : srwKernel a x ^ 2 = 0 := by
    have hz := Polymer.srwKernel_eq_zero_of_not_mem a 0 x hx
    simp only [sub_zero] at hz
    rw [hz]
    norm_num
  have hI : Finset.Ico (u + 1) v = Finset.Ioo u v := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  change collisionCellSum (Polymer.sigmaSq β) (t (u - 1)) (t u) (fun a x => srwKernel a x ^ 2)
    (fun c z => ∑ T ∈ (Finset.Ico (u + 1) v).powerset,
      stringTail (Polymer.sigmaSq β) t (T.sort (· ≤ ·) ++ [v]) c z) = _
  rw [collisionCellSum_finsetSum β (t (u - 1)) (t u) (fun a x => srwKernel a x ^ 2)
    S hW, closedStringSum_eq_sum_firstCell, hI]

end Critical2DKPZ.Blocks
