/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.CollisionEnergyCells
import Mathlib.Tactic

/-! # Square-moment recurrence for occupied and unoccupied blocks -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Blocks

/-- Reset-tail masses have integrable squares. -/
theorem integrable_sq_resetTailMass (β : ℝ) (t : ℕ → ℕ) (b : ℕ) (y : Site) (u v : ℕ) :
    Integrable (fun ω => resetTailMass β t b y u v ω ^ 2) disorderLaw := by
  have h := (memLp_resetTailMass β t b y u v 2 (by norm_num) (by norm_num)).integrable_norm_pow'
  simpa only [Real.norm_eq_abs, sq_abs] using h

/-- A block is either unoccupied or contributes its first/last collision cell. -/
theorem resetTailMass_sq_integral_recursion (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (b : ℕ) (y : Site) {u v : ℕ} (huv : u < v) (hb : b ≤ t (u - 1)) :
    (∫ ω, resetTailMass β t b y u v ω ^ 2 ∂disorderLaw) =
      (∫ ω, resetTailMass β t b y (u + 1) v ω ^ 2 ∂disorderLaw) +
        collisionCellSum (Polymer.sigmaSq β) (t (u - 1)) (t u)
          (fun a x => discrepancyHeatKernel b a y x ^ 2)
          (fun c z => ∫ ω, resetTailMass β t c z (u + 1) v ω ^ 2 ∂disorderLaw) := by
  let S : ℕ → Finset Site := fun a => Polymer.endpoints y (a - b) ∪ Polymer.endpoints 0 a
  have hW (a : ℕ) (x : Site) (hx : x ∉ S a) : discrepancyHeatKernel b a y x ^ 2 = 0 := by
    rw [discrepancyHeatKernel_eq_zero_of_not_mem_support b a y x hx]
    norm_num
  have hcell := collisionCellSum_integrable_integral β (t (u - 1)) (t u)
    (fun a x => discrepancyHeatKernel b a y x ^ 2) S hW
    (fun c z ω => resetTailMass β t c z (u + 1) v ω ^ 2)
    (fun c z => integrable_sq_resetTailMass β t c z (u + 1) v)
  have henergy := resetTailMass_sq_integral_energy β t ht b y huv hb
  calc
    _ = ∫ ω, resetProfileEnergy β (t (u - 1)) (t u - t (u - 1)) b y
        (fun z => discrepancyTailMass β t (u + 1) v z ω) ∂disorderLaw := henergy.2
    _ = ∫ ω, (resetTailMass β t b y (u + 1) v ω ^ 2 +
        collisionCellSum (Polymer.sigmaSq β) (t (u - 1)) (t u)
          (fun a x => discrepancyHeatKernel b a y x ^ 2)
          (fun c z => resetTailMass β t c z (u + 1) v ω ^ 2)) ∂disorderLaw := by
      exact integral_congr_ae (Filter.Eventually.of_forall
        (resetProfileEnergy_tail_eq β t ht b y u v hb))
    _ = _ := by
      rw [integral_add (integrable_sq_resetTailMass β t b y (u + 1) v) hcell.1, hcell.2]

/-- The first discrepancy block must be occupied. -/
theorem closedDiscrepancy_sq_integral_firstCell (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    {u v : ℕ} (huv : u < v) :
    (∫ ω, closedDiscrepancy β t u v ω ^ 2 ∂disorderLaw) =
      collisionCellSum (Polymer.sigmaSq β) (t (u - 1)) (t u) (fun a x => srwKernel a x ^ 2)
        (fun c z => ∫ ω, resetTailMass β t c z (u + 1) v ω ^ 2 ∂disorderLaw) := by
  let S : ℕ → Finset Site := fun a => Polymer.endpoints 0 a
  have hW (a : ℕ) (x : Site) (hx : x ∉ S a) : srwKernel a x ^ 2 = 0 := by
    have hz := Polymer.srwKernel_eq_zero_of_not_mem a 0 x hx
    simp only [sub_zero] at hz
    rw [hz]
    norm_num
  have hcell := collisionCellSum_integrable_integral β (t (u - 1)) (t u)
    (fun a x => srwKernel a x ^ 2) S hW
    (fun c z ω => resetTailMass β t c z (u + 1) v ω ^ 2)
    (fun c z => integrable_sq_resetTailMass β t c z (u + 1) v)
  calc
    _ = ∫ ω, heatStartProfileEnergy β (t (u - 1)) (t u - t (u - 1))
        (fun z => discrepancyTailMass β t (u + 1) v z ω) ∂disorderLaw :=
      (closedDiscrepancy_sq_integral_energy β t ht huv).2
    _ = ∫ ω, collisionCellSum (Polymer.sigmaSq β) (t (u - 1)) (t u)
        (fun a x => srwKernel a x ^ 2)
        (fun c z => resetTailMass β t c z (u + 1) v ω ^ 2) ∂disorderLaw := by
      exact integral_congr_ae (Filter.Eventually.of_forall (heatStartProfileEnergy_tail_eq β t ht u v))
    _ = _ := hcell.2

/-- The terminal block must also be occupied; a single collision is the zero-gap atom. -/
theorem resetTailMass_sq_integral_self (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (b : ℕ) (y : Site) (v : ℕ) (hb : b ≤ t (v - 1)) :
    (∫ ω, resetTailMass β t b y v v ω ^ 2 ∂disorderLaw) =
      collisionCellSum (Polymer.sigmaSq β) (t (v - 1)) (t v)
        (fun a x => discrepancyHeatKernel b a y x ^ 2) (fun _ _ => 1) := by
  let A := t (v - 1)
  let B := t v
  have hAB : A ≤ B := ht (by omega)
  let S : ℕ → Finset Site := fun a => Polymer.endpoints y (a - b) ∪ Polymer.endpoints 0 a
  have hW (a : ℕ) (x : Site) (hx : x ∉ S a) : discrepancyHeatKernel b a y x ^ 2 = 0 := by
    rw [discrepancyHeatKernel_eq_zero_of_not_mem_support b a y x hx]
    norm_num
  rw [collisionCellSum_eq_relative (Polymer.sigmaSq β) A B
    (fun a x => discrepancyHeatKernel b a y x ^ 2) _ S hW]
  have hmom := finite_terminalProfile_sq_integral_firstLastCollision β A (B - A)
    (resetStartSupport b A y) (fun w => discrepancyHeatKernel b A y w) (fun _ => 1)
  rw [sum_resetProfile_terminalWalkMean] at hmom
  simp only [terminalWalkMean_const, sub_self, zero_pow (by omega : 2 ≠ 0), zero_add,
    heatEvolveFinite_resetProfile (b := b) (τ := A) hb, one_pow, mul_one, Polymer.tsum_pointToPoint] at hmom
  have heq (ω : Disorder) : resetTailMass β t b y v v ω =
      ∑ w ∈ resetStartSupport b A y, discrepancyHeatKernel b A y w *
        pointToPlane β A (B - A) w ω := by
    simp only [resetTailMass_eq_finiteSum, discrepancyTailMass_self, A, B]
  calc
    _ = ∫ ω, (∑ w ∈ resetStartSupport b A y, discrepancyHeatKernel b A y w *
        pointToPlane β A (B - A) w ω) ^ 2 ∂disorderLaw := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        congrArg (fun q : ℝ => q ^ 2) (heq ω))
    _ = _ := by simpa only [relativeCollisionCellSum, mul_one] using hmom

end Critical2DKPZ.Blocks
