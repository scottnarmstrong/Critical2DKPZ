/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.SuffixEnergy
public import Critical2DKPZ.Blocks.CollisionIntegration
import Mathlib.Tactic

/-! # Collision energies in the absolute cells of the string sum -/

@[expose] public noncomputable section

namespace Critical2DKPZ.Blocks

/-- Rewrite the reset-profile collision energy in absolute first/last time coordinates. -/
theorem resetProfileCollisionEnergy_eq_cell (β : ℝ) (A B b : ℕ) (hAB : A ≤ B)
    (y : Site) (f : Site → ℝ) :
    resetProfileCollisionEnergy β A (B - A) b y f =
      collisionCellSum (Polymer.sigmaSq β) A B
        (fun a x => discrepancyHeatKernel b a y x ^ 2)
        (fun c z => (Collision.terminalWalkMean (B - c) z f -
          Collision.terminalWalkMean B 0 f) ^ 2) := by
  let S : ℕ → Finset Site := fun a => Polymer.endpoints y (a - b) ∪ Polymer.endpoints 0 a
  have hW (a : ℕ) (x : Site) (hx : x ∉ S a) : discrepancyHeatKernel b a y x ^ 2 = 0 := by
    rw [discrepancyHeatKernel_eq_zero_of_not_mem_support b a y x hx]
    norm_num
  rw [collisionCellSum_eq_relative (Polymer.sigmaSq β) A B
    (fun a x => discrepancyHeatKernel b a y x ^ 2) _ S hW]
  have htotal : A + (B - A) = B := Nat.add_sub_of_le hAB
  have hsub (s r : ℕ) : B - (A + s + r) = B - A - s - r := by omega
  simp only [resetProfileCollisionEnergy, relativeCollisionCellSum, htotal, hsub]

/-- Rewrite the heat-start collision energy in absolute first/last time coordinates. -/
theorem heatStartProfileEnergy_eq_cell (β : ℝ) (A B : ℕ) (hAB : A ≤ B) (f : Site → ℝ) :
    heatStartProfileEnergy β A (B - A) f =
      collisionCellSum (Polymer.sigmaSq β) A B (fun a x => srwKernel a x ^ 2)
        (fun c z => (Collision.terminalWalkMean (B - c) z f -
          Collision.terminalWalkMean B 0 f) ^ 2) := by
  let S : ℕ → Finset Site := fun a => Polymer.endpoints 0 a
  have hW (a : ℕ) (x : Site) (hx : x ∉ S a) : srwKernel a x ^ 2 = 0 := by
    have hz := Polymer.srwKernel_eq_zero_of_not_mem a 0 x hx
    simp only [sub_zero] at hz
    rw [hz]
    norm_num
  rw [collisionCellSum_eq_relative (Polymer.sigmaSq β) A B
    (fun a x => srwKernel a x ^ 2) _ S hW]
  have htotal : A + (B - A) = B := Nat.add_sub_of_le hAB
  have hsub (s r : ℕ) : B - (A + s + r) = B - A - s - r := by omega
  simp only [heatStartProfileEnergy, relativeCollisionCellSum, htotal, hsub]

/-- The reset-profile energy equals the squared reset-tail mass plus a collision-cell contribution. -/
theorem resetProfileEnergy_tail_eq (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (b : ℕ) (y : Site) (u v : ℕ) (hb : b ≤ t (u - 1)) (ω : Disorder) :
    resetProfileEnergy β (t (u - 1)) (t u - t (u - 1)) b y
      (fun z => discrepancyTailMass β t (u + 1) v z ω) =
      resetTailMass β t b y (u + 1) v ω ^ 2 +
        collisionCellSum (Polymer.sigmaSq β) (t (u - 1)) (t u)
          (fun a x => discrepancyHeatKernel b a y x ^ 2)
          (fun c z => resetTailMass β t c z (u + 1) v ω ^ 2) := by
  let f : Site → ℝ := fun z => discrepancyTailMass β t (u + 1) v z ω
  have hAB : t (u - 1) ≤ t u := ht (by omega)
  have htotal : t (u - 1) + (t u - t (u - 1)) = t u := Nat.add_sub_of_le hAB
  have htime : t (u - 1) - b + (t u - t (u - 1)) = t u - b := by omega
  have hfree : Collision.terminalWalkMean (t (u - 1) - b + (t u - t (u - 1))) y f -
      Collision.terminalWalkMean (t (u - 1) + (t u - t (u - 1))) 0 f =
      resetTailMass β t b y (u + 1) v ω := by
    simp only [htotal, htime, resetTailMass, Nat.add_sub_cancel, f]
  have hrest (c : ℕ) (z : Site) :
      (Collision.terminalWalkMean (t u - c) z f - Collision.terminalWalkMean (t u) 0 f) =
      resetTailMass β t c z (u + 1) v ω := by
    simp only [resetTailMass, Nat.add_sub_cancel, f]
  unfold resetProfileEnergy
  rw [hfree, resetProfileCollisionEnergy_eq_cell β (t (u - 1)) (t u) b hAB]
  apply congrArg (fun F : ℕ → Site → ℝ => resetTailMass β t b y (u + 1) v ω ^ 2 +
    collisionCellSum (Polymer.sigmaSq β) (t (u - 1)) (t u)
      (fun a x => discrepancyHeatKernel b a y x ^ 2) F)
  funext c z
  exact congrArg (fun q : ℝ => q ^ 2) (hrest c z)

/-- The heat-start discrepancy energy is a collision-cell sum weighted by the squared remaining reset-tail mass. -/
theorem heatStartProfileEnergy_tail_eq (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (u v : ℕ) (ω : Disorder) :
    heatStartProfileEnergy β (t (u - 1)) (t u - t (u - 1))
      (fun z => discrepancyTailMass β t (u + 1) v z ω) =
      collisionCellSum (Polymer.sigmaSq β) (t (u - 1)) (t u) (fun a x => srwKernel a x ^ 2)
        (fun c z => resetTailMass β t c z (u + 1) v ω ^ 2) := by
  rw [heatStartProfileEnergy_eq_cell β (t (u - 1)) (t u) (ht (by omega))]
  simp only [resetTailMass, Nat.add_sub_cancel]

end Critical2DKPZ.Blocks
