/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.ResetTail
import Mathlib.Tactic

/-! # Finite reset profiles and their deterministic propagation -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Blocks

/-- A finite set containing the support of the incoming reset profile after a collision at `(b,y)`. -/
def resetStartSupport (b τ : ℕ) (y : Site) : Finset Site :=
  Polymer.endpoints y (τ - b) ∪ Polymer.endpoints 0 τ

/-- A reset suffix can be expressed using its finite incoming support. -/
theorem resetTailMass_eq_finiteSum (β : ℝ) (t : ℕ → ℕ) (b : ℕ) (y : Site)
    (u v : ℕ) (ω : Disorder) :
    resetTailMass β t b y u v ω =
      ∑ x ∈ resetStartSupport b (t (u - 1)) y,
        discrepancyHeatKernel b (t (u - 1)) y x * discrepancyTailMass β t u v x ω := by
  rw [resetTailMass_eq_kernelSum]
  apply tsum_eq_sum
  intro x hx
  rw [discrepancyHeatKernel_eq_zero_of_not_mem_support b (t (u - 1)) y x hx, zero_mul]

/-- The reset profile propagates by the difference of the two free walk means. -/
theorem sum_resetProfile_terminalWalkMean (b τ n : ℕ) (y : Site) (f : Site → ℝ) :
    (∑ x ∈ resetStartSupport b τ y,
      discrepancyHeatKernel b τ y x * Collision.terminalWalkMean n x f) =
      Collision.terminalWalkMean (τ - b + n) y f -
        Collision.terminalWalkMean (τ + n) 0 f := by
  have hfinite : (∑' x, discrepancyHeatKernel b τ y x * Collision.terminalWalkMean n x f) =
      ∑ x ∈ resetStartSupport b τ y,
        discrepancyHeatKernel b τ y x * Collision.terminalWalkMean n x f := by
    apply tsum_eq_sum
    intro x hx
    rw [discrepancyHeatKernel_eq_zero_of_not_mem_support b τ y x hx, zero_mul]
  rw [← hfinite]
  have hfirst := Collision.summable_terminalWalkMean (τ - b) y
    (fun x => Collision.terminalWalkMean n x f)
  have hsecond := Collision.summable_terminalWalkMean τ 0
    (fun x => Collision.terminalWalkMean n x f)
  simp only [sub_zero] at hsecond
  simp only [discrepancyHeatKernel, sub_mul]
  rw [hfirst.tsum_sub hsecond]
  have hleft := terminalWalkMean_comp (τ - b) n y f
  have hright := terminalWalkMean_comp τ n 0 f
  simpa only [Collision.terminalWalkMean, sub_zero] using congrArg₂ (· - ·) hleft.symm hright.symm

/-- Centering the future terminal profile does not alter the propagated reset mean. -/
theorem sum_resetProfile_centered_terminalWalkMean (b τ n : ℕ) (y : Site)
    (f : Site → ℝ) (c : ℝ) :
    (∑ x ∈ resetStartSupport b τ y,
      discrepancyHeatKernel b τ y x * Collision.terminalWalkMean n x (fun z => f z - c)) =
      Collision.terminalWalkMean (τ - b + n) y f -
        Collision.terminalWalkMean (τ + n) 0 f := by
  rw [sum_resetProfile_terminalWalkMean, terminalWalkMean_sub_const, terminalWalkMean_sub_const]
  ring

/-- Free heat evolution of an incoming reset profile has the reset kernel at the later time. -/
theorem heatEvolveFinite_resetProfile {b τ : ℕ} (hbτ : b ≤ τ) (s : ℕ) (y x : Site) :
    Collision.heatEvolveFinite s (resetStartSupport b τ y)
      (fun w => discrepancyHeatKernel b τ y w) x =
        discrepancyHeatKernel b (τ + s) y x := by
  have h := sum_resetProfile_terminalWalkMean b τ s y (fun z => if z = x then 1 else 0)
  simp only [Collision.terminalWalkMean, mul_ite, mul_one, mul_zero, tsum_ite_eq, sub_zero] at h
  have htime : τ - b + s = τ + s - b := by omega
  simpa only [Collision.heatEvolveFinite, discrepancyHeatKernel, htime] using h

/-- Incoming absolute heat data propagate by the free walk semigroup. -/
theorem sum_heatStart_terminalWalkMean (τ n : ℕ) (f : Site → ℝ) :
    (∑ w ∈ Polymer.endpoints 0 τ, srwKernel τ w * Collision.terminalWalkMean n w f) =
      Collision.terminalWalkMean (τ + n) 0 f := by
  rw [terminalWalkMean_comp τ n 0 f]
  simp only [Collision.terminalWalkMean, sub_zero]
  symm
  apply tsum_eq_sum
  intro w hw
  have hz := Polymer.srwKernel_eq_zero_of_not_mem τ 0 w hw
  simp only [sub_zero] at hz
  rw [hz, zero_mul]

/-- Centering against the total-time heat profile cancels the deterministic incoming heat term. -/
theorem sum_heatStart_centered_terminalWalkMean (τ n : ℕ) (f : Site → ℝ) :
    (∑ w ∈ Polymer.endpoints 0 τ, srwKernel τ w * Collision.terminalWalkMean n w
      (fun z => f z - Collision.terminalWalkMean (τ + n) 0 f)) = 0 := by
  rw [sum_heatStart_terminalWalkMean, terminalWalkMean_sub_const, sub_self]

/-- The heat-evolved finite incoming heat profile is the absolute heat kernel. -/
theorem heatEvolveFinite_heatStart (τ s : ℕ) (x : Site) :
    Collision.heatEvolveFinite s (Polymer.endpoints 0 τ) (srwKernel τ) x =
      srwKernel (τ + s) x := by
  have h := sum_heatStart_terminalWalkMean τ s (fun z => if z = x then 1 else 0)
  simpa only [Collision.terminalWalkMean, mul_ite, mul_one, mul_zero,
    tsum_ite_eq, sub_zero, Collision.heatEvolveFinite] using h

end Critical2DKPZ.Blocks
