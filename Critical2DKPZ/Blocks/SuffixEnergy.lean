/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.RandomProfileEnergy
import Mathlib.Tactic

/-! # Annealing the first block of a discrepancy suffix -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Blocks

/-- Annealing the first block of a reset suffix gives its first-last collision energy. -/
theorem resetTailMass_sq_integral_energy (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (b : ℕ) (y : Site) {u v : ℕ} (huv : u < v) (hb : b ≤ t (u - 1)) :
    Integrable (fun ω => resetProfileEnergy β (t (u - 1)) (t u - t (u - 1)) b y
      (fun z => discrepancyTailMass β t (u + 1) v z ω)) disorderLaw ∧
    (∫ ω, resetTailMass β t b y u v ω ^ 2 ∂disorderLaw) =
      ∫ ω, resetProfileEnergy β (t (u - 1)) (t u - t (u - 1)) b y
        (fun z => discrepancyTailMass β t (u + 1) v z ω) ∂disorderLaw := by
  let a := t (u - 1)
  let n := t u - t (u - 1)
  let f : Disorder → Site → ℝ := fun ω z => discrepancyTailMass β t (u + 1) v z ω
  have hadd : a + n = t u := Nat.add_sub_of_le (ht (by omega))
  have hm (z) : Measurable[Gaussian.disorderBlock (a + n) (t v)] (fun ω => f ω z) := by
    rw [hadd]
    simpa only [Nat.add_sub_cancel] using
      measurable_discrepancyTailMass_block β t ht (u + 1) v (by omega) z
  have hf (z) : MemLp (fun ω => f ω z) 4 disorderLaw :=
    memLp_discrepancyTailMass β t (u + 1) v z 4 (by norm_num) (by norm_num)
  have hann := random_resetProfile_sq_integral_energy β a n (t v) b hb y f hm hf
  have heq (ω : Disorder) : resetTailMass β t b y u v ω =
      ∑ w ∈ resetStartSupport b a y, discrepancyHeatKernel b a y w *
        (∑' z, pointToPoint β a n w z ω *
          (f ω z - Collision.terminalWalkMean (a + n) 0 (f ω))) := by
    rw [resetTailMass_eq_finiteSum]
    apply Finset.sum_congr rfl
    intro w _
    apply congrArg (fun q : ℝ => discrepancyHeatKernel b a y w * q)
    simpa only [hadd] using discrepancyTailMass_eq_reset_terminal β t huv w ω
  refine ⟨hann.1, ?_⟩
  calc
    _ = ∫ ω, (∑ w ∈ resetStartSupport b a y, discrepancyHeatKernel b a y w *
        (∑' z, pointToPoint β a n w z ω *
          (f ω z - Collision.terminalWalkMean (a + n) 0 (f ω)))) ^ 2 ∂disorderLaw := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        congrArg (fun q : ℝ => q ^ 2) (heq ω))
    _ = _ := hann.2

/-- Annealing the first discrepancy block leaves only the occupied-block contribution. -/
theorem closedDiscrepancy_sq_integral_energy (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    {u v : ℕ} (huv : u < v) :
    Integrable (fun ω => heatStartProfileEnergy β (t (u - 1)) (t u - t (u - 1))
      (fun z => discrepancyTailMass β t (u + 1) v z ω)) disorderLaw ∧
    (∫ ω, closedDiscrepancy β t u v ω ^ 2 ∂disorderLaw) =
      ∫ ω, heatStartProfileEnergy β (t (u - 1)) (t u - t (u - 1))
        (fun z => discrepancyTailMass β t (u + 1) v z ω) ∂disorderLaw := by
  let a := t (u - 1)
  let n := t u - t (u - 1)
  let f : Disorder → Site → ℝ := fun ω z => discrepancyTailMass β t (u + 1) v z ω
  have hadd : a + n = t u := Nat.add_sub_of_le (ht (by omega))
  have hm (z) : Measurable[Gaussian.disorderBlock (a + n) (t v)] (fun ω => f ω z) := by
    rw [hadd]
    simpa only [Nat.add_sub_cancel] using
      measurable_discrepancyTailMass_block β t ht (u + 1) v (by omega) z
  have hf (z) : MemLp (fun ω => f ω z) 4 disorderLaw :=
    memLp_discrepancyTailMass β t (u + 1) v z 4 (by norm_num) (by norm_num)
  have hann := random_heatStartProfile_sq_integral_energy β a n (t v) f hm hf
  have heq (ω : Disorder) : closedDiscrepancy β t u v ω =
      ∑ w ∈ Polymer.endpoints 0 a, srwKernel a w *
        (∑' z, pointToPoint β a n w z ω *
          (f ω z - Collision.terminalWalkMean (a + n) 0 (f ω))) := by
    have hfinite : closedDiscrepancy β t u v ω =
        ∑ w ∈ Polymer.endpoints 0 a, srwKernel a w * discrepancyTailMass β t u v w ω := by
      rw [closedDiscrepancy_eq_heatStart_tail]
      apply tsum_eq_sum
      intro w hw
      have hz := Polymer.srwKernel_eq_zero_of_not_mem a 0 w hw
      simp only [sub_zero] at hz
      rw [hz, zero_mul]
    rw [hfinite]
    apply Finset.sum_congr rfl
    intro w _
    apply congrArg (fun q : ℝ => srwKernel a w * q)
    simpa only [hadd] using discrepancyTailMass_eq_reset_terminal β t huv w ω
  refine ⟨hann.1, ?_⟩
  calc
    _ = ∫ ω, (∑ w ∈ Polymer.endpoints 0 a, srwKernel a w *
        (∑' z, pointToPoint β a n w z ω *
          (f ω z - Collision.terminalWalkMean (a + n) 0 (f ω)))) ^ 2 ∂disorderLaw := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        congrArg (fun q : ℝ => q ^ 2) (heq ω))
    _ = _ := hann.2

end Critical2DKPZ.Blocks
