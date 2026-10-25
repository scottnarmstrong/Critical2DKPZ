/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.InitialLatticeStep
public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! # Exact configuration cell integration for the tested-word limit -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- At positive scales, a finitely supported even-lattice configuration step function is integrable, and its integral is the lattice sum times one cell volume per label. -/
theorem integrable_integral_configurationLatticeStep {h N : ℕ} (hN : 0 < N)
    (S : Finset (Fin h → Site))
    (hS : ∀ z ∈ S, ∀ i, z i ∈ evenLattice)
    (G : (Fin h → Site) → ℝ) (hzero : ∀ z ∉ S, G z = 0) :
    Integrable (fun x : Configuration h => G (fun i => latticePoint N (x i))) ∧
      (∫ x : Configuration h, G (fun i => latticePoint N (x i))) =
        (4 / (N : ℝ)) ^ h * ∑ z ∈ S, G z := by
  classical
  let A : (Fin h → Site) → Set (Configuration h) :=
    fun z => Set.pi Set.univ (fun i => cell N (z i))
  have hmeas (z : Fin h → Site) : MeasurableSet (A z) :=
    MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_cell N (z i))
  have hmem (x : Configuration h) (z : Fin h → Site) :
      x ∈ A z ↔ (fun i => latticePoint N (x i)) = z := by
    simp only [A, Set.mem_pi, Set.mem_univ, forall_const, mem_cell_iff, funext_iff]
  have hfin (z : Fin h → Site) : volume (A z) < ⊤ := by
    rw [show A z = Set.pi Set.univ (fun i => cell N (z i)) from rfl, volume_pi_pi]
    apply ENNReal.prod_lt_top
    intro i hi
    by_cases hz : z i ∈ evenLattice
    · exact volume_cell_lt_top hN hz
    · simp only [cell_eq_empty_of_not_even hz, measure_empty, ENNReal.zero_lt_top]
  have hint (z : Fin h → Site) : Integrable ((A z).indicator (fun _ => G z)) :=
    (integrableOn_const (C := G z) (hfin z).ne).integrable_indicator (hmeas z)
  have hrepr (x : Configuration h) : G (fun i => latticePoint N (x i)) =
      ∑ z ∈ S, (A z).indicator (fun _ => G z) x := by
    let z₀ : Fin h → Site := fun i => latticePoint N (x i)
    rw [Finset.sum_eq_single z₀]
    · exact (Set.indicator_of_mem ((hmem x z₀).2 rfl) (fun _ : Configuration h => G z₀)).symm
    · intro z hz hne
      exact Set.indicator_of_notMem (fun hx => hne ((hmem x z).1 hx).symm) (fun _ : Configuration h => G z)
    · intro hz
      rw [hzero z₀ hz, Set.indicator_of_mem ((hmem x z₀).2 rfl)]
  have heq : (fun x : Configuration h => G (fun i => latticePoint N (x i))) =
      fun x => ∑ z ∈ S, (A z).indicator (fun _ => G z) x := funext hrepr
  rw [heq]
  refine ⟨integrable_finsetSum S (fun z _ => hint z), ?_⟩
  rw [integral_finsetSum S (fun z _ => hint z)]
  have hvol (z : Fin h → Site) (hz : z ∈ S) :
      (volume (A z)).toReal = (4 / (N : ℝ)) ^ h := by
    rw [show A z = Set.pi Set.univ (fun i => cell N (z i)) from rfl,
      volume_pi_pi, ENNReal.toReal_prod]
    simp only [volume_cell_toReal hN (hS z hz _), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  calc
    _ = ∑ z ∈ S, (4 / (N : ℝ)) ^ h * G z := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [integral_indicator_const _ (hmeas z)]
      simp only [measureReal_def, smul_eq_mul, hvol z hz]
    _ = _ := (Finset.mul_sum _ _ _).symm

end Critical2DKPZ.SHF.Moments
