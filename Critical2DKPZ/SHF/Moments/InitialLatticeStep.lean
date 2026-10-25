/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabProductsCore
import Mathlib.Tactic

/-! # Integrability of finite initial lattice step functions -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory

/-- At positive scales, a lattice step function with finite even-lattice support is integrable. -/
theorem integrable_finite_initialLatticeStep {N : ℕ} (hN : 0 < N)
    (G : Site → Site → ℝ) (hG : {q : Site × Site | G q.1 q.2 ≠ 0}.Finite) :
    Integrable (fun p : Plane × Plane => G (latticePoint N p.1) (latticePoint N p.2)) := by
  classical
  let S := hG.toFinset
  let A : Site × Site → Set (Plane × Plane) := fun q => cell N q.1 ×ˢ cell N q.2
  have hAfin (q : Site × Site) : volume (A q) < ⊤ := by
    have hcell (z : Site) : volume (cell N z) < ⊤ := by
      by_cases hz : z ∈ evenLattice
      · exact volume_cell_lt_top hN hz
      · simp only [cell_eq_empty_of_not_even hz, measure_empty, ENNReal.zero_lt_top]
    rw [show A q = cell N q.1 ×ˢ cell N q.2 from rfl,
      Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top (hcell q.1) (hcell q.2)
  have hrepr (p : Plane × Plane) :
      G (latticePoint N p.1) (latticePoint N p.2) =
        ∑ q ∈ S, (A q).indicator (fun _ => G q.1 q.2) p := by
    let q₀ : Site × Site := (latticePoint N p.1, latticePoint N p.2)
    change G q₀.1 q₀.2 = _
    rw [Finset.sum_eq_single q₀]
    · exact (Set.indicator_of_mem
        (show p ∈ A q₀ from ⟨mem_cell_latticePoint N p.1, mem_cell_latticePoint N p.2⟩)
        (fun _ : Plane × Plane => G q₀.1 q₀.2)).symm
    · intro q _hq hq
      apply Set.indicator_of_notMem
      intro hp
      have heq : q₀ = q := Prod.ext ((mem_cell_iff N q.1 p.1).mp hp.1)
        ((mem_cell_iff N q.2 p.2).mp hp.2)
      exact hq heq.symm
    · intro hq
      have hz : G q₀.1 q₀.2 = 0 := by
        by_contra hne
        exact hq (hG.mem_toFinset.mpr hne)
      simp only [hz, Set.indicator_apply, ite_self]
  rw [show (fun p : Plane × Plane => G (latticePoint N p.1) (latticePoint N p.2)) =
      fun p => ∑ q ∈ S, (A q).indicator (fun _ => G q.1 q.2) p from funext hrepr]
  apply integrable_finsetSum
  intro q _hq
  exact (integrableOn_const (C := G q.1 q.2) (hAfin q).ne).integrable_indicator
    ((measurableSet_cell N q.1).prod (measurableSet_cell N q.2))

end Critical2DKPZ.SHF.Moments
