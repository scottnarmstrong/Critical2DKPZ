/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.InitialLatticeStep
import Mathlib.Tactic

/-! # Exact initial-cell volumes for rectangular lattice supports -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory

/-- At positive scales, integrating a finite even-rectangle step function multiplies its lattice sum by the two cell volumes, and the step function is integrable. -/
theorem integral_initialLatticeStep_rectangle {N : ℕ} (hN : 0 < N)
    (A B : Finset Site) (hA : ∀ a ∈ A, a ∈ evenLattice) (hB : ∀ b ∈ B, b ∈ evenLattice)
    (G : Site → Site → ℝ) (hzero : ∀ a b, a ∉ A ∨ b ∉ B → G a b = 0) :
    Integrable (fun p : Plane × Plane => G (latticePoint N p.1) (latticePoint N p.2)) ∧
      (∫ p : Plane × Plane, G (latticePoint N p.1) (latticePoint N p.2)) =
        (4 / (N : ℝ))^2 * ∑ a ∈ A, ∑ b ∈ B, G a b := by
  classical
  have hsub (q : Site × Site) (hq : G q.1 q.2 ≠ 0) : q ∈ (A ×ˢ B) := by
    rw [Finset.mem_product]
    constructor
    · by_contra ha
      exact hq (hzero q.1 q.2 (Or.inl ha))
    · by_contra hb
      exact hq (hzero q.1 q.2 (Or.inr hb))
  have hfinite : {q : Site × Site | G q.1 q.2 ≠ 0}.Finite :=
    ((A ×ˢ B)).finite_toSet.subset hsub
  refine ⟨integrable_finite_initialLatticeStep hN G hfinite, ?_⟩
  rw [SHF.Flow.integral_finiteLatticeStep_eq_cellSum N hN G hfinite]
  have hpad :
      (∑ q ∈ hfinite.toFinset, G q.1 q.2 * (volume (cell N q.1 ×ˢ cell N q.2)).toReal) =
        ∑ q ∈ (A ×ˢ B), G q.1 q.2 * (volume (cell N q.1 ×ˢ cell N q.2)).toReal := by
    apply Finset.sum_subset (fun q hq => hsub q (hfinite.mem_toFinset.mp hq))
    intro q _hq hnot
    have hz : G q.1 q.2 = 0 := by
      by_contra hne
      exact hnot (hfinite.mem_toFinset.mpr hne)
    rw [hz, zero_mul]
  rw [hpad]
  have hvol (q : Site × Site) (hq : q ∈ (A ×ˢ B)) :
      (volume (cell N q.1 ×ˢ cell N q.2)).toReal = (4 / (N : ℝ))^2 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul,
      volume_cell_toReal hN (hA q.1 (Finset.mem_product.mp hq).1),
      volume_cell_toReal hN (hB q.2 (Finset.mem_product.mp hq).2), pow_two]
  simp_rw [Finset.sum_congr rfl (fun q hq => congrArg (fun v : ℝ => G q.1 q.2 * v) (hvol q hq))]
  rw [← Finset.sum_mul, Finset.sum_product]
  ring

end Critical2DKPZ.SHF.Moments
