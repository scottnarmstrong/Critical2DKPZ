/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordInitialCutoff
public import Critical2DKPZ.SHF.Moments.InitialLatticeSum
public import Critical2DKPZ.SHF.Moments.EntranceInitialAverage
import Mathlib.Tactic

/-! # Initial-cell integration for arbitrary collision cutoffs -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory
open scoped CompactlySupported

/-- Every collision cutoff preserves finite incoming support. Its exact
incoming step integral is the configuration sum times the two cell volumes. -/
theorem pairTwoCutoffInitialStep_integrable_integral
    (ϑ : ℝ) {N : ℕ} (hN : 0 < N) (L lo hi : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : ℝ × Plane → ℝ) :
    Integrable (pairTwoCutoffInitialStep ϑ N L lo hi φ η) ∧
      (∫ p : Plane × Plane, pairTwoCutoffInitialStep ϑ N L lo hi φ η p) =
        (4 / (N : ℝ))^2 * ∑ x ∈ Fintype.piFinset (fun i : Fin 2 =>
          ((SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image Prod.fst)),
          collisionEntrance N lo hi (x 0) (x 1)
            (fun q => η q * pairTwoFutureSampleProfile ϑ N L φ x q) := by
  classical
  let S : Fin 2 → Finset Site := fun i =>
    ((SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image Prod.fst)
  let G : Site → Site → ℝ := fun a b => collisionEntrance N lo hi a b
    (fun q => η q * pairTwoFutureSampleProfile ϑ N L φ ![a, b] q)
  have hzero (a b : Site) (hab : a ∉ S 0 ∨ b ∉ S 1) : G a b = 0 := by
    have hx : ∃ i : Fin 2, (![a, b] : Fin 2 → Site) i ∉ S i := by
      rcases hab with ha | hb
      · exact ⟨0, ha⟩
      · exact ⟨1, hb⟩
    obtain ⟨i, hxi⟩ := hx
    have hz (q : ℝ × Plane) : pairTwoFutureSampleProfile ϑ N L φ ![a, b] q = 0 :=
      pairTwoFutureSampleProfile_zero_of_initial_notSupport ϑ N L φ ![a, b] i hxi q
    simp only [G, collisionEntrance, collisionSlice, hz, mul_zero, Finset.sum_const_zero]
  have heven (i : Fin 2) (a : Site) (ha : a ∈ S i) : a ∈ evenLattice :=
    cellPairTest_initialSupport_even N (φ i) ha
  have hrect := integral_initialLatticeStep_rectangle hN (S 0) (S 1) (heven 0) (heven 1) G hzero
  have hstep : pairTwoCutoffInitialStep ϑ N L lo hi φ η =
      fun p : Plane × Plane => G (latticePoint N p.1) (latticePoint N p.2) := by
    funext p
    simp only [pairTwoCutoffInitialStep, G, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨?_, ?_⟩
  · rw [hstep]
    exact hrect.1
  · rw [hstep, hrect.2, sum_initialConfigurations_eq_double]
    simp only [S, G, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

end Critical2DKPZ.SHF.Moments
