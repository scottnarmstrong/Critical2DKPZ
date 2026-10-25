/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-! # Iterated derivative bounds for a linear differential identity -/

public section
noncomputable section
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A constant linear differential identity controls every iterated derivative sharply. -/
theorem norm_iteratedFDeriv_le_of_linear_fderiv {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (f : V → B) (L : B →L[ℝ] (V →L[ℝ] B)) (R : ℝ) (hR : 0 ≤ R)
    (hf : ContDiff ℝ ⊤ f) (hdf : fderiv ℝ f = L ∘ f) (hL : ‖L‖ ≤ R)
    (k : ℕ) (y : V) : ‖iteratedFDeriv ℝ k f y‖ ≤ R ^ k * ‖f y‖ := by
  induction k with
  | zero => simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, le_refl]
  | succ k ih =>
    rw [← norm_iteratedFDeriv_fderiv, hdf,
      L.iteratedFDeriv_comp_left hf.contDiffAt (by simp : (k : WithTop ℕ∞) ≤ ⊤)]
    calc
      ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ k f y)‖ ≤
          ‖L‖ * ‖iteratedFDeriv ℝ k f y‖ := L.norm_compContinuousMultilinearMap_le _
      _ ≤ R * (R ^ k * ‖f y‖) := mul_le_mul hL ih (norm_nonneg _) hR
      _ = R ^ (k + 1) * ‖f y‖ := by rw [pow_succ]; ring

end Critical2DKPZ.Extensions.ScaleLimit
