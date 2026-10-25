/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.LinearDerivativeBounds
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

/-! # Sharp iterated derivative bounds for linear exponential families -/

public section
noncomputable section
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A continuous linear exponential family in a commutative Banach algebra is smooth. -/
theorem contDiff_exp_linear {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedCommRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
    (A : V →L[ℝ] B) : ContDiff ℝ ⊤ (fun y => NormedSpace.exp (A y)) := by
  have he : ContDiff ℝ ⊤ (NormedSpace.exp : B → B) :=
    AnalyticOnNhd.contDiff (fun y _ => NormedSpace.exp_analytic (𝕂 := ℝ) y)
  exact he.comp A.contDiff

/-- The sharp bound keeps the value of the exponential, rather than replacing it
by the exponential of the norm of its argument. -/
theorem norm_iteratedFDeriv_exp_linear {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedCommRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
    (A : V →L[ℝ] B) (R : ℝ) (hR : 0 ≤ R) (hA : ‖A‖ ≤ R) (k : ℕ) (y : V) :
    ‖iteratedFDeriv ℝ k (fun y => NormedSpace.exp (A y)) y‖ ≤
      R ^ k * ‖NormedSpace.exp (A y)‖ := by
  let L : B →L[ℝ] (V →L[ℝ] B) :=
    ((ContinuousLinearMap.compL ℝ V B B).flip A).comp (ContinuousLinearMap.mul ℝ B)
  have hdf : fderiv ℝ (fun y => NormedSpace.exp (A y)) = L ∘ (fun y => NormedSpace.exp (A y)) := by
    funext y
    have hd := (hasFDerivAt_exp (𝕂 := ℝ) (x := A y)).comp y A.hasFDerivAt
    change fderiv ℝ (NormedSpace.exp ∘ A) y = _
    rw [hd.fderiv]
    ext v
    simp [L, ContinuousLinearMap.compL_apply]
  have hL : ‖L‖ ≤ R := by
    apply L.opNorm_le_bound hR
    intro b
    calc
      ‖L b‖ ≤ ‖ContinuousLinearMap.mul ℝ B b‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖b‖ * R := mul_le_mul (ContinuousLinearMap.opNorm_mul_apply_le ℝ B b) hA
        (norm_nonneg A) (norm_nonneg b)
      _ = R * ‖b‖ := mul_comm _ _
  exact norm_iteratedFDeriv_le_of_linear_fderiv _ L R hR (contDiff_exp_linear A) hdf hL k y

end Critical2DKPZ.Extensions.ScaleLimit
