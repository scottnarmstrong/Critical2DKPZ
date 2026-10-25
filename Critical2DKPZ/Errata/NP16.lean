/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Ehrhard.FunctionalHessian
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Coercive quadratic forms and interpolation ranges

Source: arXiv:1605.07233v1, proof of Lemma 3.2 and definition
of `J_R`. These witnesses concern the printed proof, not the PSD conclusion.
-/

@[expose] public noncomputable section

open scoped Matrix

namespace Critical2DKPZ.Errata

/-- A one-dimensional coercive matrix example at `ε = 1/4` has quadratic form `1/4`, below the proposed lower bound `3/4`. -/
theorem np16_printed_psd_lower_bound_counterexample :
    let A : Matrix (Fin 1) (Fin 1) ℝ := 0
    let B : Matrix (Fin 1) (Fin 1) ℝ := 1
    let u : Fin 1 → ℝ := fun _ => 1
    A *ᵥ u = 0 ∧ u ⬝ᵥ (B *ᵥ u) = 1 ∧
      u ⬝ᵥ ((A + (1 / 4 : ℝ) • B) *ᵥ u) < 1 - (1 / 4 : ℝ) := by
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_one]

/-- The interpolation functional is strictly positive and therefore is not valued in the singleton zero. -/
theorem np16_gaussianFunctional_mem_Ioo {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (R : ℝ) (x : ι → ℝ) :
    Ehrhard.gaussianFunctional θ R x ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨Ehrhard.gaussianCDF_pos _, Ehrhard.gaussianCDF_lt_one _⟩

end Critical2DKPZ.Errata

end
