/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Extensions.ScaleLimit.ExponentialDerivativeBounds
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-! # The smooth angular phase on a bounded frequency ball -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The angular exponent as a linear function with values in continuous functions
on the compact frequency ball. -/
def compactPhaseLinear (R : ℝ) (hR : 0 ≤ R) :
    Plane →L[ℝ] C(Metric.closedBall (0 : Plane) R, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun y => ⟨fun ξ => -(Complex.I * (inner ℝ y (ξ : Plane) : ℂ)), by fun_prop⟩
      map_add' := by intro y z; ext ξ; simp [inner_add_left, mul_add]; ring
      map_smul' := by intro c y; ext ξ; simp [inner_smul_left]; ring }
    R (fun y => by
      apply (ContinuousMap.norm_le _ (mul_nonneg hR (norm_nonneg y))).mpr
      intro ξ
      change ‖-(Complex.I * (inner ℝ y (ξ : Plane) : ℂ))‖ ≤ R * ‖y‖
      simp only [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_real_inner_le_norm y ξ).trans
        ((mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp ξ.property) (norm_nonneg y)).trans_eq
          (mul_comm ‖y‖ R)))

@[simp] theorem compactPhaseLinear_apply (R : ℝ) (hR : 0 ≤ R) (y : Plane)
    (ξ : Metric.closedBall (0 : Plane) R) :
    compactPhaseLinear R hR y ξ = -(Complex.I * (inner ℝ y (ξ : Plane) : ℂ)) := rfl

/-- The exponent map has operator norm at most the frequency radius. -/
theorem norm_compactPhaseLinear_le (R : ℝ) (hR : 0 ≤ R) : ‖compactPhaseLinear R hR‖ ≤ R :=
  LinearMap.mkContinuous_norm_le _ hR _

/-- The angular phase as a continuous function on a compact frequency ball. -/
def compactPhase (R : ℝ) (hR : 0 ≤ R) (y : Plane) : C(Metric.closedBall (0 : Plane) R, ℂ) :=
  NormedSpace.exp (compactPhaseLinear R hR y)

@[simp] theorem compactPhase_apply (R : ℝ) (hR : 0 ≤ R) (y : Plane)
    (ξ : Metric.closedBall (0 : Plane) R) :
    compactPhase R hR y ξ = Complex.exp (-(Complex.I * (inner ℝ y (ξ : Plane) : ℂ))) := by
  calc
    compactPhase R hR y ξ = NormedSpace.exp (compactPhaseLinear R hR y ξ) :=
      NormedSpace.map_exp (ContinuousMap.evalAlgHom ℝ ℂ ξ) (continuous_eval_const ξ) _
    _ = Complex.exp (-(Complex.I * (inner ℝ y (ξ : Plane) : ℂ))) := by
      rw [compactPhaseLinear_apply, Complex.exp_eq_exp_ℂ]

/-- The phase has uniform norm at most one. -/
theorem norm_compactPhase_le (R : ℝ) (hR : 0 ≤ R) (y : Plane) : ‖compactPhase R hR y‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro ξ
  rw [compactPhase_apply, Complex.norm_exp]
  simp

/-- Smoothness holds in the uniform norm on the frequency ball. -/
theorem contDiff_compactPhase (R : ℝ) (hR : 0 ≤ R) : ContDiff ℝ ⊤ (compactPhase R hR) :=
  contDiff_exp_linear _

/-- Every derivative costs at most one power of the frequency radius. -/
theorem norm_iteratedFDeriv_compactPhase (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (y : Plane) :
    ‖iteratedFDeriv ℝ k (compactPhase R hR) y‖ ≤ R ^ k := by
  exact (norm_iteratedFDeriv_exp_linear (compactPhaseLinear R hR) R hR
    (norm_compactPhaseLinear_le R hR) k y).trans
      ((mul_le_mul_of_nonneg_left (norm_compactPhase_le R hR y) (pow_nonneg hR k)).trans_eq (mul_one _))

end Critical2DKPZ.Extensions.ScaleLimit
