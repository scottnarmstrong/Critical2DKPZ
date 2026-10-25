/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Errata.GQT21Strict
public import Critical2DKPZ.SHF.DeltaBose.CollisionScaling
public import Critical2DKPZ.SHF.DeltaBose.TwoParticle
public import Critical2DKPZ.Analysis.Heat.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic

/-! # Resolvent integrals and Gaussian collision kernels

The examples concern GQT21 Lemmas 4.2, 8.1 and 8.8 with positive heat times and integrable resolvent integrands. -/

@[expose] public noncomputable section
namespace Critical2DKPZ.Errata

open MeasureTheory DeltaBose

/-- The planar resolvent integrand at parameter one is integrable. -/
theorem gqt21_04_integrable_one :
    Integrable (fun q : Plane => ((‖q‖ ^ 2 + 1) ^ 2)⁻¹) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := Plane) (μ := volume)
    (r := 4) (by norm_num [Plane, finrank_euclideanSpace])
  convert h using 1
  funext q
  rw [show -(4 : ℝ) / 2 = -(2 : ℝ) by norm_num, Real.rpow_neg (by positivity),
    Real.rpow_two, add_comm]

/-- The planar resolvent integrand at parameter two is integrable. -/
theorem gqt21_04_integrable_two :
    Integrable (fun q : Plane => ((‖q‖ ^ 2 + 2) ^ 2)⁻¹) := by
  apply gqt21_04_integrable_one.mono' (by fun_prop)
  filter_upwards [] with q
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_anti₀ (by positivity) (by nlinarith [sq_nonneg ‖q‖])

/-- The planar resolvent integrands at parameters one and two are integrable and rule out the proposed linear evaluation. -/
theorem gqt21_04_strict_refutation :
    Integrable (fun q : Plane => ((‖q‖ ^ 2 + 1) ^ 2)⁻¹) ∧
    Integrable (fun q : Plane => ((‖q‖ ^ 2 + 2) ^ 2)⁻¹) ∧
    ¬ ∀ a : ℝ, 0 < a → GQT21.gqt21_04_polarIntegral a = a / (4 * Real.pi) := by
  exact ⟨gqt21_04_integrable_one, gqt21_04_integrable_two,
    GQT21.gqt21_04_printed_polar_integral_false⟩

/-- The joint spatial domain of a configuration and its fused configuration has dimension `4 * n - 2`. -/
theorem gqt21_06_joint_spatial_dimension {n : ℕ} (α : CollisionPair n) :
    Module.finrank ℝ (Configuration n × FusedConfiguration α) = 4 * n - 2 := by
  have hn : 2 ≤ n := by have h := α.2; have hi := α.1.2.isLt; omega
  rw [Module.finrank_prod, finrank_fusedConfiguration]
  have hfull : Module.finrank ℝ (Configuration n) = 2 * n := by
    simp [Configuration, Module.finrank_pi_fintype, Plane, finrank_euclideanSpace,
      Nat.mul_comm]
  rw [hfull]
  omega

/-- The two-particle collision kernel is the square of the heat kernel of the endpoint difference. -/
theorem gqt21_16_corrected_kernel (τ : ℝ) (y y' : FusedConfiguration pairTwo) :
    freeKernel 2 τ (collisionEmbedding pairTwo y) (collisionEmbedding pairTwo y') =
      heatKernel τ (y'.1 - y.1) ^ 2 := by
  simp [freeKernel, collisionEmbedding_pairTwo, pow_two]

/-- At positive time and distinct centers, the collision kernel is smaller than the proposed constant value. -/
theorem gqt21_16_printed_kernel_false {τ : ℝ} (hτ : 0 < τ)
    (y y' : FusedConfiguration pairTwo) (hne : y'.1 ≠ y.1) :
    freeKernel 2 τ (collisionEmbedding pairTwo y) (collisionEmbedding pairTwo y') ≠
      heatKernel τ (y.1 - y.1) ^ 2 := by
  rw [gqt21_16_corrected_kernel, sub_self]
  have hv : 0 < ‖y'.1 - y.1‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have he : Real.exp (-‖y'.1 - y.1‖ ^ 2 / (2 * τ)) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos hv) (by positivity))
  have hp : 0 < (2 * Real.pi * τ)⁻¹ := by positivity
  have hk : heatKernel τ (y'.1 - y.1) < heatKernel τ 0 := by
    rw [heatKernel, heatKernel_at_zero]
    exact mul_lt_of_lt_one_right hp he
  exact ne_of_lt (by nlinarith [heatKernel_pos hτ (y'.1 - y.1), heatKernel_pos hτ 0])

/-- At unit time, the collision kernel differs from the proposed constant between zero and the first coordinate vector. -/
theorem gqt21_16_concrete_counterexample :
    ∃ y y' : FusedConfiguration pairTwo,
      freeKernel 2 1 (collisionEmbedding pairTwo y) (collisionEmbedding pairTwo y') ≠
        heatKernel 1 (y.1 - y.1) ^ 2 := by
  refine ⟨(0, 0), (EuclideanSpace.single 0 1, 0), ?_⟩
  apply gqt21_16_printed_kernel_false (by norm_num)
  intro he
  have hh := congrArg (fun x : Plane => x 0) he
  norm_num at hh

end Critical2DKPZ.Errata
