/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonQuadratic
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonScalarFlowClt
import Mathlib.Tactic

/-! # Finite linear projections of the flow and its Gaussian limit -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped Topology BigOperators NNReal

namespace Critical2DKPZ.Extensions.GffTangent

/-- Finite combinations preserve the mean-zero condition on compact tests. -/
theorem integral_testFn_linearCombination_eq_zero {n : ℕ} (f : Fin n → TestFn)
    (hf : ∀ i, (∫ x : Plane, f i x) = 0) (t : Fin n → ℝ) :
    (∫ x : Plane, (∑ i, t i • f i : TestFn) x) = 0 := by
  classical
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  rw [integral_finsetSum _ (fun i _ =>
    ((f i).continuous.integrable_of_hasCompactSupport (f i).hasCompactSupport).const_mul (t i))]
  simp only [integral_const_mul, hf, mul_zero, Finset.sum_const_zero]

/-- Flat-terminal flow pairings respect finite combinations almost surely;
all sample integrability obligations follow from the SHF annealed mass. -/
theorem shfPairing_linearCombination_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ϑ : ℝ)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {T : ℝ} (hT : 0 < T) {n : ℕ} (f : Fin n → TestFn) (t : Fin n → ℝ) :
    ∀ᵐ ω ∂P, shfPairing Z 0 T (∑ i, t i • f i : TestFn) (fun _ => 1) ω =
      ∑ i, t i * shfPairing Z 0 T (f i) (fun _ => 1) ω := by
  classical
  have hi (i : Fin n) := (integrable_shfPairing_one ϑ P Z hZ (le_refl 0) hT
    (f i).continuous.measurable
    ((f i).continuous.integrable_of_hasCompactSupport (f i).hasCompactSupport)).1
  filter_upwards [ae_all_iff.mpr hi] with ω hω
  simp only [shfPairing, mul_one, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  rw [integral_finsetSum _ (fun i _ => (hω i).const_mul (t i))]
  simp only [integral_const_mul]

/-- A projection of a centered multivariate Gaussian has precisely the
quadratic-form variance. -/
theorem map_inner_multivariateGaussian {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) (t : EuclideanSpace ℝ (Fin n)) :
    (multivariateGaussian 0 S).map (fun x => inner ℝ x t) =
      gaussianReal 0 (Real.toNNReal (t ⬝ᵥ S *ᵥ t)) := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ t
  have hmean : (∫ x, L x ∂multivariateGaussian 0 S) = 0 := by
    rw [L.integral_comp_id_comm IsGaussian.integrable_id, integral_id_multivariateGaussian]
    exact L.map_zero
  have hvariance : variance L (multivariateGaussian 0 S) = t ⬝ᵥ S *ᵥ t := by
    change variance (fun x => inner ℝ t x) (multivariateGaussian 0 S) = _
    rw [← covarianceBilin_self IsGaussian.memLp_two_id t, covarianceBilin_multivariateGaussian hS]
  have hm := IsGaussian.map_eq_gaussianReal (μ := multivariateGaussian 0 S) L
  rw [hmean, hvariance] at hm
  convert hm using 2
  funext x
  exact (real_inner_comm x t).symm

end Critical2DKPZ.Extensions.GffTangent
