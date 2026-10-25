/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Definitions.IsFiniteGffLaw
public import Critical2DKPZ.Extensions.GffTangent.LogKernelIdentities

/-!
# Finite-dimensional Gaussian free field laws

The positive semidefinite logarithmic covariance defines a multivariate Gaussian.
All six defining clauses are verified; the characteristic-function clause determines
the law, including empty and singular families.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

namespace Critical2DKPZ.Extensions.GffTangent

/-- The characteristic-function clause alone determines the probability measure.
No zero-integral assumption on the tests is needed for uniqueness. -/
theorem isFiniteGffLaw_unique {n : ℕ} {f : Fin n → TestFn}
    {μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    (hμ : IsFiniteGffLaw f μ) (hν : IsFiniteGffLaw f ν) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext z
  exact (hμ.2.2.2.2.2 z).trans (hν.2.2.2.2.2 z).symm

/-- The multivariate Gaussian with the logarithmic covariance satisfies all six
clauses of the finite GFF law predicate. -/
theorem isFiniteGffLaw_multivariateGaussian {n : ℕ} (f : Fin n → TestFn)
    (hfzero : ∀ i, (∫ x : Plane, f i x) = 0) :
    IsFiniteGffLaw f ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      (Matrix.of fun i j => logCovariance (f i) (f j))).toProbabilityMeasure) := by
  unfold IsFiniteGffLaw
  simp only [Measure.coe_toProbabilityMeasure]
  let S : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => logCovariance (f i) (f j)
  have hS : S.PosSemidef := posSemidef_logCovariance f hfzero
  change AEMeasurable id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) ∧ _
  refine ⟨aemeasurable_id, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro i
    apply IsGaussian.memLp_two_id.of_le
    · exact (by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin n) => z i)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z => PiLp.norm_apply_le z i
  · intro i
    change (∫ z : EuclideanSpace ℝ (Fin n), EuclideanSpace.proj i z ∂multivariateGaussian 0 S) = 0
    rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_multivariateGaussian, map_zero]
  · intro i j
    exact covariance_eval_multivariateGaussian hS i j
  · intro z
    rw [charFun_multivariateGaussian hS]
    congr 1
    have hquad : (z : Fin n → ℝ) ⬝ᵥ (Matrix.mulVec S z) = ∑ i, ∑ j,
        z i * logCovariance (f i) (f j) * z j := by
      simp only [dotProduct, Matrix.mulVec, S, Matrix.of_apply, Finset.mul_sum, mul_assoc]
    rw [hquad]
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
    push_cast
    ring

/-- Existence, with the witness identified as Mathlib's multivariate Gaussian. -/
theorem exists_isFiniteGffLaw_eq_multivariateGaussian {n : ℕ} (f : Fin n → TestFn)
    (hfzero : ∀ i, (∫ x : Plane, f i x) = 0) :
    ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)), IsFiniteGffLaw f μ ∧
      (μ : Measure _) = multivariateGaussian 0 (Matrix.of fun i j => logCovariance (f i) (f j)) := by
  exact ⟨_, isFiniteGffLaw_multivariateGaussian f hfzero, rfl⟩

/-- Existence and uniqueness of the finite GFF law, with empty and singular
families included. -/
theorem existsUnique_isFiniteGffLaw {n : ℕ} (f : Fin n → TestFn)
    (hfzero : ∀ i, (∫ x : Plane, f i x) = 0) :
    ∃! μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)), IsFiniteGffLaw f μ := by
  obtain ⟨μ, hμ, _⟩ := exists_isFiniteGffLaw_eq_multivariateGaussian f hfzero
  exact ⟨μ, hμ, fun ν hν => isFiniteGffLaw_unique hν hμ⟩


end Critical2DKPZ.Extensions.GffTangent

end

end
