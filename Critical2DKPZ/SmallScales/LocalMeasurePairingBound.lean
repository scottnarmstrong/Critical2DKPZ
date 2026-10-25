/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Distr
public import Critical2DKPZ.Definitions.TestFnDilate
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # A local measure bound for dilated distribution pairings -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported Distributions ENNReal

namespace Critical2DKPZ.SmallScales

/-- Integrating a nonnegative function supported in a finite-measure set is bounded by its
pointwise bound times the measure of that set. -/
private theorem integral_nonneg_le_of_support_subset (μ : Measure Plane)
    (S : Set Plane) (hS : MeasurableSet S) (hSfinite : μ S < ∞)
    (f : Plane → ℝ) (hf : Integrable f μ)
    (hzero : ∀ x, x ∉ S → f x = 0)
    (hnonneg : ∀ x, 0 ≤ f x) (C : ℝ) (hbound : ∀ x ∈ S, f x ≤ C) :
    0 ≤ ∫ x, f x ∂μ ∧ ∫ x, f x ∂μ ≤ C * (μ S).toReal := by
  have hconst : IntegrableOn (fun _ : Plane => C) S μ :=
    integrableOn_const (ne_of_lt hSfinite)
  have hset : ∫ x in S, f x ∂μ ≤ ∫ x in S, C ∂μ :=
    setIntegral_mono_on₀ hf.integrableOn hconst hS.nullMeasurableSet hbound
  refine ⟨integral_nonneg_of_ae (ae_of_all _ hnonneg), ?_⟩
  calc
    ∫ x, f x ∂μ = ∫ x in S, f x ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ ≤ ∫ x in S, C ∂μ := hset
    _ = C * (μ S).toReal := by
      simp only [setIntegral_const, smul_eq_mul]
      change (μ S).toReal * C = C * (μ S).toReal
      ring

/-- A local difference-of-measures representation bounds the pairing with a dilated nonnegative test by its supremum times the total measure of a set containing its support. -/
theorem abs_pairing_le_of_local_measure_representation
    (T : Distr) (μ ν : Measure Plane) (x : Plane) {ε : ℝ}
    (φ : TestFn) (M : ℝ) (hφnonneg : ∀ y, 0 ≤ φ y) (hφbound : ∀ y, φ y ≤ M)
    (B : Set Plane) (hB : MeasurableSet B)
    (hSupport : tsupport (φ.dilate ε x) ⊆ B)
    (hμfinite : μ B < ∞) (hνfinite : ν B < ∞)
    (hRep : T (φ.dilate ε x) =
      (∫ y, φ.dilate ε x y ∂μ) - ∫ y, φ.dilate ε x y ∂ν) :
    |T (φ.dilate ε x)| ≤ ε⁻¹ ^ 2 * M * ((μ + ν) B).toReal := by
  let f : Plane → ℝ := φ.dilate ε x
  let C : ℝ := ε⁻¹ ^ 2 * M
  have hfzero : ∀ y, y ∉ B → f y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hyf
    exact hy (hSupport hyf)
  have hfnonneg (y : Plane) : 0 ≤ f y := by
    simp only [f, TestFn.dilate]
    exact mul_nonneg (sq_nonneg ε⁻¹) (hφnonneg _)
  have hfbound (y : Plane) (hy : y ∈ B) : f y ≤ C := by
    simp only [f, C, TestFn.dilate]
    exact mul_le_mul_of_nonneg_left (hφbound _) (sq_nonneg ε⁻¹)
  have hfnorm (y : Plane) : ‖f y‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnonneg y)]
    simp only [f, C, TestFn.dilate]
    exact mul_le_mul_of_nonneg_left (hφbound _) (sq_nonneg ε⁻¹)
  have hμOn : IntegrableOn f B μ := by
    exact IntegrableOn.of_bound hμfinite
      ((φ.dilate ε x).continuous.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      C (ae_of_all _ hfnorm)
  have hνOn : IntegrableOn f B ν := by
    exact IntegrableOn.of_bound hνfinite
      ((φ.dilate ε x).continuous.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      C (ae_of_all _ hfnorm)
  have hμInt : Integrable f μ :=
    (integrableOn_iff_integrable_of_support_subset
      (Set.Subset.trans (subset_tsupport f) hSupport)).mp hμOn
  have hνInt : Integrable f ν :=
    (integrableOn_iff_integrable_of_support_subset
      (Set.Subset.trans (subset_tsupport f) hSupport)).mp hνOn
  have hμ := integral_nonneg_le_of_support_subset μ B hB hμfinite f hμInt
    hfzero hfnonneg C hfbound
  have hν := integral_nonneg_le_of_support_subset ν B hB hνfinite f hνInt
    hfzero hfnonneg C hfbound
  have hadd : ((μ + ν) B).toReal = (μ B).toReal + (ν B).toReal := by
    rw [Measure.add_apply μ ν B]
    exact ENNReal.toReal_add (ne_of_lt hμfinite) (ne_of_lt hνfinite)
  calc
    |T (φ.dilate ε x)| =
        |(∫ y, f y ∂μ) - ∫ y, f y ∂ν| := by simpa [f] using congrArg abs hRep
    _ ≤ |∫ y, f y ∂μ| + |∫ y, f y ∂ν| := by
      simpa [abs_neg] using
        (abs_sub_le (∫ y, f y ∂μ) (0 : ℝ) (∫ y, f y ∂ν))
    _ = (∫ y, f y ∂μ) + ∫ y, f y ∂ν := by
      rw [abs_of_nonneg hμ.1, abs_of_nonneg hν.1]
    _ ≤ C * (μ B).toReal + C * (ν B).toReal := add_le_add hμ.2 hν.2
    _ = ε⁻¹ ^ 2 * M * ((μ + ν) B).toReal := by
      rw [hadd]
      dsimp [C]
      ring

end Critical2DKPZ.SmallScales

end
