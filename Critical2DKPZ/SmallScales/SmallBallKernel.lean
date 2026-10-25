/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.CompactMollifier
public import Critical2DKPZ.Analysis.Sobolev.Localizers
public import Critical2DKPZ.Definitions.TestFnDilate

/-! # Support and supremum bounds for a nonnegative unit-mass test function -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Distributions

namespace Critical2DKPZ.SmallScales

/-- The fixed unit-mass kernel is bounded by the reciprocal of the first localizer's mass. -/
theorem unitMassTestFn_le (y : Plane) :
    Analysis.Sobolev.unitMassTestFn y ≤
      (∫ z : Plane, Critical2DKPZ.localizer 0 z)⁻¹ :=
  Analysis.Sobolev.unitMassTestFn_le y

/-- The normalized kernel remains supported in the radius-two ball. -/
theorem tsupport_unitMassTestFn_subset :
    tsupport Analysis.Sobolev.unitMassTestFn ⊆ Metric.closedBall (0 : Plane) 2 :=
  Analysis.Sobolev.tsupport_unitMassTestFn_subset

/-- Dilation of a test function supported in a centered ball stays in the correspondingly
scaled ball around its center. -/
theorem tsupport_dilate_subset_closedBall
    (φ : TestFn) (R ε : ℝ) (x : Plane)
    (hφ : tsupport φ ⊆ Metric.closedBall (0 : Plane) R) (hε : 0 < ε) :
    tsupport (φ.dilate ε x) ⊆ Metric.closedBall x (R * ε) := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  intro y hy
  have hφy : φ (ε⁻¹ • (y - x)) ≠ 0 := by
    intro hz
    apply hy
    simp [TestFn.dilate, hz]
  have hφsupport : ε⁻¹ • (y - x) ∈ tsupport φ := subset_tsupport φ hφy
  have hnorm : ‖ε⁻¹ • (y - x)‖ ≤ R := by
    have h := hφ hφsupport
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    simpa only [sub_zero] using h
  have hnorm' : ε⁻¹ * ‖y - x‖ ≤ R := by
    simpa [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε] using hnorm
  apply Metric.mem_closedBall.mpr
  rw [dist_eq_norm]
  calc
    ‖y - x‖ = ε * (ε⁻¹ * ‖y - x‖) := by field_simp
    _ ≤ ε * R := mul_le_mul_of_nonneg_left hnorm' hε.le
    _ = R * ε := by ring

end Critical2DKPZ.SmallScales

end
