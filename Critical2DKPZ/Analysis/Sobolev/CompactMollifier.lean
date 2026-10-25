/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Localizers

/-!
# A concrete compactly supported unit-mass test kernel

The first member of the countable localizer family is nonnegative, compactly supported, and equal
to one near the origin. Normalizing its positive integral gives a smooth compactly supported
probability density.
-/

public section

noncomputable section

open MeasureTheory
open scoped Distributions

namespace Critical2DKPZ.Analysis.Sobolev

/-- The mass of the first cutoff is strictly positive. -/
theorem integral_localizer_zero_pos : 0 < ∫ x : Plane, localizer 0 x := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    (localizer 0).continuous (localizer 0).hasCompactSupport ?_ ?_
  · intro x
    exact localizer_nonneg 0 x
  · rw [localizer_eq_one_of_mem_closedBall 0]
    · norm_num
    · simp [Metric.mem_closedBall]

/-- The first cutoff normalized to have unit integral. -/
noncomputable def unitMassTestFn : TestFn :=
  (∫ x : Plane, localizer 0 x)⁻¹ • localizer 0

/-- The concrete smooth compactly supported kernel has mass one. -/
theorem integral_unitMassTestFn : ∫ x : Plane, unitMassTestFn x = 1 := by
  change ∫ x : Plane, (∫ y : Plane, localizer 0 y)⁻¹ * localizer 0 x = 1
  rw [integral_const_mul]
  have hI : 0 < ∫ y : Plane, localizer 0 y := integral_localizer_zero_pos
  field_simp

/-- The concrete unit-mass test kernel is nonnegative. -/
theorem unitMassTestFn_nonneg (x : Plane) : 0 ≤ unitMassTestFn x := by
  change 0 ≤ (∫ y : Plane, localizer 0 y)⁻¹ * localizer 0 x
  exact mul_nonneg (inv_nonneg.mpr (integral_localizer_zero_pos.le)) (localizer_nonneg 0 x)

/-- The normalized unit-mass kernel is bounded by the reciprocal normalizing constant. -/
theorem unitMassTestFn_le (x : Plane) :
    unitMassTestFn x ≤ (∫ y : Plane, localizer 0 y)⁻¹ := by
  change (∫ y : Plane, localizer 0 y)⁻¹ * localizer 0 x ≤
    (∫ y : Plane, localizer 0 y)⁻¹
  calc
    _ ≤ (∫ y : Plane, localizer 0 y)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left (localizer_le_one 0 x)
        (inv_nonneg.mpr integral_localizer_zero_pos.le)
    _ = _ := mul_one _

/-- The normalized unit-mass kernel keeps the radius-two support of its defining localizer. -/
theorem tsupport_unitMassTestFn_subset :
    tsupport unitMassTestFn ⊆ Metric.closedBall (0 : Plane) 2 := by
  calc
    tsupport unitMassTestFn ⊆ tsupport (localizer 0) := by
      change tsupport (fun y : Plane =>
        (∫ z : Plane, localizer 0 z)⁻¹ * localizer 0 y) ⊆ _
      exact tsupport_mul_subset_right
    _ = Metric.closedBall (0 : Plane) 2 := by simpa using tsupport_localizer 0

end Critical2DKPZ.Analysis.Sobolev

end
