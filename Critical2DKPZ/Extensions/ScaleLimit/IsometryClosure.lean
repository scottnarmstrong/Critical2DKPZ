/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # Extending a pairing through the closure of its spectral range -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.Extensions.ScaleLimit

variable {V H K : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]

/-- The spectral map, with codomain restricted to the closure of its range. -/
def closureRangeMap (T : V →ₗ[ℝ] H) : V →ₗ[ℝ] T.range.topologicalClosure :=
  T.codRestrict _ (fun v => T.range.le_topologicalClosure (LinearMap.mem_range_self T v))

/-- The original range is dense in its closure, with its inherited norm. -/
theorem denseRange_closureRangeMap (T : V →ₗ[ℝ] H) :
    DenseRange (closureRangeMap T) := by
  rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
  change (closure (Set.range T)) ⊆ closure (Set.range T)
  exact Set.Subset.rfl

/-- Norm equality on the original tests extends to a linear isometry on the closed spectral range. -/
def isometryOnClosure (S : V →ₗ[ℝ] K) (T : V →ₗ[ℝ] H)
    (h : ∀ v, ‖S v‖ = ‖T v‖) : T.range.topologicalClosure →ₗᵢ[ℝ] K :=
  S.extendOfIsometry (denseRange_closureRangeMap T) h

@[simp] theorem isometryOnClosure_apply (S : V →ₗ[ℝ] K) (T : V →ₗ[ℝ] H)
    (h : ∀ v, ‖S v‖ = ‖T v‖) (v : V) :
    isometryOnClosure S T h (closureRangeMap T v) = S v :=
  LinearMap.extendOfIsometry_eq S _ _ v

end Critical2DKPZ.Extensions.ScaleLimit
