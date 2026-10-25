/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Localization
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! On each fixed compact support, a distribution is controlled by finitely many derivative supremum seminorms. -/

public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace Critical2DKPZ

/-- Every real distribution has finite order on each fixed compact test-function space. -/
theorem exists_distribution_compact_order_bound (T : Distr) (K : Compacts Plane) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ φ : ContDiffMapSupportedIn Plane ℝ ⊤ K,
        ‖T (TestFunction.ofSupportedIn (Set.subset_univ _) φ)‖ ≤
          C * ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ := by
  let iK : ContDiffMapSupportedIn Plane ℝ ⊤ K →L[ℝ] TestFn :=
    TestFunction.ofSupportedInCLM ℝ (Set.subset_univ _)
  let q : Seminorm ℝ (ContDiffMapSupportedIn Plane ℝ ⊤ K) :=
    (normSeminorm ℝ ℝ).comp (T.toLinearMap.comp iK.toLinearMap)
  have hq : Continuous q := (T.continuous.comp iK.continuous).norm
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ Plane ℝ ⊤ K) q hq
  refine ⟨s.sup id, C, C.coe_nonneg, fun φ => ?_⟩
  have hs : s ⊆ Finset.Iic (s.sup id) := by
    intro j hj
    exact Finset.mem_Iic.mpr (Finset.le_sup (f := id) hj)
  have hsup : s.sup (ContDiffMapSupportedIn.seminorm ℝ Plane ℝ ⊤ K) ≤
      (Finset.Iic (s.sup id)).sup (ContDiffMapSupportedIn.seminorm ℝ Plane ℝ ⊤ K) :=
    Finset.sup_mono hs
  have hbound := hC φ
  change q φ ≤ (C : ℝ) * _
  exact hbound.trans (mul_le_mul_of_nonneg_left (hsup φ) C.coe_nonneg)

end Critical2DKPZ

end
