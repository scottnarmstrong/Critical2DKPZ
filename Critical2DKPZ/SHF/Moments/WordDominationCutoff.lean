/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Localizers
public import Critical2DKPZ.Definitions.TestFn
import Mathlib.Tactic

/-! # Compact first-coordinate cutoffs for pair tests -/

@[expose] public section

noncomputable section

open Set
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Moments

/-- The fixed smooth localizer, viewed as an ordinary compactly supported
continuous function. -/
def collisionWordCompactLocalizer (n : ℕ) : C_c(Plane, ℝ) :=
  ⟨⟨Critical2DKPZ.localizer n, (Critical2DKPZ.localizer n).continuous⟩,
    TestFunctionClass.map_hasCompactSupport (Critical2DKPZ.localizer n)⟩


/-- Every compactly supported pair test is bounded by a constant times a
nonnegative compactly supported cutoff of its first coordinate. -/
theorem exists_pairTest_firstCoordinate_majorant (φ : C_c(Plane × Plane, ℝ)) :
    ∃ M : ℝ, ∃ χ : C_c(Plane, ℝ), 0 ≤ M ∧ (∀ x, 0 ≤ χ x) ∧
      ∀ p : Plane × Plane, |φ p| ≤ M * χ p.1 := by
  let K : Set Plane := Prod.fst '' tsupport φ
  have hK : IsCompact K := φ.hasCompactSupport.image continuous_fst
  obtain ⟨n, hn⟩ := Critical2DKPZ.exists_localizer_eq_one_on_compact hK
  obtain ⟨B₀, hB₀⟩ :=
    φ.hasCompactSupport.exists_bound_of_continuousOn φ.continuous.continuousOn
  let M := max B₀ 0
  let χ := collisionWordCompactLocalizer n
  have hM : 0 ≤ M := le_max_right _ _
  have hχ : ∀ x, 0 ≤ χ x := by
    intro x
    exact Critical2DKPZ.localizer_nonneg n x
  have hφbound (p : Plane × Plane) : |φ p| ≤ M := by
    by_cases hp : φ p = 0
    · simp [hp, M]
    · have hpt : p ∈ tsupport φ := subset_closure (Function.mem_support.mpr hp)
      have h := hB₀ p hpt
      rw [Real.norm_eq_abs] at h
      exact h.trans (le_max_left _ _)
  refine ⟨M, χ, hM, hχ, fun p => ?_⟩
  by_cases hp : φ p = 0
  · simpa [hp] using mul_nonneg hM (hχ p.1)
  · have hpt : p ∈ tsupport φ := subset_closure (Function.mem_support.mpr hp)
    have hfirst : p.1 ∈ K := ⟨p, hpt, rfl⟩
    have hχone : χ p.1 = 1 := by
      simpa [χ, collisionWordCompactLocalizer] using hn n (le_rfl) p.1 hfirst
    rw [hχone, mul_one]
    exact hφbound p

end Critical2DKPZ.SHF.Moments

end
