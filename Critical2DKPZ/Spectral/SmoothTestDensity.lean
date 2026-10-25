/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Localizers
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-! # Uniform approximation of compactly supported continuous functions by tests -/

@[expose] public section

noncomputable section

open Set
open scoped CompactlySupported

namespace Critical2DKPZ.Spectral

/-- One canonical localizer works for smooth test approximations of a fixed compactly supported
continuous function at every accuracy. Thus all approximants can be kept in one compact set. -/
theorem exists_localizer_uniform_testFn_approx (f : C_c(Plane, ℝ)) :
    ∃ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ φ : TestFn, tsupport φ ⊆ tsupport (Critical2DKPZ.localizer n) ∧
        ∀ x : Plane, |φ x - f x| < ε := by
  obtain ⟨n, hn⟩ := Critical2DKPZ.exists_localizer_eq_one_on_compact
    f.hasCompactSupport.isCompact
  refine ⟨n, fun ε hε => ?_⟩
  obtain ⟨u, huSmooth, hu⟩ :=
    (CompactlySupportedContinuousMapClass.uniformContinuous f).exists_contDiff_dist_le hε
  let χ : TestFn := Critical2DKPZ.localizer n
  let φ : TestFn := {
    toFun := fun x => χ x * u x
    contDiff' := χ.contDiff.mul huSmooth
    hasCompactSupport' := χ.hasCompactSupport.mul_right
    tsupport_subset' := subset_univ _ }
  refine ⟨φ, ?_, fun x => ?_⟩
  · change tsupport (fun x : Plane => χ x * u x) ⊆ tsupport χ
    exact tsupport_mul_subset_left
  · have hcut : χ x * f x = f x := by
      by_cases hfx : f x = 0
      · simp [hfx]
      · rw [hn n le_rfl x (subset_tsupport f hfx), one_mul]
    have herror : φ x - f x = χ x * (u x - f x) := by
      change χ x * u x - f x = χ x * (u x - f x)
      rw [mul_sub, hcut]
    rw [herror, abs_mul]
    have hχnonneg : 0 ≤ χ x := Critical2DKPZ.localizer_nonneg n x
    have hχle : χ x ≤ 1 := Critical2DKPZ.localizer_le_one n x
    have hχabs : |χ x| ≤ 1 := by rw [abs_of_nonneg hχnonneg]; exact hχle
    have hu' : |u x - f x| < ε := by simpa only [Real.dist_eq] using hu x
    exact (mul_le_of_le_one_left (abs_nonneg _) hχabs).trans_lt
      (by simpa only [one_mul] using hu')


/-- A chosen sequence of compactly supported smooth approximations to a compactly supported
continuous function. All terms have support in one compact localizer support. -/
noncomputable def uniformTestApproxSequence (f : C_c(Plane, ℝ)) : ℕ → TestFn :=
  let happrox := Classical.choose_spec (exists_localizer_uniform_testFn_approx f)
  fun n => Classical.choose (happrox (1 / ((n : ℝ) + 1)) (by positivity))

/-- Each chosen smooth approximation has support in the common localizer support. -/
theorem uniformTestApproxSequence_support (f : C_c(Plane, ℝ)) (n : ℕ) :
    tsupport (uniformTestApproxSequence f n) ⊆
      tsupport (Critical2DKPZ.localizer
        (Classical.choose (exists_localizer_uniform_testFn_approx f))) := by
  unfold uniformTestApproxSequence
  exact (Classical.choose_spec
    ((Classical.choose_spec (exists_localizer_uniform_testFn_approx f))
      (1 / ((n : ℝ) + 1)) (by positivity))).1

/-- The uniform error of the chosen approximation tends to zero at an explicit rate. -/
theorem uniformTestApproxSequence_error (f : C_c(Plane, ℝ)) (n : ℕ) (x : Plane) :
    |uniformTestApproxSequence f n x - f x| < 1 / ((n : ℝ) + 1) := by
  unfold uniformTestApproxSequence
  exact (Classical.choose_spec
    ((Classical.choose_spec (exists_localizer_uniform_testFn_approx f))
      (1 / ((n : ℝ) + 1)) (by positivity))).2 x

end Critical2DKPZ.Spectral

end
