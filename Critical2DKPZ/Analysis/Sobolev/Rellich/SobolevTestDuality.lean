/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.DualityAssembly
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Opposite-order Sobolev duality for smooth compactly supported functions.

Adapted from work of A. Bou-Rabee, licensed under Apache 2.0. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

section Producers

variable {d : ℕ} {D : Set (Space d)} {φ : Space d → ℝ}

/-- A test function is integrable. -/
theorem IsTestFn.integrable (h : IsTestFn D φ) : Integrable φ :=
  h.1.continuous.integrable_of_hasCompactSupport h.2.1

/-- A test function lies in `L²`. -/
theorem IsTestFn.memLp_two (h : IsTestFn D φ) : MemLp φ 2 volume :=
  h.1.continuous.memLp_of_hasCompactSupport h.2.1

/-- The reflected translate `t ↦ φ (x - t)` of a test function is a test function, on the
reflected translate of its domain. -/
theorem IsTestFn.comp_sub_left (h : IsTestFn D φ) (x : Space d) :
    IsTestFn ((fun t => x - t) ⁻¹' D) (fun t => φ (x - t)) := by
  refine ⟨h.1.comp (contDiff_const.sub contDiff_id), ?_, ?_⟩
  · exact h.2.1.comp_homeomorph (Homeomorph.subLeft x)
  · have e : tsupport (fun t => φ (x - t)) = (fun t => x - t) ⁻¹' tsupport φ := by
      unfold tsupport
      have e0 : Function.support (fun t => φ (x - t))
          = (Homeomorph.subLeft x) ⁻¹' Function.support φ := rfl
      rw [e0, ← (Homeomorph.subLeft x).preimage_closure]
      rfl
    rw [e]
    exact Set.preimage_mono h.2.2

/-- A directional derivative of a test function is a test function on the same domain. -/
theorem IsTestFn.fderiv_apply (h : IsTestFn D φ) (v : Space d) :
    IsTestFn D (fun t => fderiv ℝ φ t v) := by
  refine ⟨?_, h.2.1.fderiv_apply ℝ v, (tsupport_fderiv_apply_subset ℝ v).trans h.2.2⟩
  exact (h.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

end Producers

section Wrapper

variable {d : ℕ} {D₁ D₂ : Set (Space d)} {f g : Space d → ℝ}

/-- **The `H^s`–`H^{−s}` duality bound for test functions.**  The two test functions live on
independent domains `D₁`, `D₂`; no finiteness of the Sobolev norms is needed, since the bound is
in `ℝ≥0∞`. -/
theorem sobolevDualityBound_of_isTestFn (s : ℝ) (hf : IsTestFn D₁ f) (hg : IsTestFn D₂ g) :
    ENNReal.ofReal (|∫ x, f x * g x| ^ 2) ≤ sobolevNormSq d s f * sobolevNormSq d (-s) g :=
  sobolevDualityBound_of_memLp s hf.memLp_two hg.memLp_two hf.integrable hg.integrable




end Wrapper

section Consumers

variable {d : ℕ}





end Consumers

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
