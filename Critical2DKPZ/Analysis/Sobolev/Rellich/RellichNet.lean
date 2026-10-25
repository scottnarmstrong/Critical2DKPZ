/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichEstimate
public import Critical2DKPZ.Analysis.Sobolev.Rellich.Scaling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Finite derivative bounds control Sobolev energy with quadratic dependence on their common bound.

Adapted from work of A. Bou-Rabee, licensed under Apache 2.0. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- Derivative bounds of size ε on a common compact support give a Sobolev energy bound of size C ε². -/
theorem rkResidual_diff_bound {d : ℕ} {K : Set (Space d)} (hK : IsCompact K)
    (s₀ : ℝ) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (g : Space d → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → tsupport g ⊆ K →
        ∀ (ε : ℝ), 0 < ε →
          (∀ k ≤ m, ∀ x : Space d, ‖iteratedFDeriv ℝ k g x‖ ≤ ε) →
            sobolevNormSq d s₀ g ≤ ENNReal.ofReal (C * ε ^ 2) := by
  obtain ⟨m, C, hC0, hC⟩ := rkResidual_holds d K hK s₀
  refine ⟨m, C, hC0, ?_⟩
  intro g hg hsupp ε hε hbd
  have hgsm : ContDiff ℝ (⊤ : ℕ∞) (fun x => (1 / ε) * g x) := hg.const_smul (1 / ε)
  have hgsupp : tsupport (fun x => (1 / ε) * g x) ⊆ K :=
    (tsupport_mul_subset_right (f := fun _ : Space d => 1 / ε) (g := g)).trans hsupp
  have hgbd : ∀ k ≤ m, ∀ x : Space d,
      ‖iteratedFDeriv ℝ k (fun x => (1 / ε) * g x) x‖ ≤ 1 := by
    intro k hk x
    have hcont : ContDiffAt ℝ (k : ℕ∞) g x :=
      hg.contDiffAt.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
    change ‖iteratedFDeriv ℝ k (fun x : Space d => (1 / ε) • g x) x‖ ≤ 1
    rw [iteratedFDeriv_const_smul_apply' hcont, norm_smul,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ε)]
    calc (1 / ε) * ‖iteratedFDeriv ℝ k g x‖ ≤ (1 / ε) * ε :=
          mul_le_mul_of_nonneg_left (hbd k hk x) (by positivity)
      _ = 1 := by field_simp
  have hkey : ENNReal.ofReal ((1 / ε) ^ 2) * sobolevNormSq d s₀ g ≤ ENNReal.ofReal C := by
    have h := hC (fun x => (1 / ε) * g x) hgsm hgsupp hgbd
    rwa [sobolevNormSq_const_mul] at h
  have hb : (0 : ℝ) ≤ ε ^ 2 := by positivity
  have hfac : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (ε ^ 2) := bot_le
  have hba : ε ^ 2 * (1 / ε) ^ 2 = 1 := by
    rw [← mul_pow]; field_simp
  calc sobolevNormSq d s₀ g
      = ENNReal.ofReal (ε ^ 2) *
          (ENNReal.ofReal ((1 / ε) ^ 2) * sobolevNormSq d s₀ g) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hb, hba, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal C :=
          mul_le_mul_of_nonneg_left hkey hfac
    _ = ENNReal.ofReal (C * ε ^ 2) := by
          rw [← ENNReal.ofReal_mul hb]
          congr 1
          ring


end Critical2DKPZ.Analysis.Sobolev.Rellich

end
