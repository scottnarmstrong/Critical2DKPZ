/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic

/-! # The nonnegative collision-diagram series

Each collision word contributes the ordered time-space integral in Tsai (2024), equation (2.13), with product Lebesgue measure on the free collision coordinates. The moment kernel is the free kernel plus the sum over nonempty words; at one particle the collision correction vanishes, and at two particles only the single resummed collision term remains. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- A word's positive kernel, recursively integrated over its first collision interval. -/
noncomputable def diagramKernel {n : ℕ} (θ : ℝ) :
    List (CollisionPair n) → ℝ → Configuration n → Configuration n → ℝ≥0∞
  | [], h, x, y => ENNReal.ofReal (freeKernel n h x y)
  | α :: w, h, x, y =>
      ∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h,
        ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
          ENNReal.ofReal (incomingKernel α r z x) *
          ENNReal.ofReal (collisionKernel α θ (u - r) z z') *
          diagramKernel θ w (h - u) (collisionEmbedding α z') y

/-- The delta-Bose moment kernel is the free kernel plus the nonnegative collision-diagram series. -/
noncomputable def momentKernel (n : ℕ) (θ h : ℝ) (x y : Configuration n) : ℝ≥0∞ :=
  ENNReal.ofReal (freeKernel n h x y) +
    ∑' m : ℕ, ∑ w : CollisionWord n (m + 1), diagramKernel θ (List.ofFn w.1) h x y

/-- Every moment kernel dominates its free part. -/
theorem freeKernel_le_momentKernel (n : ℕ) (θ h : ℝ) (x y : Configuration n) :
    ENNReal.ofReal (freeKernel n h x y) ≤ momentKernel n θ h x y := by
  exact le_self_add


/-- The first-moment kernel is the planar heat kernel. -/
theorem momentKernel_one (θ h : ℝ) (x y : Configuration 1) :
    momentKernel 1 θ h x y = ENNReal.ofReal (heatKernel h (y 0 - x 0)) := by
  simp only [momentKernel, Finset.univ_eq_empty, Finset.sum_empty, tsum_zero, add_zero,
    freeKernel_one]

/-- The one resummed collision contribution to the two-particle moment kernel. -/
noncomputable def twoParticleCorrection (θ h : ℝ) (x y : Configuration 2) : ℝ≥0∞ :=
  diagramKernel θ [pairTwo] h x y

/-- Exactly one diagram word survives in the two-particle series. -/
theorem momentKernel_two (θ h : ℝ) (x y : Configuration 2) :
    momentKernel 2 θ h x y =
      ENNReal.ofReal (heatKernel h (y 0 - x 0) * heatKernel h (y 1 - x 1)) +
      twoParticleCorrection θ h x y := by
  have hsum : (∑' m : ℕ, ∑ w : CollisionWord 2 (m + 1),
      diagramKernel θ (List.ofFn w.1) h x y) = twoParticleCorrection θ h x y := by
    rw [tsum_eq_single 0]
    · rw [← (pairEquivWordOne 2).sum_comp]
      rw [Fintype.sum_subsingleton _ pairTwo]
      change diagramKernel θ (List.ofFn (fun _ : Fin 1 => pairTwo)) h x y = _
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    · intro m hm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      exact Finset.sum_eq_zero fun w _ => isEmptyElim w
  rw [momentKernel, hsum]
  simp only [freeKernel, Fin.prod_univ_two]

/-- The exact single-collision integral in the canonical free collision coordinates. -/
theorem twoParticleCorrection_eq_integral (θ h : ℝ) (x y : Configuration 2) :
    twoParticleCorrection θ h x y =
      ∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h,
        ∫⁻ z : FusedConfiguration pairTwo, ∫⁻ z' : FusedConfiguration pairTwo,
          ENNReal.ofReal (incomingKernel pairTwo r z x) *
          ENNReal.ofReal (collisionKernel pairTwo θ (u - r) z z') *
          ENNReal.ofReal (freeKernel 2 (h - u) (collisionEmbedding pairTwo z') y) := rfl

end Critical2DKPZ.DeltaBose
