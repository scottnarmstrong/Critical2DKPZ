/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.PathReversal
import Mathlib.Tactic

/-! # Endpoint symmetry of the full positive collision-diagram series -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Nonempty diagrams vanish when their ordered time simplex is empty. -/
theorem diagramKernel_of_nonpos {n : ℕ} (θ : ℝ) {w : List (CollisionPair n)}
    (hw : w ≠ []) {t : ℝ} (ht : t ≤ 0) (x y : Configuration n) :
    diagramKernel θ w t x y = 0 := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons α w =>
    rw [diagramKernel, Ioo_eq_empty_of_le ht, Measure.restrict_empty, lintegral_zero_measure]

/-- Reversing a word transposes its entire ordered time-space diagram. -/
theorem diagramKernel_reverse {n : ℕ} (θ : ℝ) (w : List (CollisionPair n))
    (t : ℝ) (x y : Configuration n) :
    diagramKernel θ w t x y = diagramKernel θ w.reverse t y x := by
  by_cases ht : 0 < t
  · calc diagramKernel θ w t x y = pathTimeKernel θ w id id (t, x, y) := by
          rw [pathTimeKernel_eq_diagram θ w measurable_id measurable_id, causalKernel_of_pos _ ht]
          rfl
        _ = pathTimeKernel θ w.reverse id id (t, y, x) :=
          congrFun (pathTimeKernel_transpose θ w measurable_id measurable_id) (t, y, x)
        _ = diagramKernel θ w.reverse t y x := by
          rw [pathTimeKernel_eq_diagram θ w.reverse measurable_id measurable_id, causalKernel_of_pos _ ht]
          rfl
  · by_cases hw : w = []
    · subst w
      exact congrArg ENNReal.ofReal (freeKernel_symm n t x y)
    · have hwr : w.reverse ≠ [] := fun he => hw (by
        have hn := congrArg List.reverse he
        simpa only [List.reverse_reverse, List.reverse_nil] using hn)
      rw [diagramKernel_of_nonpos θ hw (not_lt.mp ht), diagramKernel_of_nonpos θ hwr (not_lt.mp ht)]

/-- List and collision-word reversal are the same ordered-label operation. -/
theorem CollisionWord.ofFn_reverse {n m : ℕ} (w : CollisionWord n m) :
    List.ofFn w.reverse.1 = (List.ofFn w.1).reverse := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_reverse]
  · intro i hi hi'
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn, CollisionWord.reverse]
    apply congrArg w.1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

/-- Endpoint exchange for the complete moment kernel, for every particle number. -/
theorem momentKernel_symm (n : ℕ) (θ t : ℝ) (x y : Configuration n) :
    momentKernel n θ t x y = momentKernel n θ t y x := by
  unfold momentKernel
  rw [freeKernel_symm n t x y]
  congr 1
  apply tsum_congr
  intro m
  calc (∑ w : CollisionWord n (m + 1), diagramKernel θ (List.ofFn w.1) t x y)
      = ∑ w : CollisionWord n (m + 1), diagramKernel θ (List.ofFn w.reverse.1) t y x := by
        apply Finset.sum_congr rfl
        intro w _
        rw [CollisionWord.ofFn_reverse]
        exact diagramKernel_reverse θ _ t x y
    _ = ∑ w : CollisionWord n (m + 1), diagramKernel θ (List.ofFn w.1) t y x :=
      (reverseWordEquiv n (m + 1)).sum_comp (fun w => diagramKernel θ (List.ofFn w.1) t y x)

end Critical2DKPZ.DeltaBose
