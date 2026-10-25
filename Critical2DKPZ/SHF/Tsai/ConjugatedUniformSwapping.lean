/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedLaplaceSwapping
import Mathlib.Tactic

/-! # Uniform conjugated swapping resolvents over all collision labels -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- One resolvent coefficient and damping threshold work simultaneously for all distinct collision pairs. -/
theorem exists_uniform_conjugated_laplace_swapping (n : ℕ) {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) :
    ∃ C R : ℝ, 1 ≤ C ∧ 1 ≤ R ∧ ∀ (α β : CollisionPair n), α ≠ β →
      ∀ rate : ℝ, R ≤ rate →
        WeightedFormBound volume volume (fun y => -(a * fusedOneNorm α y))
          (fun z => a * fusedOneNorm β z) p (p / (p - 1))
          (laplaceTimeKernel rate (fun q : ℝ × FusedConfiguration α × FusedConfiguration β =>
            ENNReal.ofReal (swappingKernel α β q.1 q.2.1 q.2.2))) (ENNReal.ofReal C) := by
  classical
  let Pair : Type := {q : CollisionPair n × CollisionPair n // q.1 ≠ q.2}
  choose c r hc hbound using (fun q : Pair => weightedFormBound_laplace_swapping_conj q.1.1 q.1.2 q.2 hp ha)
  let C : ℝ := 1 + ∑ q : Pair, c q
  let R : ℝ := 1 + ∑ q : Pair, max (r q) 0
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg fun q _ => (hc q).le)
  have hR : 1 ≤ R := le_add_of_nonneg_right (Finset.sum_nonneg fun q _ => le_max_right _ _)
  have hcc (q : Pair) : c q ≤ C := by
    calc
      c q ≤ ∑ q' : Pair, c q' :=
        Finset.single_le_sum (fun q' _ => (hc q').le) (Finset.mem_univ q)
      _ ≤ C := le_add_of_nonneg_left zero_le_one
  have hrr (q : Pair) : r q ≤ R := by
    calc
      r q ≤ max (r q) 0 := le_max_left _ _
      _ ≤ ∑ q' : Pair, max (r q') 0 :=
        Finset.single_le_sum (fun q' _ => le_max_right _ _) (Finset.mem_univ q)
      _ ≤ R := le_add_of_nonneg_left zero_le_one
  refine ⟨C, R, hC, hR, ?_⟩
  intro α β hne rate hrate
  let q : Pair := ⟨(α, β), hne⟩
  exact (hbound q rate ((hrr q).trans hrate)).mono (fun _ _ => le_rfl)
    (ENNReal.ofReal_le_ofReal (hcc q))

end Critical2DKPZ.SHF.Tsai

end
