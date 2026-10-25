/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedBounds
import Mathlib.Tactic

/-! # Uniform constants for the conjugated incoming and outgoing endpoints -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- One constant controls both conjugated endpoint orientations for every collision label and positive time. -/
theorem exists_uniform_conjugated_endpoint_bounds (n : ℕ) {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (α : CollisionPair n) (t : ℝ), 0 < t →
      WeightedFormBound volume volume (fun y => -(a * fusedOneNorm α y))
        (fun x => a * configurationOneNorm x) p (p / (p - 1))
        (fun (y : FusedConfiguration α) (x : Configuration n) => ENNReal.ofReal (incomingKernel α t y x))
        (ENNReal.ofReal (c * Real.exp (c * t) * t ^ (-1 / p))) ∧
      WeightedFormBound volume volume (fun x => -(a * configurationOneNorm x))
        (fun y => a * fusedOneNorm α y) p (p / (p - 1))
        (fun (x : Configuration n) (y : FusedConfiguration α) => ENNReal.ofReal (incomingKernel α t y x))
        (ENNReal.ofReal (c * Real.exp (c * t) * t ^ (-(p - 1) / p))) := by
  classical
  choose ci hci hi using (fun α : CollisionPair n => weightedFormBound_incoming_conj α hp ha)
  choose co hco ho using (fun α : CollisionPair n => weightedFormBound_outgoing_conj α hp ha)
  let D : CollisionPair n → ℝ := fun α => ci α + co α
  have hD (α : CollisionPair n) : 0 < D α := add_pos (hci α) (hco α)
  let c : ℝ := 1 + ∑ α : CollisionPair n, D α
  have hc1 : 1 ≤ c := le_add_of_nonneg_right (Finset.sum_nonneg fun α _ => (hD α).le)
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  have hDc (α : CollisionPair n) : D α ≤ c := by
    calc
      D α ≤ ∑ β : CollisionPair n, D β :=
        Finset.single_le_sum (fun β _ => (hD β).le) (Finset.mem_univ α)
      _ ≤ c := le_add_of_nonneg_left zero_le_one
  have hinc (α : CollisionPair n) : ci α ≤ c := by
    have h := hDc α
    dsimp [D] at h
    linarith only [h, hco α]
  have hout (α : CollisionPair n) : co α ≤ c := by
    have h := hDc α
    dsimp [D] at h
    linarith only [h, hci α]
  have hscalar (d b t : ℝ) (hdc : d ≤ c) (ht : 0 < t) :
      ENNReal.ofReal (d * Real.exp (d * t) * t ^ b) ≤
        ENNReal.ofReal (c * Real.exp (c * t) * t ^ b) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hdc (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdc ht.le))
        (Real.exp_pos _).le hc0) (Real.rpow_nonneg ht.le _)
  refine ⟨c, hc1, ?_⟩
  intro α t ht
  constructor
  · exact (hi α t ht).mono (fun _ _ => le_rfl) (hscalar (ci α) (-1 / p) t (hinc α) ht)
  · exact (ho α t ht).mono (fun _ _ => le_rfl) (hscalar (co α) (-(p - 1) / p) t (hout α) ht)

end Critical2DKPZ.SHF.Tsai

end
