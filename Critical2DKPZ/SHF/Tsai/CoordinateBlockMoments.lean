/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainCoordinateCopies
public import Critical2DKPZ.SHF.Tsai.BlockMomentTransport

/-! # Moment data and independence of coordinate-copy blocks

Coordinate evaluation preserves the original probability measure, so each
copy retains the full block moment predicate. The standard product-space
independence theorem supplies mutual independence of all prefix copies.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Each prefix coordinate-copy block retains the exact original block moment data. -/
theorem hasDeltaBoseMoments_coordinateCopyBlock {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ)
    (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k)) (k : ℕ) (hk : k ≤ K) :
    HasDeltaBoseMoments θ (τ k) (Measure.pi (fun _ : Fin (K + 1) => P))
      (fun ω => coordinateCopyBlock K B ω k) := by
  have h := (hB k hk).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin (K + 1) => P) (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (K + 1)))
  simpa only [coordinateCopyBlock, dite_eq_left hk] using h

/-- The coordinate-copy prefix blocks are mutually independent. -/
theorem iIndepFun_coordinateCopyBlock {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, Measurable (B k)) :
    iIndepFun (fun k : Fin (K + 1) => fun ω => coordinateCopyBlock K B ω k)
      (Measure.pi (fun _ : Fin (K + 1) => P)) := by
  have h := iIndepFun_pi (μ := fun _ : Fin (K + 1) => P) (X := fun k : Fin (K + 1) => B k)
    (fun k => (hB k (Nat.le_of_lt_succ k.is_lt)).aemeasurable)
  have heq : (fun k : Fin (K + 1) => fun ω => coordinateCopyBlock K B ω k) =
      fun (k : Fin (K + 1)) (ω : Fin (K + 1) → Ω) => B k (ω k) := by
    funext k ω
    simp only [coordinateCopyBlock, dite_eq_left (Nat.le_of_lt_succ k.is_lt)]
  rw [heq]
  exact h

end Critical2DKPZ.SHF.Tsai

end
