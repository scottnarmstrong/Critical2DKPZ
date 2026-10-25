/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainReadoutLaws
public import Critical2DKPZ.SHF.Tsai.IndependentCopies

/-! # Chain pairings on independent coordinate copies

Evaluating each independent block on its own probability coordinate preserves the joint
laws of finite families of measurable chain pairings.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- One independent coordinate per prefix block, extended by zero outside the finite prefix. -/
def coordinateCopyBlock {Ω : Type*} (K : ℕ) (B : ℕ → Ω → Measure (Plane × Plane))
    (ω : Fin (K + 1) → Ω) (k : ℕ) : Measure (Plane × Plane) :=
  if hk : k ≤ K then B k (ω ⟨k, Nat.lt_succ_of_le hk⟩) else 0

/-- Prefix coordinate-copy blocks are measurable whenever their original blocks are measurable. -/
theorem measurable_coordinateCopyBlock {Ω : Type*} [MeasurableSpace Ω]
    (K : ℕ) (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, Measurable (B k))
    (k : ℕ) (hk : k ≤ K) : Measurable (fun ω => coordinateCopyBlock K B ω k) := by
  simp only [coordinateCopyBlock, dite_eq_left hk]
  exact (hB k hk).comp (measurable_pi_apply _)

/-- Almost-sure local finiteness is retained by each independent coordinate copy. -/
theorem ae_locallyFinite_coordinateCopyBlock {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (B : ℕ → Ω → Measure (Plane × Plane))
    (hlf : ∀ k ≤ K, ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B k ω)) (k : ℕ) (hk : k ≤ K) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin (K + 1) => P),
      IsLocallyFiniteMeasure (coordinateCopyBlock K B ω k) := by
  have h := (measurePreserving_eval (fun _ : Fin (K + 1) => P)
    (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (K + 1))).quasiMeasurePreserving.ae (hlf k hk)
  simpa only [coordinateCopyBlock, dite_eq_left hk] using h

/-- Independent blocks and their separate coordinate copies give the same joint laws of endpoint pairings. -/
theorem map_chainReadouts_eq_coordinateCopies {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, Measurable (B k))
    (hlf : ∀ k ≤ K, ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B k ω))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → Plane → ℝ) (hw : ∀ k, Measurable (w k)) {ι : Type*}
    (F : ι → Plane × Plane → ℝ) (hF : ∀ i, Measurable (F i)) :
    P.map (fun ω i => ∫ p, F i p ∂chainProduct (fun k => B k ω) w K) =
      (Measure.pi (fun _ : Fin (K + 1) => P)).map (fun ω i =>
        ∫ p, F i p ∂chainProduct (coordinateCopyBlock K B ω) w K) := by
  have hLaw := iIndepFun.map_eq_map_coordinateCopies P (K + 1) (fun k => B k)
    (fun k => hB k (Nat.le_of_lt_succ k.is_lt)) hind
  have hcopy : (fun ω : Fin (K + 1) → Ω => fun k : Fin (K + 1) => coordinateCopyBlock K B ω k) =
      fun (ω : Fin (K + 1) → Ω) (k : Fin (K + 1)) => B k (ω k) := by
    funext ω k
    simp only [coordinateCopyBlock, dite_eq_left (Nat.le_of_lt_succ k.is_lt)]
  rw [← hcopy] at hLaw
  exact map_chainReadouts_eq_of_block_law P (Measure.pi (fun _ : Fin (K + 1) => P)) K
    B (fun k ω => coordinateCopyBlock K B ω k) hB (measurable_coordinateCopyBlock K B hB)
    hlf (ae_locallyFinite_coordinateCopyBlock P K B hlf) hLaw w hw F hF

end Critical2DKPZ.SHF.Tsai

end
