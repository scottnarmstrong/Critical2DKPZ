/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockMoments

/-! # Consecutive blocks on a natural-indexed dense-time grid

The dense-flow axioms give measurable delta-Bose moment blocks and mutual
independence on each finite prefix of a strictly increasing time sequence.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Each consecutive interval of a natural-indexed dense-time grid has its prescribed block moments. -/
theorem IsDenseSHF.hasDeltaBoseMoments_natConsecutive {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)} (hZ : IsDenseSHF θ D P Z)
    (K : ℕ) (t : ℕ → ℝ) (ht : StrictMono t) (htD : ∀ k ≤ K + 1, t k ∈ D)
    (k : ℕ) (hk : k ≤ K) :
    HasDeltaBoseMoments θ (t (k + 1) - t k) P (Z (t k) (t (k + 1))) :=
  hZ.hasDeltaBoseMoments (htD k (by omega)) (htD (k + 1) (by omega)) (ht (Nat.lt_succ_self k))

/-- The consecutive blocks of a finite natural-indexed grid are mutually independent. -/
theorem IsDenseSHF.iIndepFun_natConsecutive {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z) (K : ℕ) (t : ℕ → ℝ) (ht : StrictMono t)
    (htD : ∀ k ≤ K + 1, t k ∈ D) :
    iIndepFun (fun k : Fin (K + 1) => Z (t k) (t (k + 1))) P := by
  have htf : StrictMono (fun k : Fin (K + 2) => t k) := fun i j hij => ht hij
  exact hZ.2.2.1 (K + 1) (fun k => t k) htf (fun k => htD k (Nat.le_of_lt_succ k.is_lt))

end Critical2DKPZ.SHF.Tsai

end
