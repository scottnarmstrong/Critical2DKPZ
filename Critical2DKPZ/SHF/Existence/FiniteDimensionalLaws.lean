/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.SubseqExistence
public import Critical2DKPZ.SHF.Tsai.Defs
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Finite-dimensional laws -/

@[expose] public section

open MeasureTheory
open scoped CompactlySupported Topology
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai

noncomputable section

namespace Critical2DKPZ.SHF.Existence

universe u v

/-- Every subsequential polymer limit on a countable nonnegative time set satisfies the SHF conditions on that set, with parameter shifted by the Euler–Mascheroni constant. -/
def SubseqLimitsAreDense (ϑ : ℝ) : Prop :=
  ∀ (D : Set ℝ), D.Countable → (∀ s ∈ D, 0 ≤ s) → ∀ (ψ : ℕ → ℕ), StrictMono ψ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsPolymerSubseqLimit ϑ D ψ P Z →
        IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z

/-- The SHF conditions determine the finite-dimensional random-measure laws on each bounded dense time set. -/
def DenseSHFUnique (θ : ℝ) : Prop :=
  ∀ (B : ℝ), 0 < B → ∀ (D : Set ℝ), D ⊆ Set.Icc 0 B → Set.Icc 0 B ⊆ closure D →
    ∀ {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
      (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
      (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)),
      IsDenseSHF θ D P Z → IsDenseSHF θ D P' Z' → ∀ (k : ℕ) (s t : Fin k → ℝ),
        (∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) →
        P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω)

/-- A subsequential polymer limit on `D` is one on every subset of `D`. -/
theorem isPolymerSubseqLimit_mono {ϑ : ℝ} {D D' : Set ℝ} (hD' : D' ⊆ D) {ψ : ℕ → ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z) : IsPolymerSubseqLimit ϑ D' ψ P Z := by
  refine ⟨?_, ?_⟩
  · intro s hs t ht hst
    exact hZ.1 s (hD' hs) t (hD' ht) hst
  · intro k s t hTimes φ χ
    exact hZ.2 k s t (fun i => ⟨hD' (hTimes i).1, hD' (hTimes i).2.1,
      (hTimes i).2.2⟩) φ χ


end Critical2DKPZ.SHF.Existence

end
