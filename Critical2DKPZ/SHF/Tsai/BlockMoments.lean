/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Delta-Bose moments of random measure blocks

Measurable, almost surely locally finite random measures with delta-Bose tensor moments
through order four satisfy the block moment condition from Tsai (2024), equation (2.25).
Subset moments give the corresponding centered moments by inclusion-exclusion.
-/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The heat measure, used for the mean block in the replacement argument. -/
def heatBlock (τ : ℝ) : Measure (Plane × Plane) :=
  volume.withDensity fun p => ENNReal.ofReal (heatKernel τ (p.2 - p.1))


/-- A measurable, almost surely locally finite random measure with delta-Bose tensor moments through order four at duration `τ`, as in Tsai (2024), Definition 1.2(d) and equation (2.25). -/
def HasDeltaBoseMoments (θ τ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Ω → Measure (Plane × Plane)) : Prop :=
  Measurable B ∧ (∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B ω)) ∧
  ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ g g' : Fin n → Plane → ℝ, (∀ i, MemLp (g i) 2) → (∀ i, MemLp (g' i) 2) →
    (∀ᵐ ω ∂P, ∀ i, Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2) (B ω)) ∧
    Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂(B ω)) P ∧
    ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂(B ω)) ∂P =
      ∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, g i (x i)) * (momentKernel n θ τ x y).toReal * ∏ i, g' i (y i)

/-- Every positive-duration block of a dense stochastic heat flow has the delta-Bose moment formulas. -/
theorem IsDenseSHF.hasDeltaBoseMoments {θ : ℝ} {D : Set ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)} (hZ : IsDenseSHF θ D P Z)
    {s t : ℝ} (hs : s ∈ D) (ht : t ∈ D) (hst : s < t) :
    HasDeltaBoseMoments θ (t - s) P (Z s t) := by
  exact ⟨(hZ.1 s hs t ht hst).1, (hZ.1 s hs t ht hst).2,
    fun n hn hn' g g' hg hg' => hZ.2.2.2 n hn hn' s hs t ht hst g g' hg hg'⟩





end Critical2DKPZ.SHF.Tsai

end
