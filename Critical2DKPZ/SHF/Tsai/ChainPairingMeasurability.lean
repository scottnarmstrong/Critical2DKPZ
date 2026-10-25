/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockModification
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Almost-everywhere measurability of chain pairings

The block axioms give local finiteness almost surely. Canonical modifications
produce a measurable chain equal to the original chain almost surely. Both
positive and real endpoint pairings are therefore almost-everywhere measurable.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The actual finite chain is a.e. measurable under a.e. local finiteness of its input blocks. -/
theorem aemeasurable_chainProduct {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (K : ℕ)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, Measurable (B k))
    (hlf : ∀ k ≤ K, ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B k ω))
    (w : ℕ → Plane → ℝ) (hw : ∀ k, Measurable (w k)) :
    AEMeasurable (fun ω => chainProduct (fun k => B k ω) w K) P := by
  let E := CompactExhaustion.choice (Plane × Plane)
  let B' k := RandomMeasure.locallyFiniteMeasureModification E (B k)
  have hB'm (k) (hk : k ≤ K) : Measurable (B' k) := by
    classical
    exact Measurable.ite (RandomMeasure.measurableSet_locallyFiniteEvent E (B k) (hB k hk))
      (hB k hk) measurable_const
  have hB'lf (ω) (k) (_ : k ≤ K) : IsLocallyFiniteMeasure (B' k ω) :=
    RandomMeasure.locallyFinite_locallyFiniteMeasureModification E (B k) ω
  have hmod (k) (hk : k ≤ K) : B' k =ᵐ[P] B k :=
    RandomMeasure.ae_eq_radonValuedModification E P (B k) (hlf k hk)
  exact (measurable_chainProduct K B' hB'm hB'lf w hw).aemeasurable.congr
    (chainProduct_congr_ae K B' B hmod w)


/-- Measurable endpoint tests give measurable pairings for everywhere locally finite input blocks. -/
theorem measurable_integral_chainProduct {Ω : Type*} [MeasurableSpace Ω] (K : ℕ)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, Measurable (B k))
    (hlf : ∀ ω, ∀ k ≤ K, IsLocallyFiniteMeasure (B k ω))
    (w : ℕ → Plane → ℝ) (hw : ∀ k, Measurable (w k))
    (F : Plane × Plane → ℝ) (hF : Measurable F) :
    Measurable (fun ω => ∫ p, F p ∂chainProduct (fun k => B k ω) w K) := by
  let κ : Kernel (Measure (Plane × Plane)) (Plane × Plane) := ⟨id, measurable_id⟩
  have hm : Measurable (fun μ : Measure (Plane × Plane) => ∫ p, F p ∂μ) :=
    (hF.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  exact hm.comp (measurable_chainProduct K B hB hlf w hw)


end Critical2DKPZ.SHF.Tsai

end
