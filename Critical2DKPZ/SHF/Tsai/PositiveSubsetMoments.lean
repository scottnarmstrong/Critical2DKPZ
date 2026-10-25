/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockPositiveExtension

/-! # Positive subset moments, including the empty subset

The increasing enumeration of a label subset turns its product moment into
the corresponding lower-particle moment kernel. At zero particles both
sides equal one; this case uses the probability normalization explicitly.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The zero-particle moment kernel is the empty product, equal to one. -/
theorem momentKernel_zero (θ τ : ℝ) (x y : Configuration 0) :
    momentKernel 0 θ τ x y = 1 := by
  simp only [momentKernel, Finset.univ_eq_empty, Finset.sum_empty, tsum_zero, add_zero,
    freeKernel, Finset.prod_empty, ENNReal.ofReal_one]

/-- The positive moment formula includes zero particles on a probability space. -/
theorem HasDeltaBoseMoments.lintegral_prod_eq_of_le_four {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : Ω → Measure (Plane × Plane)} (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ)
    {n : ℕ} (hn : n ≤ 4) (f f' : Fin n → Plane → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hf' : ∀ i, Measurable (f' i)) :
    (∫⁻ ω, ∏ i, (∫⁻ p, f i p.1 * f' i p.2 ∂B ω) ∂P) =
      ∫⁻ x : Configuration n, ∫⁻ y : Configuration n,
        (∏ i, f i (x i)) * momentKernel n θ τ x y * ∏ i, f' i (y i) := by
  by_cases hzero : n = 0
  · subst n
    simp only [Finset.univ_eq_empty, Finset.prod_empty, momentKernel_zero,
      mul_one, lintegral_const, measure_univ, volume_pi, Measure.pi_empty_univ]
  · exact hB.lintegral_prod_eq hτ (Nat.one_le_iff_ne_zero.mpr hzero) hn f f' hf hf'

/-- Every subset of at most four labels has its literal lower-particle positive moment. -/
theorem HasDeltaBoseMoments.lintegral_prod_finset_eq {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : Ω → Measure (Plane × Plane)} (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ)
    {n : ℕ} (hn : n ≤ 4) (S : Finset (Fin n)) (f f' : Fin n → Plane → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hf' : ∀ i, Measurable (f' i)) :
    (∫⁻ ω, ∏ i ∈ S, (∫⁻ p, f i p.1 * f' i p.2 ∂B ω) ∂P) =
      ∫⁻ x : Configuration S.card, ∫⁻ y : Configuration S.card,
        (∏ i, f (S.orderEmbOfFin rfl i) (x i)) * momentKernel S.card θ τ x y *
          ∏ i, f' (S.orderEmbOfFin rfl i) (y i) := by
  have hcard : S.card ≤ 4 := (Finset.card_le_univ S).trans (by simpa using hn)
  have h := hB.lintegral_prod_eq_of_le_four hτ hcard
    (fun i => f (S.orderEmbOfFin rfl i)) (fun i => f' (S.orderEmbOfFin rfl i))
    (fun i => hf _) (fun i => hf' _)
  convert h using 1
  congr 1
  funext ω
  conv_lhs => rw [← S.map_orderEmbOfFin_univ rfl, Finset.prod_map]
  rfl

end Critical2DKPZ.SHF.Tsai

end
