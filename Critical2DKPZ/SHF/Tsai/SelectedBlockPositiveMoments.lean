/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.PositiveChainBlockTests
public import Critical2DKPZ.SHF.Tsai.BlockTestMoments

/-! # Positive chain moments after conditioning on every other block

The other block measures are arbitrary fixed sigma-finite measures. Isolating
the selected random block turns every chain pairing into its positive endpoint
test. The full block moment measure then evaluates their product, without a
spatial L2 hypothesis on these conditional tests.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- With all other blocks fixed, products of positive chain pairings have the selected block moment measure. -/
theorem HasDeltaBoseMoments.lintegral_prod_chain_update_eq {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {B : Ω → Measure (Plane × Plane)}
    (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ)
    (μ : ℕ → Measure (Plane × Plane)) [∀ k, SigmaFinite (μ k)]
    (K : ℕ) (j : Fin (K + 1)) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → Plane → ℝ) (hw : ∀ i k, Measurable (w i k))
    (F : Fin n → Plane × Plane → ℝ≥0∞) (hF : ∀ i, Measurable (F i)) :
    (∫⁻ ω, ∏ i, (∫⁻ p, F i p ∂chainProduct (Function.update μ j (B ω)) (w i) K) ∂P) =
      ∫⁻ q : Configuration n × Configuration n, momentKernel n θ τ q.1 q.2 *
        ∏ i, positiveChainBlockTest K j μ (w i) (F i) (q.1 i, q.2 i) := by
  classical
  have htest (i) : Measurable (positiveChainBlockTest K j μ (w i) (F i)) :=
    measurable_positiveChainBlockTest_fixed μ K j (w i) (hw i) (F i) (hF i)
  have hpair (ω : Ω) (hω : IsLocallyFiniteMeasure (B ω)) (i : Fin n) :
      (∫⁻ p, F i p ∂chainProduct (Function.update μ j (B ω)) (w i) K) =
        ∫⁻ p, positiveChainBlockTest K j μ (w i) (F i) p ∂B ω := by
    let : IsLocallyFiniteMeasure (B ω) := hω
    have hsf (k : ℕ) : SigmaFinite (Function.update μ j (B ω) k) := by
      by_cases hk : k = (j : ℕ)
      · subst k
        rw [Function.update_self]
        infer_instance
      · rw [Function.update_of_ne hk]
        infer_instance
    let : ∀ k, SigmaFinite (Function.update μ j (B ω) k) := hsf
    rw [lintegral_chainProduct_eq_lintegral_blockTest _ (hw i) K j _ (hF i),
      positiveChainBlockTest_update, Function.update_self]
  calc
    _ = ∫⁻ ω, ∏ i, (∫⁻ p, positiveChainBlockTest K j μ (w i) (F i) p ∂B ω) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hB.2.1] with ω hω
      exact Finset.prod_congr rfl (fun i _ => hpair ω hω i)
    _ = _ := hB.lintegral_prod_tests_eq hτ hn1 hn
      (fun i => positiveChainBlockTest K j μ (w i) (F i)) htest

end Critical2DKPZ.SHF.Tsai

end
