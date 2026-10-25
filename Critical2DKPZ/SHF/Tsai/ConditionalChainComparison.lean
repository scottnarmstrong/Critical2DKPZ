/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConditionalChainMoments

/-! # Matching conditional chain moments under block replacement

The replaced family retains the prescribed block moments. Its outer-copy
family is identical to the original one, so the conditional endpoint tests
and moment kernels coincide. Thus both actual conditional products are
integrable and have equal expectations.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Replacing the selected block by one with the same moment data preserves every conditional product through order four. -/
theorem ae_integral_prod_chain_update_eq_of_replacement {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (j : Fin (K + 1))
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hlf : ∀ k ≤ K, ∀ ω, IsLocallyFiniteMeasure (B k ω))
    (B' : Ω → Measure (Plane × Plane)) (hB' : HasDeltaBoseMoments θ (τ j) P B')
    (hlf' : ∀ ω, IsLocallyFiniteMeasure (B' ω))
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ)
    (g g' : Fin n → Plane → ℝ) (hgm : ∀ i, Measurable (g i)) (hg'm : ∀ i, Measurable (g' i))
    (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    ∀ᵐ a : Fin K → Ω ∂Measure.pi (fun _ : Fin K => P),
      Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2
        ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B j ω)) (fun k => w i k ℓ) K) P ∧
      Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2
        ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B' ω)) (fun k => w i k ℓ) K) P ∧
      (∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2
        ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B j ω)) (fun k => w i k ℓ) K) ∂P) =
        ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2
          ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B' ω)) (fun k => w i k ℓ) K) ∂P := by
  classical
  let D := Function.update B j B'
  have hDj : D j = B' := Function.update_self _ _ _
  have hD (k) (hk : k ≤ K) : HasDeltaBoseMoments θ (τ k) P (D k) := by
    by_cases hkj : k = (j : ℕ)
    · subst k
      simpa only [hDj] using hB'
    · simpa only [D, Function.update_of_ne hkj] using hB k hk
  have hDlf (k) (hk : k ≤ K) (ω : Ω) : IsLocallyFiniteMeasure (D k ω) := by
    by_cases hkj : k = (j : ℕ)
    · subst k
      simpa only [hDj] using hlf' ω
    · simpa only [D, Function.update_of_ne hkj] using hlf k hk ω
  have hOuter : outerCopyBlock K j D = outerCopyBlock K j B := outerCopyBlock_update K j B B'
  have hOriginal := ae_integral_prod_chain_update_eq P K j τ hτ B hB hlf hn1 hn w hw ℓ
    g g' hgm hg'm hg hg'
  have hReplacement := ae_integral_prod_chain_update_eq P K j τ hτ D hD hDlf hn1 hn w hw ℓ
    g g' hgm hg'm hg hg'
  simp only [hOuter, hDj] at hReplacement
  filter_upwards [hOriginal, hReplacement] with a ha ha'
  exact ⟨ha.1, ha'.1, ha.2.trans ha'.2.symm⟩

end Critical2DKPZ.SHF.Tsai

end
