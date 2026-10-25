/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConditionalChainComparison
public import Critical2DKPZ.SHF.Tsai.ProductMomentComparison
import Critical2DKPZ.SHF.Tsai.SubsetProductIntegrals

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

/-- Conditional centered products match through order four for every common outer-dependent centering. -/
theorem ae_integral_prod_centered_chain_update_eq_of_replacement {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (j : Fin (K + 1))
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hlf : ∀ k ≤ K, ∀ ω, IsLocallyFiniteMeasure (B k ω))
    (B' : Ω → Measure (Plane × Plane)) (hB' : HasDeltaBoseMoments θ (τ j) P B')
    (hlf' : ∀ ω, IsLocallyFiniteMeasure (B' ω))
    {n : ℕ} (hn : n ≤ 4)
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ)
    (g g' : Fin n → Plane → ℝ) (hgm : ∀ i, Measurable (g i)) (hg'm : ∀ i, Measurable (g' i))
    (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) (c : Fin n → (Fin K → Ω) → ℝ) :
    ∀ᵐ a : Fin K → Ω ∂Measure.pi (fun _ : Fin K => P),
      Integrable (fun ω => ∏ i, ((∫ p, g i p.1 * g' i p.2
        ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B j ω))
          (fun k => w i k ℓ) K) - c i a)) P ∧
      Integrable (fun ω => ∏ i, ((∫ p, g i p.1 * g' i p.2
        ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B' ω))
          (fun k => w i k ℓ) K) - c i a)) P ∧
      (∫ ω, ∏ i, ((∫ p, g i p.1 * g' i p.2
        ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B j ω))
          (fun k => w i k ℓ) K) - c i a) ∂P) =
        ∫ ω, ∏ i, ((∫ p, g i p.1 * g' i p.2
          ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B' ω))
            (fun k => w i k ℓ) K) - c i a) ∂P := by
  classical
  let X (a : Fin K → Ω) (i : Fin n) (ω : Ω) := ∫ p, g i p.1 * g' i p.2
    ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B j ω)) (fun k => w i k ℓ) K
  let Y (a : Fin K → Ω) (i : Fin n) (ω : Ω) := ∫ p, g i p.1 * g' i p.2
    ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B' ω)) (fun k => w i k ℓ) K
  have hS (S : Finset (Fin n)) :
      ∀ᵐ a : Fin K → Ω ∂Measure.pi (fun _ : Fin K => P),
        Integrable (fun ω => ∏ i ∈ S, X a i ω) P ∧
        Integrable (fun ω => ∏ i ∈ S, Y a i ω) P ∧
        (∫ ω, ∏ i ∈ S, X a i ω ∂P) = ∫ ω, ∏ i ∈ S, Y a i ω ∂P := by
    by_cases hzero : S.card = 0
    · have hEmpty : S = ∅ := Finset.card_eq_zero.mp hzero
      subst S
      simp only [Finset.prod_empty]
      exact Filter.Eventually.of_forall (fun _ => ⟨integrable_const 1, integrable_const 1, trivial⟩)
    · have hcard : S.card ≤ 4 := (Finset.card_le_univ S).trans (by simpa using hn)
      have h := ae_integral_prod_chain_update_eq_of_replacement P K j τ hτ B hB hlf B' hB' hlf'
        (Nat.one_le_iff_ne_zero.mpr hzero) hcard
        (fun i => w (S.orderEmbOfFin rfl i)) (fun i k => hw _ k) ℓ
        (fun i => g (S.orderEmbOfFin rfl i)) (fun i => g' (S.orderEmbOfFin rfl i))
        (fun i => hgm _) (fun i => hg'm _) (fun i => hg _) (fun i => hg' _)
      simpa only [← prod_orderEmbOfFin S, X, Y] using h
  filter_upwards [ae_all_iff.2 hS] with a ha
  exact integral_prod_sub_const_eq_of_subset_moments P P (X a) (Y a)
    (fun S => (ha S).1) (fun S => (ha S).2.1) (fun S => (ha S).2.2) (fun i => c i a)

end Critical2DKPZ.SHF.Tsai

end
