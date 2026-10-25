/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConditionalCenteredChainComparison

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

/-- Conditional mixed moments of finite tensor sums agree after common centering. -/
theorem ae_integral_prod_sum_centered_chain_update_eq_of_replacement {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (j : Fin (K + 1))
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hlf : ∀ k ≤ K, ∀ ω, IsLocallyFiniteMeasure (B k ω))
    (B' : Ω → Measure (Plane × Plane)) (hB' : HasDeltaBoseMoments θ (τ j) P B')
    (hlf' : ∀ ω, IsLocallyFiniteMeasure (B' ω))
    {n r : ℕ} (hn : n ≤ 4)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ)
    (g g' : Fin n → Fin r → Plane → ℝ) (hgm : ∀ i b, Measurable (g i b)) (hg'm : ∀ i b, Measurable (g' i b))
    (hg : ∀ i b, MemLp (g i b) 2) (hg' : ∀ i b, MemLp (g' i b) 2) (c : Fin n → Fin r → (Fin K → Ω) → ℝ) :
    ∀ᵐ a : Fin K → Ω ∂Measure.pi (fun _ : Fin K => P),
      Integrable (fun ω => ∏ i, ∑ b, ((∫ p, g i b p.1 * g' i b p.2
        ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B j ω))
          (fun k => w k ℓ) K) - c i b a)) P ∧
      Integrable (fun ω => ∏ i, ∑ b, ((∫ p, g i b p.1 * g' i b p.2
        ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B' ω))
          (fun k => w k ℓ) K) - c i b a)) P ∧
      (∫ ω, ∏ i, ∑ b, ((∫ p, g i b p.1 * g' i b p.2
        ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B j ω))
          (fun k => w k ℓ) K) - c i b a) ∂P) =
        ∫ ω, ∏ i, ∑ b, ((∫ p, g i b p.1 * g' i b p.2
          ∂chainProduct (Function.update (outerCopyBlock K j B a) j (B' ω))
            (fun k => w k ℓ) K) - c i b a) ∂P := by
  classical
  have hq (q : Fin n → Fin r) := ae_integral_prod_centered_chain_update_eq_of_replacement
    P K j τ hτ B hB hlf B' hB' hlf' hn (fun _ => w) (fun _ k => hw k) ℓ
    (fun i => g i (q i)) (fun i => g' i (q i))
    (fun i => hgm _ _) (fun i => hg'm _ _) (fun i => hg _ _) (fun i => hg' _ _)
    (fun i => c i (q i))
  filter_upwards [ae_all_iff.2 hq] with a ha
  exact integral_prod_sum_eq_of_mixed_moments P P _ _
    (fun q => (ha q).1) (fun q => (ha q).2.1) (fun q => (ha q).2.2)

end Critical2DKPZ.SHF.Tsai

end
