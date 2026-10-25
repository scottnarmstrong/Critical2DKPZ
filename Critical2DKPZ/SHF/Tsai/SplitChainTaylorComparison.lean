/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConditionalTensorMoments
public import Critical2DKPZ.SHF.Tsai.SplitChainFourthMoments
public import Critical2DKPZ.SHF.Tsai.OuterChainMeasurability
public import Critical2DKPZ.SHF.Tsai.ConditionalTaylorComparison

/-! # Conditional Taylor bounds for chain replacement

Matching conditional centered cubic moments bound the difference of nonlinear chain
expectations by their fourth moments about the heat-replaced chain. Both nonlinear
observables are integrable.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Replacing one block on the split product probability space gives an integrable nonlinear observable and a fourth-moment error bound. Integrability of the fourth-moment terms is given by `integrable_sum_centered_splitChain_pow_four` and `integrable_sum_centered_splitChain_swap_pow_four`. -/
theorem abs_integral_splitChain_swap_le {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (j : Fin (K + 1))
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hlf : ∀ k ≤ K, ∀ ω, IsLocallyFiniteMeasure (B k ω))
    (B' : Ω → Measure (Plane × Plane)) (hB' : HasDeltaBoseMoments θ (τ j) P B')
    (hlf' : ∀ ω, IsLocallyFiniteMeasure (B' ω))
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ)
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ)
    (hgm : ∀ a b, Measurable (g a b)) (hg'm : ∀ a b, Measurable (g' a b))
    (hg : ∀ a b, MemLp (g a b) 2) (hg' : ∀ a b, MemLp (g' a b) 2)
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hH0 : ∀ z, ‖H z‖ ≤ CH) (hCH : ∀ z, ‖iteratedFDeriv ℝ 4 H z‖ ≤ CH) :
    let Q := (Measure.pi (fun _ : Fin K => P)).prod P
    let A (a : Fin K → Ω) (i : Fin m) := ∑ b, ∫ p, g i b p.1 * g' i b p.2
      ∂chainProduct (Function.update (outerCopyBlock K j B a) j (heatBlock (τ j))) (fun k => w k ℓ) K
    let F (q : (Fin K → Ω) × Ω) (i : Fin m) := ∑ b, ∫ p, g i b p.1 * g' i b p.2
      ∂chainProduct (Function.update (outerCopyBlock K j B q.1) j (B j q.2)) (fun k => w k ℓ) K
    let G (q : (Fin K → Ω) × Ω) (i : Fin m) := ∑ b, ∫ p, g i b p.1 * g' i b p.2
      ∂chainProduct (Function.update (outerCopyBlock K j B q.1) j (B' q.2)) (fun k => w k ℓ) K
    Integrable (fun q => H (F q)) Q ∧ Integrable (fun q => H (G q)) Q ∧
      |(∫ q, H (F q) ∂Q) - ∫ q, H (G q) ∂Q| ≤
        CH / 24 * ((∫ q, ∑ i, (F q i - A q.1 i) ^ 4 ∂Q) +
          ∫ q, ∑ i, (G q i - A q.1 i) ^ 4 ∂Q) := by
  classical
  dsimp only
  let Q := Measure.pi (fun _ : Fin K => P)
  let T (i : Fin m) (b : Fin r) (p : Plane × Plane) := g i b p.1 * g' i b p.2
  let A (a : Fin K → Ω) (i : Fin m) := ∑ b, ∫ p, T i b p
    ∂chainProduct (Function.update (outerCopyBlock K j B a) j (heatBlock (τ j))) (fun k => w k ℓ) K
  let F (q : (Fin K → Ω) × Ω) (i : Fin m) := ∑ b, ∫ p, T i b p
    ∂chainProduct (Function.update (outerCopyBlock K j B q.1) j (B j q.2)) (fun k => w k ℓ) K
  let G (q : (Fin K → Ω) × Ω) (i : Fin m) := ∑ b, ∫ p, T i b p
    ∂chainProduct (Function.update (outerCopyBlock K j B q.1) j (B' q.2)) (fun k => w k ℓ) K
  have hTm (i b) : Measurable (T i b) :=
    ((hgm i b).comp measurable_fst).mul ((hg'm i b).comp measurable_snd)
  have hwm (k) : Measurable (w k ℓ) := ((hw k).2.1 ℓ).measurable
  have hBm (k) (hk : k ≤ K) : Measurable (B k) := (hB k hk).1
  have hAm : Measurable A := by
    apply Measurable.of_eval
    intro i
    exact Finset.measurable_sum _ fun b _ => measurable_integral_outerCopyChain_update
      K j B hBm hlf id measurable_id (fun _ => heatBlock (τ j)) measurable_const
      (fun _ => locallyFinite_heatBlock _) _ hwm _ (hTm i b)
  have hFm : Measurable F := by
    apply Measurable.of_eval
    intro i
    exact Finset.measurable_sum _ fun b _ => measurable_integral_outerCopyChain_update
      K j B hBm hlf Prod.fst measurable_fst (fun q => B j q.2)
      ((hBm j (Nat.le_of_lt_succ j.is_lt)).comp measurable_snd)
      (fun q => hlf j (Nat.le_of_lt_succ j.is_lt) q.2) _ hwm _ (hTm i b)
  have hGm : Measurable G := by
    apply Measurable.of_eval
    intro i
    exact Finset.measurable_sum _ fun b _ => measurable_integral_outerCopyChain_update
      K j B hBm hlf Prod.fst measurable_fst (fun q => B' q.2) (hB'.1.comp measurable_snd)
      (fun q => hlf' q.2) _ hwm _ (hTm i b)
  let X (q : (Fin K → Ω) × Ω) := F q - A q.1
  let Y (q : (Fin K → Ω) × Ω) := G q - A q.1
  have hFourth := integrable_sum_centered_splitChain_swap_pow_four P K j τ hτ B hB B' hB'
    w hw ℓ g g' hg hg'
  have hX4 : Integrable (fun q => ∑ i, X q i ^ 4) (Q.prod P) := by
    simpa only [X, F, A, T, Pi.sub_apply] using hFourth.1
  have hY4 : Integrable (fun q => ∑ i, Y q i ^ 4) (Q.prod P) := by
    simpa only [Y, G, A, T, Pi.sub_apply] using hFourth.2
  have hmatch : ∀ᵐ a ∂Q, ∀ k ≤ 3, ∀ q : Fin k → Fin m,
      Integrable (fun ω => ∏ i, X (a, ω) (q i)) P ∧
      Integrable (fun ω => ∏ i, Y (a, ω) (q i)) P ∧
      (∫ ω, ∏ i, X (a, ω) (q i) ∂P) = ∫ ω, ∏ i, Y (a, ω) (q i) ∂P := by
    apply ae_all_iff.2
    intro k
    apply ae_all_iff.2
    intro hk
    apply ae_all_iff.2
    intro q
    have h := ae_integral_prod_sum_centered_chain_update_eq_of_replacement
      P K j τ hτ B hB hlf B' hB' hlf' (hk.trans (by norm_num : 3 ≤ 4)) w hw ℓ
      (fun i => g (q i)) (fun i => g' (q i)) (fun i => hgm _) (fun i => hg'm _)
      (fun i => hg _) (fun i => hg' _)
      (fun i b a => ∫ p, T (q i) b p ∂chainProduct
        (Function.update (outerCopyBlock K j B a) j (heatBlock (τ j))) (fun k => w k ℓ) K)
    simpa only [X, Y, F, G, A, T, Pi.sub_apply, Finset.sum_sub_distrib] using h
  have h := abs_integral_conditional_add_sub_le P Q A hAm.aestronglyMeasurable X Y
    (hFm.sub (hAm.comp measurable_fst)).aestronglyMeasurable
    (hGm.sub (hAm.comp measurable_fst)).aestronglyMeasurable
    hX4 hY4 hmatch H hH CH hH0 hCH
  have hAX (q) : A q.1 + X q = F q := add_sub_cancel _ _
  have hAY (q) : A q.1 + Y q = G q := add_sub_cancel _ _
  simpa only [hAX, hAY, X, Y, F, G, A, T, Q, Pi.sub_apply] using h

end Critical2DKPZ.SHF.Tsai

end
