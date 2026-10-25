/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredChainComparison
public import Critical2DKPZ.SHF.Tsai.SignedChainMoments

/-! # Integrability of nonlinear chain observables

Bounded continuous functions of finite sums of chain pairings are integrable for `L²`
endpoint representatives. The corresponding finite sum of centered fourth powers is integrable.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- A bounded continuous function of finite tensor chain pairings is integrable. -/
theorem integrable_comp_chainPairings {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ)
    (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ)
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ)
    (hg : ∀ a b, MemLp (g a b) 2) (hg' : ∀ a b, MemLp (g' a b) 2)
    (H : (Fin m → ℝ) → ℝ) (hH : Continuous H) (C : ℝ) (hC : ∀ z, ‖H z‖ ≤ C) :
    Integrable (fun ω => H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K)) P := by
  have hI (a : Fin m) : Integrable (fun ω => ∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) P := by
    apply integrable_finsetSum
    intro b _
    have h := (integral_prod_chainProduct_eq K τ hτ B hB hind
      (n := 1) (by norm_num) (by norm_num) (fun _ => w) (fun _ => hw) ℓ
      (fun _ => g a b) (fun _ => g' a b) (fun _ => hg a b) (fun _ => hg' a b)).2.1
    simpa only [Fin.prod_univ_one] using h
  have hm : AEMeasurable (fun ω a => ∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) P :=
    AEMeasurable.of_eval (fun a => (hI a).aemeasurable)
  exact Integrable.of_bound (hH.comp_aestronglyMeasurable hm.aestronglyMeasurable) C
    (Filter.Eventually.of_forall (fun ω => hC _))

/-- The actual sum of centered fourth moments is integrable. -/
theorem integrable_sum_centeredChainPairings_pow_four {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ)
    (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ)
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ)
    (hg : ∀ a b, MemLp (g a b) 2) (hg' : ∀ a b, MemLp (g' a b) 2) :
    Integrable (fun ω => ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
      ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K) ^ 4) P := by
  apply integrable_finsetSum
  intro a _
  have h := (integral_sum_centeredChainPairings_pow_four_eq_of_moments
    K j hj τ hτ B B hB hB hind hind w hw ℓ (g a) (g' a) (hg a) (hg' a)).1
  simpa only [Finset.sum_sub_distrib] using h

end Critical2DKPZ.SHF.Tsai

end
