/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredChainComparison
public import Critical2DKPZ.SHF.Tsai.BlockReplacementIndependence
public import Critical2DKPZ.SHF.Tsai.MollifierSubsequences

/-! # Exact centered fourth-moment equality under one block replacement

The extra independent block supplies the replacement family. Any connector
sample from an applicable mollifier can be placed at index zero of a shifted
applicable family. Common block moments then compare the actual integrable
centered fourth moments appearing in the swap estimate.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Replacing one independent block by another with the same delta-Bose moments preserves the heat-centered fourth moment. Both integrands are integrable by `integral_sum_centeredChainPairings_pow_four_eq_of_moments`. -/
theorem integral_sum_centeredChainPairings_pow_four_eq_of_swap {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (B' : Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k)) (hB' : HasDeltaBoseMoments θ (τ j) P B')
    (hind : iIndepFun (fun k : Fin (K + 2) => if (k : ℕ) ≤ K then B k else B') P)
    (u : ℕ → Plane → ℝ) (hu : ∀ k, ∃ w : ℕ → Plane → ℝ, IsL2ApplicableMollifier w ∧ ∃ ℓ, u k = w ℓ)
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ) (hg : ∀ a b, MemLp (g a b) 2)
    (hg' : ∀ a b, MemLp (g' a b) 2) :
    (∫ ω, ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂(chainProduct (fun k => B k ω) u K)) -
        ∑ b, ∫ p, g a b p.1 * g' a b p.2
          ∂(chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K)) ^ 4 ∂P =
      ∫ ω, ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2
          ∂(chainProduct (Function.update (fun k => B k ω) j (B' ω)) u K)) -
        ∑ b, ∫ p, g a b p.1 * g' a b p.2
          ∂(chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K)) ^ 4 ∂P) := by
  classical
  choose w hw q hq using hu
  let v (k ℓ : ℕ) := w k (ℓ + q k)
  have hv (k) : IsL2ApplicableMollifier (v k) :=
    (hw k).comp_tendsto (tendsto_add_atTop_nat (q k))
  have hvu : (fun k => v k 0) = u := by
    funext k
    simpa only [v, Nat.zero_add] using (hq k).symm
  let C (k : ℕ) (ω : Ω) := Function.update (fun k => B k ω) j (B' ω) k
  have hC (k) (hk : k ≤ K) : HasDeltaBoseMoments θ (τ k) P (C k) := by
    by_cases hkj : k = j
    · subst k
      simpa only [C, Function.update_self] using hB'
    · simpa only [C, Function.update_of_ne hkj] using hB k hk
  have hindB := iIndepFun_prefix_of_extra K B B' hind
  have hindC : iIndepFun (fun k : Fin (K + 1) => C k) P :=
    iIndepFun_update_of_extra K j hj B B' hind
  let X (a : Fin m) (ω : Ω) := ((∑ b, ∫ p, g a b p.1 * g' a b p.2
    ∂chainProduct (fun k => B k ω) u K) - ∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K) ^ 4
  let Y (a : Fin m) (ω : Ω) := ((∑ b, ∫ p, g a b p.1 * g' a b p.2
    ∂chainProduct (Function.update (fun k => B k ω) j (B' ω)) u K) -
      ∑ b, ∫ p, g a b p.1 * g' a b p.2
        ∂chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) u K) ^ 4
  have hdata (a : Fin m) : Integrable (X a) P ∧ Integrable (Y a) P ∧
      (∫ ω, X a ω ∂P) = ∫ ω, Y a ω ∂P := by
    have h := integral_sum_centeredChainPairings_pow_four_eq_of_moments
      K j hj τ hτ B C hB hC hindB hindC v hv 0 (g a) (g' a) (hg a) (hg' a)
    rw [hvu] at h
    simpa only [C, Function.update_idem, Finset.sum_sub_distrib, X, Y] using h
  change (∫ ω, ∑ a, X a ω ∂P) = ∫ ω, ∑ a, Y a ω ∂P
  rw [integral_finsetSum _ (fun a _ => (hdata a).1),
    integral_finsetSum _ (fun a _ => (hdata a).2.1)]
  exact Finset.sum_congr rfl (fun a _ => (hdata a).2.2)

end Critical2DKPZ.SHF.Tsai

end
