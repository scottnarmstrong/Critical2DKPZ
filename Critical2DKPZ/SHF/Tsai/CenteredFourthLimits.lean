/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredChainMomentLimits
import Critical2DKPZ.SHF.Tsai.FourthMomentSumLimits
import Critical2DKPZ.SHF.Tsai.HeatMollifier

/-! # Common centered fourth-moment limits of finite tensor sums

Expand the fourth power into finitely many fourfold products. Their signed
kernel limits are independent of the connector family, so the actual
nonnegative fourth-moment sum has one finite common limit.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Centered fourth moments of finite tensor sums have a common finite nonnegative limit for every applicable connector family. -/
theorem exists_integral_sum_centeredChainPairings_four_limit {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    {m r : ℕ} (g g' : Fin m → Fin r → Plane → ℝ)
    (hg : ∀ a b, MemLp (g a b) 2) (hg' : ∀ a b, MemLp (g' a b) 2) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ w : ℕ → ℕ → Plane → ℝ,
      (∀ k, IsL2ApplicableMollifier (w k)) →
      (∀ ℓ, Integrable (fun ω => ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2
        ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
        ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
          (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K) ^ 4) P) ∧
      Tendsto (fun ℓ => ∫ ω, ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2
        ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
        ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
          (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K) ^ 4 ∂P)
        atTop (𝓝 L) := by
  classical
  let X (w : ℕ → ℕ → Plane → ℝ) (ℓ : ℕ) (a : Fin m) (b : Fin r) (ω : Ω) :=
    (∫ p, g a b p.1 * g' a b p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
      ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K
  have hExists (a : Fin m) (q : Fin 4 → Fin r) : ∃ L : ℝ,
      ∀ w : ℕ → ℕ → Plane → ℝ, (∀ k, IsL2ApplicableMollifier (w k)) →
        Tendsto (fun ℓ => ∫ ω, ∏ i, X w ℓ a (q i) ω ∂P) atTop (𝓝 L) := by
    refine ⟨∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset, (-1 : ℝ) ^ S.card *
      ∫ x, ∫ y, (∏ i, g a (q i) (x i)) *
        (chainKernelLimit 4 (Function.update (fun k => momentKernel 4 θ (τ k)) j
          (mixedBlockKernel 4 θ (τ j) Sᶜ)) K x y).toReal * ∏ i, g' a (q i) (y i),
      fun w hw => ?_⟩
    exact tendsto_integral_prod_centeredChainPairings K j hj τ hτ B hB hind
      (n := 4) (by norm_num) (by norm_num) (fun _ => w) (fun _ => hw)
      (fun i => g a (q i)) (fun i => g' a (q i)) (fun i => hg _ _) (fun i => hg' _ _)
  choose L hL using hExists
  have hData (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) :
      (∀ ℓ, Integrable (fun ω => ∑ a, (∑ b, X w ℓ a b ω) ^ 4) P) ∧
      Tendsto (fun ℓ => ∫ ω, ∑ a, (∑ b, X w ℓ a b ω) ^ 4 ∂P) atTop (𝓝 (∑ a, ∑ q, L a q)) := by
    have hI (ℓ : ℕ) (a : Fin m) (q : Fin 4 → Fin r) : Integrable (fun ω => ∏ i, X w ℓ a (q i) ω) P :=
      (integral_prod_centeredChainPairings_eq K j hj τ hτ B hB hind
        (n := 4) (by norm_num) (by norm_num) (fun _ => w) (fun _ => hw) ℓ
        (fun i => g a (q i)) (fun i => g' a (q i)) (fun i => hg _ _) (fun i => hg' _ _)).1
    exact tendsto_integral_sum_sum_pow_four_of_mixed_limits P (fun ℓ => X w ℓ) L hI
      (fun a q => hL a q w hw)
  have hNonneg : 0 ≤ ∑ a, ∑ q, L a q :=
    ge_of_tendsto (hData (fun _ => heatMollifier) (fun _ => isL2ApplicableMollifier_heatMollifier)).2
      (Eventually.of_forall (fun ℓ => integral_nonneg (fun ω =>
        Finset.sum_nonneg (fun a _ => (show Even 4 from ⟨2, rfl⟩).pow_nonneg _))))
  refine ⟨_, hNonneg, fun w hw => ?_⟩
  simpa only [X, Finset.sum_sub_distrib] using hData w hw

end Critical2DKPZ.SHF.Tsai

end
