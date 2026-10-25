/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredChainMoments
public import Critical2DKPZ.SHF.Tsai.FourthMomentComparison

/-! # Equality of centered fourth chain moments from common block moments

The subset expansion expresses every centered mixed moment through the same
kernels on both probability spaces. The finite multinomial expansion then
compares fourth moments of finite tensor sums, with both integrability clauses.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Common independent block moments determine the integrable centered fourth moment of a finite tensor sum. -/
theorem integral_sum_centeredChainPairings_pow_four_eq_of_moments
    {θ : ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (C : ℕ → Ω' → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hC : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P' (C k))
    (hindB : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (hindC : iIndepFun (fun k : Fin (K + 1) => C k) P')
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ)
    {r : ℕ} (g g' : Fin r → Plane → ℝ) (hg : ∀ b, MemLp (g b) 2) (hg' : ∀ b, MemLp (g' b) 2) :
    Integrable (fun ω => (∑ b, ((∫ p, g b p.1 * g' b p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
        ∫ p, g b p.1 * g' b p.2 ∂chainProduct
          (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K)) ^ 4) P ∧
    Integrable (fun ω => (∑ b, ((∫ p, g b p.1 * g' b p.2
      ∂chainProduct (fun k => C k ω) (fun k => w k ℓ) K) -
        ∫ p, g b p.1 * g' b p.2 ∂chainProduct
          (Function.update (fun k => C k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K)) ^ 4) P' ∧
    (∫ ω, (∑ b, ((∫ p, g b p.1 * g' b p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
      ∫ p, g b p.1 * g' b p.2 ∂chainProduct
        (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K)) ^ 4 ∂P) =
      ∫ ω, (∑ b, ((∫ p, g b p.1 * g' b p.2 ∂chainProduct (fun k => C k ω) (fun k => w k ℓ) K) -
        ∫ p, g b p.1 * g' b p.2 ∂chainProduct
          (Function.update (fun k => C k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K)) ^ 4 ∂P' := by
  let X (b : Fin r) (ω : Ω) := (∫ p, g b p.1 * g' b p.2
    ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) -
      ∫ p, g b p.1 * g' b p.2 ∂chainProduct
        (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K
  let Y (b : Fin r) (ω : Ω') := (∫ p, g b p.1 * g' b p.2
    ∂chainProduct (fun k => C k ω) (fun k => w k ℓ) K) -
      ∫ p, g b p.1 * g' b p.2 ∂chainProduct
        (Function.update (fun k => C k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K
  have hBM (q : Fin 4 → Fin r) := integral_prod_centeredChainPairings_eq K j hj τ hτ B hB hindB
    (n := 4) (by norm_num) (by norm_num) (fun _ => w) (fun _ => hw) ℓ
    (fun i => g (q i)) (fun i => g' (q i)) (fun i => hg _) (fun i => hg' _)
  have hCM (q : Fin 4 → Fin r) := integral_prod_centeredChainPairings_eq K j hj τ hτ C hC hindC
    (n := 4) (by norm_num) (by norm_num) (fun _ => w) (fun _ => hw) ℓ
    (fun i => g (q i)) (fun i => g' (q i)) (fun i => hg _) (fun i => hg' _)
  exact integral_sum_pow_four_eq_of_mixed_moments P P' X Y
    (fun q => (hBM q).1) (fun q => (hCM q).1)
    (fun q => (hBM q).2.trans (hCM q).2.symm)

end Critical2DKPZ.SHF.Tsai

end
