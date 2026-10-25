/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.SignedMixedChainMoments
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Integrable inclusion-exclusion for heat-centered chain pairings

The signed mixed moments give integrability of every subset term. Finite
inclusion-exclusion can therefore pass through expectation, producing the
literal signed sum of partially heat-replaced chain kernel forms.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Inclusion-exclusion expressed directly by the retained-coordinate mixed products. -/
theorem prod_sub_eq_sum_prod_ite_compl {n : ℕ} (X Y : Fin n → ℝ) :
    (∏ i, (X i - Y i)) = ∑ S ∈ Finset.univ.powerset,
      (-1 : ℝ) ^ S.card * ∏ i, if i ∈ Sᶜ then X i else Y i := by
  classical
  have hprod (S : Finset (Fin n)) : (∏ i, if i ∈ Sᶜ then X i else Y i) =
      (∏ i ∈ Finset.univ \ S, X i) * ∏ i ∈ S, Y i := by
    rw [Finset.prod_ite]
    have h₁ : Finset.univ.filter (fun i : Fin n => i ∈ Sᶜ) = Finset.univ \ S := by
      ext i
      simp
    have h₂ : Finset.univ.filter (fun i : Fin n => i ∉ Sᶜ) = S := by
      ext i
      simp
    rw [h₁, h₂]
  simp_rw [hprod]
  simpa only [mul_assoc] using Finset.prod_sub X Y Finset.univ

/-- Heat-centered chain products are integrable and equal the finite signed sum of their mixed kernel forms. The kernel densities are interpreted using `ENNReal.toReal`. -/
theorem integral_prod_centeredChainPairings_eq {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ)
    (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ)
    (g g' : Fin n → Plane → ℝ) (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    Integrable (fun ω => ∏ i, ((∫ p, g i p.1 * g' i p.2
      ∂chainProduct (fun k => B k ω) (fun k => w i k ℓ) K) -
        ∫ p, g i p.1 * g' i p.2 ∂chainProduct
          (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w i k ℓ) K)) P ∧
    (∫ ω, ∏ i, ((∫ p, g i p.1 * g' i p.2 ∂chainProduct (fun k => B k ω) (fun k => w i k ℓ) K) -
      ∫ p, g i p.1 * g' i p.2 ∂chainProduct
        (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w i k ℓ) K) ∂P) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ S.card *
        ∫ x, ∫ y, (∏ i, g i (x i)) *
          (chainKernel n (Function.update (fun k => momentKernel n θ (τ k)) j
            (mixedBlockKernel n θ (τ j) Sᶜ)) (fun i k => w i k ℓ) K x y).toReal *
              ∏ i, g' i (y i) := by
  classical
  let X (i : Fin n) (ω : Ω) := ∫ p, g i p.1 * g' i p.2
    ∂chainProduct (fun k => B k ω) (fun k => w i k ℓ) K
  let Y (i : Fin n) (ω : Ω) := ∫ p, g i p.1 * g' i p.2
    ∂chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w i k ℓ) K
  let A (S : Finset (Fin n)) (ω : Ω) := ∏ i, if i ∈ Sᶜ then X i ω else Y i ω
  have hpoint (S : Finset (Fin n)) (ω : Ω) : A S ω =
      ∏ i, ∫ p, g i p.1 * g' i p.2 ∂chainProduct
        (if i ∈ Sᶜ then (fun k => B k ω) else
          Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w i k ℓ) K := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ Sᶜ
    · simp only [ite_eq_left hi, X]
    · simp only [ite_eq_right hi, Y]
  have hI (S : Finset (Fin n)) : Integrable (A S) P := by
    have h := (integral_prod_chainProduct_update_heat_eq K j hj τ hτ B hB hind hn1 hn Sᶜ
      w hw ℓ g g' hg hg').2.1
    exact h.congr (Filter.Eventually.of_forall fun ω => (hpoint S ω).symm)
  have hterm (S : Finset (Fin n)) : Integrable (fun ω => (-1 : ℝ) ^ S.card * A S ω) P :=
    (hI S).const_mul _
  have heq : (fun ω => ∏ i, (X i ω - Y i ω)) =
      fun ω => ∑ S ∈ Finset.univ.powerset, (-1 : ℝ) ^ S.card * A S ω := by
    funext ω
    exact prod_sub_eq_sum_prod_ite_compl (X · ω) (Y · ω)
  have houter : Integrable (fun ω => ∏ i, (X i ω - Y i ω)) P := by
    rw [heq]
    exact integrable_finsetSum _ (fun S _ => hterm S)
  refine ⟨houter, ?_⟩
  change (∫ ω, ∏ i, (X i ω - Y i ω) ∂P) = _
  rw [heq, integral_finsetSum _ (fun S _ => hterm S)]
  apply Finset.sum_congr rfl
  intro S _
  rw [integral_const_mul]
  congr 1
  rw [integral_congr_ae (Filter.Eventually.of_forall (hpoint S))]
  exact (integral_prod_chainProduct_update_heat_eq K j hj τ hτ B hB hind hn1 hn Sᶜ
    w hw ℓ g g' hg hg').2.2

end Critical2DKPZ.SHF.Tsai

end
