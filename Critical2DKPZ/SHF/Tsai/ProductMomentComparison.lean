/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Centering and summing matching product moments

Finite inclusion-exclusion preserves integrability and equality of moments
under deterministic centering. The product-of-sums expansion then transfers
mixed moments to finite tensor sums.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Matching integrable subset moments remain matching after any common centering. -/
theorem integral_prod_sub_const_eq_of_subset_moments {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι]
    (P : Measure Ω) (P' : Measure Ω') (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ)
    (hX : ∀ S : Finset ι, Integrable (fun ω => ∏ i ∈ S, X i ω) P)
    (hY : ∀ S : Finset ι, Integrable (fun ω => ∏ i ∈ S, Y i ω) P')
    (hEq : ∀ S : Finset ι,
      (∫ ω, ∏ i ∈ S, X i ω ∂P) = ∫ ω, ∏ i ∈ S, Y i ω ∂P') (c : ι → ℝ) :
    Integrable (fun ω => ∏ i, (X i ω - c i)) P ∧
      Integrable (fun ω => ∏ i, (Y i ω - c i)) P' ∧
      (∫ ω, ∏ i, (X i ω - c i) ∂P) = ∫ ω, ∏ i, (Y i ω - c i) ∂P' := by
  classical
  have hExpand (Z : ι → ℝ) : (∏ i, (Z i - c i)) =
      ∑ S ∈ Finset.univ.powerset, (-1 : ℝ) ^ S.card *
        (∏ i ∈ Finset.univ \ S, Z i) * ∏ i ∈ S, c i := Finset.prod_sub _ _ _
  simp_rw [hExpand]
  have hXI (S : Finset ι) : Integrable (fun ω => (-1 : ℝ) ^ S.card *
      (∏ i ∈ Finset.univ \ S, X i ω) * ∏ i ∈ S, c i) P :=
    ((hX _).const_mul _).mul_const _
  have hYI (S : Finset ι) : Integrable (fun ω => (-1 : ℝ) ^ S.card *
      (∏ i ∈ Finset.univ \ S, Y i ω) * ∏ i ∈ S, c i) P' :=
    ((hY _).const_mul _).mul_const _
  refine ⟨integrable_finsetSum _ (fun S _ => hXI S),
    integrable_finsetSum _ (fun S _ => hYI S), ?_⟩
  rw [integral_finsetSum _ (fun S _ => hXI S), integral_finsetSum _ (fun S _ => hYI S)]
  apply Finset.sum_congr rfl
  intro S _
  rw [integral_mul_const, integral_const_mul, integral_mul_const, integral_const_mul, hEq]

/-- Matching mixed products determine mixed products of finite sums, including integrability. -/
theorem integral_prod_sum_eq_of_mixed_moments {Ω Ω' ι κ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι] [Fintype κ]
    (P : Measure Ω) (P' : Measure Ω') (X : ι → κ → Ω → ℝ) (Y : ι → κ → Ω' → ℝ)
    (hX : ∀ q : ι → κ, Integrable (fun ω => ∏ i, X i (q i) ω) P)
    (hY : ∀ q : ι → κ, Integrable (fun ω => ∏ i, Y i (q i) ω) P')
    (hEq : ∀ q : ι → κ,
      (∫ ω, ∏ i, X i (q i) ω ∂P) = ∫ ω, ∏ i, Y i (q i) ω ∂P') :
    Integrable (fun ω => ∏ i, ∑ b, X i b ω) P ∧
      Integrable (fun ω => ∏ i, ∑ b, Y i b ω) P' ∧
      (∫ ω, ∏ i, ∑ b, X i b ω ∂P) = ∫ ω, ∏ i, ∑ b, Y i b ω ∂P' := by
  classical
  have hExpand (Z : ι → κ → ℝ) : (∏ i, ∑ b, Z i b) = ∑ q : ι → κ, ∏ i, Z i (q i) :=
    Fintype.prod_sum Z
  simp_rw [hExpand]
  refine ⟨integrable_finsetSum _ (fun q _ => hX q),
    integrable_finsetSum _ (fun q _ => hY q), ?_⟩
  rw [integral_finsetSum _ (fun q _ => hX q), integral_finsetSum _ (fun q _ => hY q)]
  exact Finset.sum_congr rfl (fun q _ => hEq q)

end Critical2DKPZ.SHF.Tsai

end
