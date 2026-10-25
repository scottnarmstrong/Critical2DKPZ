/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Topology.Algebra.Monoid

/-! # Cancellation of the fourth moment from common mixed moment limits

Inclusion-exclusion expands a fourth power of a difference into sixteen mixed
products. If all these product moments have the same limit, their signed sum
vanishes. Every expanded term is integrable before its expectation is used.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- The four-factor mixed scalar product, selecting the second scalar on the subset. -/
def fourthMixedProduct (S : Finset (Fin 4)) (a b : ℝ) : ℝ :=
  ∏ i : Fin 4, if i ∈ S then b else a

/-- Group the selected and unselected factors of the mixed product. -/
theorem fourthMixedProduct_eq (S : Finset (Fin 4)) (a b : ℝ) :
    fourthMixedProduct S a b = (∏ _i ∈ Finset.univ \ S, a) * ∏ _i ∈ S, b := by
  classical
  rw [fourthMixedProduct, Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_notMem_eq_sdiff]
  exact mul_comm _ _

/-- Inclusion-exclusion for a scalar fourth power of a difference. -/
theorem sub_pow_four_eq_sum_mixed (a b : ℝ) :
    (a - b) ^ 4 = ∑ S ∈ Finset.univ.powerset, (-1 : ℝ) ^ S.card * fourthMixedProduct S a b := by
  have h := Finset.prod_sub (fun _ : Fin 4 => a) (fun _ : Fin 4 => b) Finset.univ
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    fourthMixedProduct_eq, mul_assoc] using h

/-- The sixteen inclusion-exclusion coefficients add to zero. -/
theorem sum_fourthMixedProduct_coefficients :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset, (-1 : ℝ) ^ S.card) = 0 := by
  have h := (sub_pow_four_eq_sum_mixed 1 1).symm
  simpa only [sub_self, zero_pow (by norm_num : (4 : ℕ) ≠ 0), fourthMixedProduct,
    ite_self, Finset.prod_const_one, mul_one] using h

/-- Common integrable mixed fourth moments force the fourth moment of the difference to vanish. -/
theorem tendsto_integral_sub_pow_four_of_mixed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A B : ℕ → Ω → ℝ) (L : ℝ)
    (hI : ∀ S : Finset (Fin 4), ∀ j, Integrable (fun ω => fourthMixedProduct S (A j ω) (B j ω)) P)
    (hlim : ∀ S : Finset (Fin 4), Tendsto (fun j => ∫ ω, fourthMixedProduct S (A j ω) (B j ω) ∂P)
      atTop (𝓝 L)) :
    (∀ j, Integrable (fun ω => (A j ω - B j ω) ^ 4) P) ∧
      Tendsto (fun j => ∫ ω, (A j ω - B j ω) ^ 4 ∂P) atTop (𝓝 0) := by
  let U := (Finset.univ : Finset (Fin 4)).powerset
  have hterm (S : Finset (Fin 4)) (j) :
      Integrable (fun ω => (-1 : ℝ) ^ S.card * fourthMixedProduct S (A j ω) (B j ω)) P :=
    (hI S j).const_mul _
  have hfun (j) : (fun ω => (A j ω - B j ω) ^ 4) =
      fun ω => ∑ S ∈ U, (-1 : ℝ) ^ S.card * fourthMixedProduct S (A j ω) (B j ω) := by
    funext ω
    exact sub_pow_four_eq_sum_mixed _ _
  have hInt (j) : (∫ ω, (A j ω - B j ω) ^ 4 ∂P) =
      ∑ S ∈ U, (-1 : ℝ) ^ S.card * ∫ ω, fourthMixedProduct S (A j ω) (B j ω) ∂P := by
    rw [hfun j, integral_finsetSum _ (fun S _ => hterm S j)]
    simp only [integral_const_mul]
  refine ⟨fun j => ?_, ?_⟩
  · rw [hfun j]
    exact integrable_finsetSum _ (fun S _ => hterm S j)
  · have hsum := tendsto_finsetSum U (fun S _ => (hlim S).const_mul ((-1 : ℝ) ^ S.card))
    have hzero : (∑ S ∈ U, (-1 : ℝ) ^ S.card * L) = 0 := by
      rw [← Finset.sum_mul, show (∑ S ∈ U, (-1 : ℝ) ^ S.card) = 0 from sum_fourthMixedProduct_coefficients,
        zero_mul]
    rw [hzero] at hsum
    simpa only [hInt] using hsum

end Critical2DKPZ.SHF.Tsai

end
