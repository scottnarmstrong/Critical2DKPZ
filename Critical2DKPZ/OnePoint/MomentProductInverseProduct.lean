/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.MomentProductInverseDefect
public import Critical2DKPZ.OnePoint.BlockRatioInverseExpectation
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # Product lower bounds for independent block reciprocals -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

private theorem inv_rpow_three_halves_interval_le (m M : ℕ) (hm : 1 ≤ m)
    (hmM : m ≤ M) :
    ∑ j ∈ Finset.Icc m M, 1 / (j : ℝ) ^ ((3 : ℝ) / 2) ≤ 3 / Real.sqrt m := by
  let f : ℝ → ℝ := fun x => x ^ (-((3 : ℝ) / 2))
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hmone : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hanti : AntitoneOn f (Set.Ici (m : ℝ)) := by
    intro x hx y hy hxy
    dsimp [f]
    exact Real.rpow_le_rpow_of_nonpos
      (lt_of_lt_of_le hmpos hx) hxy (by norm_num)
  have hInt : IntegrableOn f (Set.Ioi (m : ℝ)) := by
    simpa [f] using integrableOn_Ioi_rpow_of_lt
      (by norm_num : -((3 : ℝ) / 2) < -1) hmpos
  have hnonneg : ∀ x ∈ Set.Ioi (m : ℝ), 0 ≤ f x := by
    intro x hx
    exact Real.rpow_nonneg (le_of_lt (lt_trans hmpos hx)) _
  have hrest :
      ∑ j ∈ Finset.Ico m M, f (j + 1 : ℕ) ≤ ∫ x in Set.Ioi (m : ℝ), f x := by
    exact (hanti.mono Set.Icc_subset_Ici_self).sum_Ico_le_integral hInt hnonneg
  have hsumShift :
      ∑ j ∈ Finset.Ico m M, f (j + 1 : ℕ) = ∑ j ∈ Finset.Ioc m M, f j := by
    apply Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
    · intro j hj
      rcases Finset.mem_Ico.mp hj with ⟨hmj, hjM⟩
      exact Finset.mem_Ioc.mpr ⟨Nat.lt_succ_of_le hmj, Nat.succ_le_of_lt hjM⟩
    · intro a ha b hb hab
      exact Nat.succ.inj hab
    · intro b hb
      rcases Finset.mem_Ioc.mp hb with ⟨hmB, bM⟩
      have hbpos : 1 ≤ b := by omega
      refine ⟨b - 1, Finset.mem_Ico.mpr ?_, ?_⟩
      · exact ⟨Nat.le_sub_one_of_lt hmB, by omega⟩
      · exact Nat.sub_add_cancel hbpos
    · intro j hj
      rfl
  have hsum :
      ∑ j ∈ Finset.Icc m M, f j = f m + ∑ j ∈ Finset.Ico m M, f (j + 1 : ℕ) := by
    rw [Finset.Icc_eq_cons_Ioc hmM, Finset.sum_cons, hsumShift]
  have hsqrt : (m : ℝ) ^ (-((1 : ℝ) / 2)) = 1 / Real.sqrt m := by
    rw [Real.sqrt_eq_rpow]
    calc
      (m : ℝ) ^ (-((1 : ℝ) / 2)) = ((m : ℝ) ^ ((1 : ℝ) / 2))⁻¹ :=
        Real.rpow_neg hmpos.le _
      _ = 1 / ((m : ℝ) ^ ((1 : ℝ) / 2)) := by simp only [one_div]
  have hfirst : f (m : ℝ) ≤ 1 / Real.sqrt m := by
    have hpow : (m : ℝ) ^ (-((3 : ℝ) / 2)) ≤ (m : ℝ) ^ (-((1 : ℝ) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hmone (by norm_num)
    calc
      f (m : ℝ) = (m : ℝ) ^ (-((3 : ℝ) / 2)) := rfl
      _ ≤ (m : ℝ) ^ (-((1 : ℝ) / 2)) := hpow
      _ = 1 / Real.sqrt m := hsqrt
  have hintegral : ∫ x in Set.Ioi (m : ℝ), f x = 2 / Real.sqrt m := by
    rw [show f = fun x : ℝ => x ^ (-((3 : ℝ) / 2)) by rfl]
    rw [integral_Ioi_rpow_of_lt (by norm_num : -((3 : ℝ) / 2) < -1) hmpos]
    rw [show -((3 : ℝ) / 2) + 1 = -((1 : ℝ) / 2) by ring]
    rw [hsqrt]
    field_simp
  calc
    ∑ j ∈ Finset.Icc m M, 1 / (j : ℝ) ^ ((3 : ℝ) / 2) =
        ∑ j ∈ Finset.Icc m M, f j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hj0 : 0 < (j : ℝ) := by
            have : 0 < m := Nat.zero_lt_of_lt hm
            exact_mod_cast lt_of_lt_of_le this (Finset.mem_Icc.mp hj).1
          dsimp [f]
          rw [div_eq_mul_inv, one_mul]
          change ((j : ℝ) ^ ((3 : ℝ) / 2))⁻¹ =
            (j : ℝ) ^ (-((3 : ℝ) / 2))
          exact (Real.rpow_neg hj0.le ((3 : ℝ) / 2)).symm
    _ = f (m : ℝ) + ∑ j ∈ Finset.Ico m M, f (j + 1 : ℕ) := hsum
    _ ≤ 1 / Real.sqrt m + 2 / Real.sqrt m := by
      have hrest' := hrest
      rw [hintegral] at hrest'
      exact add_le_add hfirst hrest'
    _ = 3 / Real.sqrt m := by ring

/-- The sum of block reciprocal errors from `r` to `s` has the terminal-distance scale. -/
private theorem block_reciprocal_error_sum_le (r s K : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s)
    (hsK : s < K) (D : ℝ) (hD : 0 ≤ D) :
    ∑ i ∈ Finset.Icc r s, D / ((K : ℝ) - i) ^ ((3 : ℝ) / 2) ≤
      3 * D / Real.sqrt ((K : ℝ) - s) := by
  have hsK' : s + 1 ≤ K := by omega
  have hm : 1 ≤ K - s := by omega
  let m := K - s
  let M := K - r
  have hindex :
      ∑ i ∈ Finset.Icc r s, 1 / ((K : ℝ) - i) ^ ((3 : ℝ) / 2) =
        ∑ j ∈ Finset.Icc m M, 1 / (j : ℝ) ^ ((3 : ℝ) / 2) := by
    refine Finset.sum_bij (fun i _ => K - i) ?_ ?_ ?_ ?_
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      simp only [Finset.mem_Icc]
      constructor
      · exact Nat.sub_le_sub_left hi'.2 K
      · exact Nat.sub_le_sub_left hi'.1 K
    · intro a ha b hb hab
      have haK : a ≤ K := by have h := Finset.mem_Icc.mp ha; omega
      have hbK : b ≤ K := by have h := Finset.mem_Icc.mp hb; omega
      omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      have hjK : j ≤ K := by dsimp [M] at hj'; omega
      refine ⟨K - j, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        constructor <;> omega
      · omega
    · intro i hi
      congr 1
      have hiK : i ≤ K := le_trans (Finset.mem_Icc.mp hi).2 (Nat.le_of_lt hsK)
      rw [Nat.cast_sub hiK]
  have hsum := inv_rpow_three_halves_interval_le m M (by simpa [m] using hm)
    (by dsimp [m, M]; omega)
  have hmReal : (m : ℝ) = (K : ℝ) - s := by
    dsimp [m]
    rw [Nat.cast_sub (by omega)]
  calc
    _ = D * (∑ i ∈ Finset.Icc r s,
          1 / ((K : ℝ) - i) ^ ((3 : ℝ) / 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = D * (∑ j ∈ Finset.Icc m M, 1 / (j : ℝ) ^ ((3 : ℝ) / 2)) := by rw [hindex]
    _ ≤ D * (3 / Real.sqrt m) := by
      exact mul_le_mul_of_nonneg_left hsum hD
    _ = 3 * D / Real.sqrt ((K : ℝ) - s) := by rw [hmReal]; ring

/-- A product of factors one minus a number is bounded below by one minus their sum. -/
theorem prod_one_sub_ge_one_sub_sum (s : Finset ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hsum0 : 0 ≤ ∑ j ∈ s, a j :=
        Finset.sum_nonneg fun j hj => ha0 j (Finset.mem_insert_of_mem hj)
      have hai0 : 0 ≤ a i := ha0 i (Finset.mem_insert_self _ _)
      have hfactor : 0 ≤ 1 - a i := sub_nonneg.mpr (ha1 i (Finset.mem_insert_self _ _))
      have ih' := ih
        (fun j hj => ha0 j (Finset.mem_insert_of_mem hj))
        (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
      have hmul := mul_le_mul_of_nonneg_left ih' hfactor
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      nlinarith [mul_nonneg hai0 hsum0]

/-- The block-moment estimate and the blockwise inverse-moment estimate give a lower bound on the product of inverse
block moments. The block inverse moments and second moments are integrable by
`integrable_blockMass_inv_and_sq`. -/
theorem prod_integral_inv_blockMass_ge_of (hC6 : BlockMomentsBound)
    (A ρ₀ ρ₁ : ℝ) (hρ : 1 < ρ₀) :
    ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ r s : ℕ, 1 ≤ r → r ≤ s → s + 1 ≤ blockCount N ρ →
        (1 - C / Real.sqrt ((blockCount N ρ : ℝ) - s)) *
            ∏ i ∈ Finset.Icc r s,
              ∫ ω, blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω ^ 2 ∂disorderLaw ≤
          ∏ i ∈ Finset.Icc r s,
              ∫ ω, (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw := by
  obtain ⟨C₀, hC₀⟩ := blockMass_inv_moment_sub_sq_moment_of hC6 A ρ₀ ρ₁ hρ
  let D := max C₀ 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC₀le : C₀ ≤ D := le_max_left _ _
  refine ⟨3 * D, ?_⟩
  intro ρ hρρ
  filter_upwards [hC₀ ρ hρρ] with N hN
  intro ϑ hϑ r s hr hrs hsK
  have hK : s < blockCount N ρ := by omega
  have hsum := block_reciprocal_error_sum_le r s (blockCount N ρ) hr hrs hK D hD
  have hmpos : 0 < (blockCount N ρ : ℝ) - s := by
    have : 0 < blockCount N ρ - s := by omega
    have hreal : 0 < ((blockCount N ρ - s : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at hreal
    exact hreal
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let mInv := fun i : ℕ => ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw
  let mSq := fun i : ℕ => ∫ ω, blockMass β t i ω ^ 2 ∂disorderLaw
  let a := fun i : ℕ => D / ((blockCount N ρ : ℝ) - i) ^ ((3 : ℝ) / 2)
  have ha_nonneg (i : ℕ) (hi : i ∈ Finset.Icc r s) : 0 ≤ a i := by
    dsimp [a]
    have hi' := Finset.mem_Icc.mp hi
    have hiK : i < blockCount N ρ := by omega
    have hden : 0 < (blockCount N ρ : ℝ) - i := by
      have hnat : 0 < blockCount N ρ - i := by omega
      have hreal : 0 < ((blockCount N ρ - i : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [Nat.cast_sub (by omega)] at hreal
      exact hreal
    positivity
  have hblock (i : ℕ) (hi : i ∈ Finset.Icc r s) :
      mSq i - a i ≤ mInv i := by
    have hi' := Finset.mem_Icc.mp hi
    have hi1 : 1 ≤ i := le_trans hr hi'.1
    have hiK : i + 1 ≤ blockCount N ρ := by omega
    have hbound := hN ϑ hϑ i hi1 hiK
    have hdef : |mInv i - mSq i| ≤
        C₀ / ((blockCount N ρ : ℝ) - i) ^ ((3 : ℝ) / 2) := by
      simpa [mInv, mSq, β, t] using hbound
    have hdenpos : 0 < (blockCount N ρ : ℝ) - i := by
      have hnat : 0 < blockCount N ρ - i := by omega
      have hreal : 0 < ((blockCount N ρ - i : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [Nat.cast_sub (by omega)] at hreal
      exact hreal
    have hDden : C₀ / ((blockCount N ρ : ℝ) - i) ^ ((3 : ℝ) / 2) ≤ a i := by
      dsimp [a]
      exact div_le_div_of_nonneg_right hC₀le (Real.rpow_nonneg hdenpos.le _)
    have habs := abs_le.mp hdef
    have hle : mSq i - mInv i ≤ a i := by linarith
    linarith
  have hMsq_one (i : ℕ) : 1 ≤ mSq i := by
    have hmem : MemLp (fun ω => blockMass β t i ω) 2 disorderLaw := by
      dsimp [β, t]
      exact Polymer.memLp_smoothedP2Plane _ _ _ _ 2 (by norm_num)
    have hmean : ∫ ω, blockMass β t i ω ∂disorderLaw = 1 := by
      dsimp [β, t]
      exact Polymer.integral_smoothedP2Plane _ _ _ _
    have hvar := ProbabilityTheory.variance_nonneg (fun ω => blockMass β t i ω) disorderLaw
    rw [ProbabilityTheory.variance_eq_sub hmem, hmean] at hvar
    have hvar' : 0 ≤ mSq i - 1 := by
      simpa [mSq, pow_two] using hvar
    linarith
  have hInv_one (i : ℕ) : 1 ≤ mInv i := by
    dsimp [mInv, β, t]
    exact one_le_integral_inv_blockMass _ _ _
  have hblockProd (i : ℕ) (hi : i ∈ Finset.Icc r s) :
      mSq i * (1 - a i) ≤ mInv i := by
    have hmul : a i * (mSq i - 1) ≥ 0 :=
      mul_nonneg (ha_nonneg i hi) (sub_nonneg.mpr (hMsq_one i))
    have h1 := hblock i hi
    nlinarith
  let S := ∑ i ∈ Finset.Icc r s, a i
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i hi => ha_nonneg i hi
  have hSbound : S ≤ 3 * D / Real.sqrt ((blockCount N ρ : ℝ) - s) := by
    dsimp [S, a]
    exact hsum
  let B := ∏ i ∈ Finset.Icc r s, mSq i
  let V := ∏ i ∈ Finset.Icc r s, mInv i
  have hBpos : 0 < B := by
    dsimp [B]
    exact Finset.prod_pos fun i hi => lt_of_lt_of_le zero_lt_one (hMsq_one i)
  have hVpos : 0 < V := by
    dsimp [V]
    exact Finset.prod_pos fun i hi => lt_of_lt_of_le zero_lt_one (hInv_one i)
  by_cases hS : S < 1
  · have ha_lt_one (i : ℕ) (hi : i ∈ Finset.Icc r s) : a i < 1 := by
      have hsingle : a i ≤ S := by
        dsimp [S]
        exact Finset.single_le_sum (fun j hj => ha_nonneg j hj) hi
      exact lt_of_le_of_lt hsingle hS
    have hprodOneSub : 1 - S ≤ ∏ i ∈ Finset.Icc r s, (1 - a i) := by
      simpa [S] using prod_one_sub_ge_one_sub_sum (Finset.Icc r s) a
        (fun i hi => ha_nonneg i hi) (fun i hi => le_of_lt (ha_lt_one i hi))
    have hprodB :
        B * ∏ i ∈ Finset.Icc r s, (1 - a i) ≤ V := by
      dsimp [B, V]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod₀
      · intro i hi
        exact mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one (hMsq_one i)))
          (sub_nonneg.mpr (le_of_lt (ha_lt_one i hi)))
      · intro i hi
        exact hblockProd i hi
    have hfinal : (1 - 3 * D / Real.sqrt ((blockCount N ρ : ℝ) - s)) * B ≤ V := by
      calc
        _ ≤ (1 - S) * B := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hBpos)
          linarith [hSbound]
        _ ≤ (∏ i ∈ Finset.Icc r s, (1 - a i)) * B :=
          mul_le_mul_of_nonneg_right hprodOneSub (le_of_lt hBpos)
        _ = B * ∏ i ∈ Finset.Icc r s, (1 - a i) := by ring
        _ ≤ V := hprodB
    simpa [B, V, β, t, mSq, mInv] using hfinal
  · have hcoef : 1 - 3 * D / Real.sqrt ((blockCount N ρ : ℝ) - s) ≤ 0 := by
      have hsumlarge : 1 ≤ S := le_of_not_gt hS
      linarith [hSbound]
    have htarget :
        (1 - 3 * D / Real.sqrt ((blockCount N ρ : ℝ) - s)) * B ≤ V := by
      calc
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcoef (le_of_lt hBpos)
        _ ≤ V := le_of_lt hVpos
    simpa [B, V, β, t, mSq, mInv] using htarget

end Critical2DKPZ.OnePoint

end
