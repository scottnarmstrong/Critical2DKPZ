/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockGaussianCompositionLimit
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # The support tail of a sampled Gaussian block -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

private theorem fullGaussianBlockOutsideWeight_le_majorant
    (m : ℕ) (hm : 0 < m) (j : ℤ)
    (hj : j ∉ Finset.Icc (0 : ℤ) m) :
    fullGaussianBlockWeight m j ≤
      Real.exp (-((m : ℝ) / 2)) *
        Real.exp (-(1 / (2 * (m : ℝ))) * (2 * (j : ℝ) - (m : ℝ)) ^ 2) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have houtside : j < 0 ∨ (m : ℤ) < j := by
    by_contra h
    push Not at h
    exact hj (Finset.mem_Icc.mpr h)
  have hcenter : (m : ℝ) ≤ |2 * (j : ℝ) - (m : ℝ)| := by
    rcases houtside with hleft | hright
    · have hleft' : 2 * j - (m : ℤ) ≤ -(m : ℤ) := by omega
      have hleftR : 2 * (j : ℝ) - (m : ℝ) ≤ -(m : ℝ) := by exact_mod_cast hleft'
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hright' : (m : ℤ) ≤ 2 * j - (m : ℤ) := by omega
      have hrightR : (m : ℝ) ≤ 2 * (j : ℝ) - (m : ℝ) := by exact_mod_cast hright'
      rw [abs_of_nonneg (by linarith)]
      exact hrightR
  have hsquare : (m : ℝ) ^ 2 ≤ (2 * (j : ℝ) - (m : ℝ)) ^ 2 := by
    nlinarith [sq_abs (2 * (j : ℝ) - (m : ℝ))]
  have hexp : -((2 * (j : ℝ) - (m : ℝ)) ^ 2) / (m : ℝ) ≤
      -((m : ℝ) / 2) -
        (1 / (2 * (m : ℝ))) * (2 * (j : ℝ) - (m : ℝ)) ^ 2 := by
    have hhalf : (m : ℝ) / 2 ≤
        (2 * (j : ℝ) - (m : ℝ)) ^ 2 / (2 * (m : ℝ)) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
        (by positivity : (0 : ℝ) < 2 * (m : ℝ))).2
      nlinarith [hsquare]
    have hdecomp : (2 * (j : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ) =
        (2 * (j : ℝ) - (m : ℝ)) ^ 2 / (2 * (m : ℝ)) +
          (2 * (j : ℝ) - (m : ℝ)) ^ 2 / (2 * (m : ℝ)) := by
      field_simp [hmR.ne']; ring
    have hdecompNeg : -((2 * (j : ℝ) - (m : ℝ)) ^ 2) / (m : ℝ) =
        -((2 * (j : ℝ) - (m : ℝ)) ^ 2 / (2 * (m : ℝ))) -
          ((2 * (j : ℝ) - (m : ℝ)) ^ 2 / (2 * (m : ℝ))) := by
      rw [show -((2 * (j : ℝ) - (m : ℝ)) ^ 2) / (m : ℝ) =
        -(((2 * (j : ℝ) - (m : ℝ)) ^ 2) / (m : ℝ)) by ring, hdecomp]
      ring
    rw [hdecompNeg]
    have harg : (1 / (2 * (m : ℝ))) *
        (2 * (j : ℝ) - (m : ℝ)) ^ 2 =
        (2 * (j : ℝ) - (m : ℝ)) ^ 2 / (2 * (m : ℝ)) := by
      field_simp
    rw [harg]
    linarith
  rw [fullGaussianBlockWeight]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [hexp]

private theorem shiftedGaussianMass_le_linear (m : ℕ) (hm : 0 < m) :
    (∑' j : ℤ,
      Real.exp (-(1 / (2 * (m : ℝ))) * (2 * (j : ℝ) - (m : ℝ)) ^ 2)) ≤
        7 * (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  let b : ℝ := 1 / (2 * (m : ℝ))
  have hb : 0 < b := by dsimp [b]; positivity
  have hmap : Function.Injective (fun j : ℤ => 2 * j - (m : ℤ)) := by
    intro j k h
    have h' := congrArg (fun x : ℤ => x + (m : ℤ)) h
    have h'' : (2 : ℤ) * j = 2 * k := by
      simpa only [sub_add_cancel] using h'
    exact (mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h'')
  have hcomp := tsum_comp_le_tsum_of_inj
    (summable_exp_neg_int_sq b hb)
    (fun k => Real.exp_nonneg _)
    hmap
  have hsum := tsum_exp_neg_int_sq_le b hb
  have hden : 0 < 1 - Real.exp (-b) := by
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hbexp : 1 + b ≤ Real.exp b := by linarith [Real.add_one_le_exp b]
  have hrecip : Real.exp (-b) ≤ 1 / (1 + b) := by
    rw [Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le (by positivity) hbexp
  have hdenLower : b / (1 + b) ≤ 1 - Real.exp (-b) := by
    rw [div_le_iff₀ (by positivity)]
    have hmul := mul_le_mul_of_nonneg_right hrecip (by positivity : 0 ≤ 1 + b)
    have hmul' : Real.exp (-b) * (1 + b) ≤ 1 := by
      calc
        _ ≤ (1 / (1 + b)) * (1 + b) := hmul
        _ = 1 := by field_simp
    nlinarith [hmul']
  have hqleOne : Real.exp (-b) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hratio : Real.exp (-b) / (1 - Real.exp (-b)) ≤ (1 + b) / b := by
    calc
      _ ≤ 1 / (1 - Real.exp (-b)) :=
        div_le_div_of_nonneg_right hqleOne hden.le
      _ ≤ 1 / (b / (1 + b)) :=
        one_div_le_one_div_of_le (by positivity) hdenLower
      _ = (1 + b) / b := by field_simp
  have hbound :
      1 + 2 * Real.exp (-b) / (1 - Real.exp (-b)) ≤ 7 * (m : ℝ) := by
    have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_of_lt hm)
    have hbform : (1 + b) / b = 2 * (m : ℝ) + 1 := by
      dsimp [b]
      field_simp
    rw [hbform] at hratio
    calc
      _ = 1 + 2 * (Real.exp (-b) / (1 - Real.exp (-b))) := by ring
      _ ≤ 1 + 2 * (2 * (m : ℝ) + 1) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2))
      _ ≤ 7 * (m : ℝ) := by nlinarith [hmone]
  calc
    _ = ∑' j : ℤ, Real.exp (-b * ((2 * j - (m : ℤ) : ℤ) : ℝ) ^ 2) := by
      apply tsum_congr
      intro j
      simp only [b, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    _ ≤ ∑' k : ℤ, Real.exp (-b * (k : ℝ) ^ 2) := hcomp
    _ ≤ 7 * (m : ℝ) := hsum.trans hbound

/-- The normalized sampled Gaussian, extended by zero outside its finite support, converges in discrete `L¹` to the full-lattice Gaussian. The latter is summable by `summable_fullGaussianBlockProbability`. -/
theorem eventually_gaussianizedBlockIntProbability_l1_le :
    ∀ᶠ m : ℕ in atTop,
      (∑' j : ℤ,
        |gaussianizedBlockIntProbability m j - fullGaussianBlockProbability m j|) ≤
        56 * Real.sqrt (m : ℝ) * Real.exp (-((m : ℝ) / 2)) := by
  have htheta : ∀ᶠ m : ℕ in atTop,
      fullGaussianBlockMassThetaError m ≤ 1 / 2 := by
    have ht := tendsto_fullGaussianBlockMassThetaError
    filter_upwards [ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with m hm
    exact hm
  filter_upwards [htheta, eventually_ge_atTop 1] with m hthetaM hm
  have hmpos : 0 < m := by omega
  have hmassBounds := fullGaussianBlockWeightMass_bounds_of_theta_small m hmpos hthetaM
  let F : Finset ℤ := Finset.Icc (0 : ℤ) m
  let Z : ℝ := ∑' j : ℤ, fullGaussianBlockWeight m j
  let U : ℝ := ∑ j ∈ F, fullGaussianBlockWeight m j
  let T : ℝ := ∑' j : {j : ℤ // j ∉ F}, fullGaussianBlockWeight m j
  have hZpos : 0 < Z := fullGaussianBlockMass_pos m hmpos
  have hZlower : Real.sqrt (m : ℝ) / 4 ≤ Z := by
    have hpi : 1 ≤ Real.sqrt Real.pi := by
      calc
        1 = Real.sqrt 1 := by norm_num
        _ ≤ Real.sqrt Real.pi := Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
    have hmR : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    calc
      Real.sqrt (m : ℝ) / 4 ≤ Real.sqrt (Real.pi * (m : ℝ) / 4) / 2 := by
        have hsq : (Real.sqrt (m : ℝ)) ^ 2 ≤
            (2 * Real.sqrt (Real.pi * (m : ℝ) / 4)) ^ 2 := by
          rw [Real.sq_sqrt hmR, mul_pow, Real.sq_sqrt (by positivity)]
          have hpi' : (1 : ℝ) ≤ Real.pi := by
            nlinarith [hpi, Real.sq_sqrt Real.pi_pos.le]
          nlinarith [hpi', hmR]
        have hrootNonneg : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
        have hboundNonneg : 0 ≤ 2 * Real.sqrt (Real.pi * (m : ℝ) / 4) := by positivity
        have hroot : Real.sqrt (m : ℝ) ≤ 2 * Real.sqrt (Real.pi * (m : ℝ) / 4) :=
          (sq_le_sq₀ hrootNonneg hboundNonneg).mp hsq
        nlinarith
      _ ≤ Z := hmassBounds.1
  have hsplit := (summable_fullGaussianBlockWeight m hmpos).sum_add_tsum_subtype_compl F
  have hsplit' : U + T = Z := by simpa [F, U, T, Z] using hsplit
  have hUratio : (∑ j ∈ F, fullGaussianBlockProbability m j) = U / Z := by
    simp [U, Z, F, fullGaussianBlockProbability, Finset.sum_div]
  have htailRatio : 1 - U / Z = T / Z := by
    have hsub : Z - U = T := by linarith [hsplit']
    rw [← hsub]
    field_simp [hZpos.ne']
  have hTbound : T ≤ Real.exp (-((m : ℝ) / 2)) * (7 * (m : ℝ)) := by
    let g : ℤ → ℝ := fun j =>
      Real.exp (-((m : ℝ) / 2)) *
        Real.exp (-(1 / (2 * (m : ℝ))) * (2 * (j : ℝ) - (m : ℝ)) ^ 2)
    have hpoint : ∀ j : {j : ℤ // j ∉ F},
        fullGaussianBlockWeight m j ≤ g j := by
      intro j
      exact fullGaussianBlockOutsideWeight_le_majorant m hmpos j j.property
    have hg : Summable g := by
      have hb : 0 < 1 / (2 * (m : ℝ)) := by positivity
      have hq : Summable (fun k : ℤ =>
          Real.exp (-(1 / (2 * (m : ℝ))) * (k : ℝ) ^ 2)) := by
        simpa using summable_exp_neg_int_sq (1 / (2 * (m : ℝ))) hb
      have hmap : Function.Injective (fun j : ℤ => 2 * j - (m : ℤ)) := by
        intro j k h
        have h' := congrArg (fun x : ℤ => x + (m : ℤ)) h
        have h'' : (2 : ℤ) * j = 2 * k := by
          simpa only [sub_add_cancel] using h'
        exact (mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h'')
      have hcomp : Summable (fun j : ℤ =>
          Real.exp (-(1 / (2 * (m : ℝ))) * ((2 * j - (m : ℤ) : ℤ) : ℝ) ^ 2)) := by
        exact hq.comp_injective hmap
      simpa [g, mul_comm] using hcomp.mul_left (Real.exp (-((m : ℝ) / 2)))
    have hbshift := shiftedGaussianMass_le_linear m hmpos
    calc
      T ≤ ∑' j : {j : ℤ // j ∉ F}, g j := by
        apply Summable.tsum_le_tsum
        · exact hpoint
        · exact (summable_fullGaussianBlockWeight m hmpos).subtype _
        · exact hg.subtype _
      _ ≤ ∑' j : ℤ, g j :=
        Summable.tsum_subtype_le g (fun j : ℤ => j ∉ F)
          (fun _ => by positivity) hg
      _ = Real.exp (-((m : ℝ) / 2)) *
          (∑' j : ℤ,
            Real.exp (-(1 / (2 * (m : ℝ))) * (2 * (j : ℝ) - (m : ℝ)) ^ 2)) := by
            rw [tsum_mul_left]
      _ ≤ Real.exp (-((m : ℝ) / 2)) * (7 * (m : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hbshift (Real.exp_nonneg _)
  have hratioBound : T / Z ≤ 28 * Real.sqrt (m : ℝ) *
      Real.exp (-((m : ℝ) / 2)) := by
    rw [div_le_iff₀ hZpos]
    have hroot : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hmpos)
    have hrootSq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)
    have hZlower' := hZlower
    calc
      T ≤ Real.exp (-((m : ℝ) / 2)) * (7 * (m : ℝ)) := hTbound
      _ ≤ (28 * Real.sqrt (m : ℝ) * Real.exp (-((m : ℝ) / 2))) * Z := by
        have hbase : 7 * (m : ℝ) ≤ 28 * Real.sqrt (m : ℝ) * Z := by
          calc
            7 * (m : ℝ) = 7 * (Real.sqrt (m : ℝ) ^ 2) := by rw [hrootSq]
            _ = 28 * Real.sqrt (m : ℝ) * (Real.sqrt (m : ℝ) / 4) := by ring
            _ ≤ 28 * Real.sqrt (m : ℝ) * Z :=
              mul_le_mul_of_nonneg_left hZlower (by positivity)
        calc
          Real.exp (-((m : ℝ) / 2)) * (7 * (m : ℝ)) ≤
              Real.exp (-((m : ℝ) / 2)) * (28 * Real.sqrt (m : ℝ) * Z) :=
                mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg _)
          _ = (28 * Real.sqrt (m : ℝ) * Real.exp (-((m : ℝ) / 2))) * Z := by ring_nf
  have hprofile := gaussianizedBlockIntProbability_l1_eq m hmpos
  rw [hprofile, hUratio]
  have hbound : 2 * (1 - U / Z) ≤
      56 * Real.sqrt (m : ℝ) * Real.exp (-((m : ℝ) / 2)) := by
    rw [htailRatio]
    nlinarith [hratioBound]
  exact hbound


end Critical2DKPZ.SHF.Moments

end
