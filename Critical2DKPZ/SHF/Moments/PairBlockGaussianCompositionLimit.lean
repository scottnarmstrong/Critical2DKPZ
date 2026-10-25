/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockGaussianList
public import Critical2DKPZ.SHF.Moments.PairBlockCompositionProfile
import Mathlib.Tactic

/-! # Local profiles of Gaussianized pair-block compositions -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

/-- The normalized sampled Gaussian block law, extended by zero from its
natural support to the integer lattice. -/
def gaussianizedBlockIntProbability (m : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j ∧ j ≤ (m : ℤ) then
    normalizedSampledHypergeometricGaussianWeight m j.toNat
  else 0

private theorem sum_range_cast_eq_Icc (m : ℕ) (f : ℤ → ℝ) :
    (∑ k ∈ Finset.range (m + 1), f (k : ℤ)) =
      ∑ j ∈ Finset.Icc (0 : ℤ) m, f j := by
  classical
  refine Finset.sum_bij (fun k hk => (k : ℤ)) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc]
    constructor
    · exact_mod_cast (Nat.zero_le k)
    · exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  · intro k hk l hl hEq
    exact_mod_cast hEq
  · intro j hj
    have hj0 : 0 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjm : j ≤ (m : ℤ) := (Finset.mem_Icc.mp hj).2
    refine ⟨j.toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      have hjcast : (j.toNat : ℤ) ≤ (m : ℤ) := by
        simpa [Int.toNat_of_nonneg hj0] using hjm
      exact Nat.lt_succ_of_le (by exact_mod_cast hjcast)
    · exact Int.toNat_of_nonneg hj0
  · intro k hk
    rfl

/-- The sampled one-block Gaussian profile is the continuous Gaussian weight
divided by its integral mass. -/
theorem sampledHypergeometricGaussianWeight_eq_fullGaussianBlockWeight_div
    (m k : ℕ) (hm : 0 < m) :
    sampledHypergeometricGaussianWeight m k =
      fullGaussianBlockWeight m (k : ℤ) / fullGaussianBlockIntegralMass m := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmroot : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hpiroot : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hI : fullGaussianBlockIntegralMass m =
      (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) / 2 := by
    dsimp [fullGaussianBlockIntegralMass]
    rw [show Real.pi * (m : ℝ) / 4 =
      (Real.pi * (m : ℝ)) / (4 : ℝ) by ring,
      Real.sqrt_div (by positivity), Real.sqrt_mul Real.pi_pos.le]
    have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
    rw [hsqrt4]
  have hcoef : (2 / Real.sqrt Real.pi / Real.sqrt (m : ℝ)) =
      (fullGaussianBlockIntegralMass m)⁻¹ := by
    rw [hI]
    field_simp [hpiroot.ne', hmroot.ne']
  rw [sampledHypergeometricGaussianWeight, fullGaussianBlockWeight]
  have harg : -(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ) =
      -(2 * ((k : ℤ) : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ) := by
    push_cast
    rfl
  rw [harg, hcoef]
  simp only [div_eq_mul_inv]
  ring

private theorem gaussianizedBlockIntProbability_eq_weight_div_sum
    (m : ℕ) (hm : 0 < m) (j : ℤ) (hj : j ∈ Finset.Icc (0 : ℤ) m) :
    gaussianizedBlockIntProbability m j =
      fullGaussianBlockWeight m j /
        (∑ k ∈ Finset.Icc (0 : ℤ) m, fullGaussianBlockWeight m k) := by
  classical
  let I := fullGaussianBlockIntegralMass m
  let U := ∑ k ∈ Finset.Icc (0 : ℤ) m, fullGaussianBlockWeight m k
  have hIpos : 0 < I := by dsimp [I, fullGaussianBlockIntegralMass]; positivity
  have hUpos : 0 < U := by
    dsimp [U]
    apply Finset.sum_pos
    · intro k hk
      unfold fullGaussianBlockWeight
      exact Real.exp_pos _
    · exact ⟨0, by simp⟩
  have hS : (∑ k ∈ Finset.range (m + 1),
        sampledHypergeometricGaussianWeight m k) = U / I := by
    calc
      _ = ∑ k ∈ Finset.range (m + 1),
          fullGaussianBlockWeight m (k : ℤ) / I := by
            apply Finset.sum_congr rfl
            intro k hk
            exact sampledHypergeometricGaussianWeight_eq_fullGaussianBlockWeight_div
              m k hm
      _ = (∑ k ∈ Finset.range (m + 1),
          fullGaussianBlockWeight m (k : ℤ)) / I := by rw [Finset.sum_div]
      _ = U / I := by rw [sum_range_cast_eq_Icc]
  have hj0 : 0 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjm : j ≤ (m : ℤ) := (Finset.mem_Icc.mp hj).2
  have hcast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
  have hq : gaussianizedBlockIntProbability m j =
      normalizedSampledHypergeometricGaussianWeight m j.toNat := by
    simp [gaussianizedBlockIntProbability, hj0, hjm]
  rw [hq]
  rw [normalizedSampledHypergeometricGaussianWeight,
    sampledHypergeometricGaussianWeight_eq_fullGaussianBlockWeight_div m j.toNat hm,
    hcast, hS]
  dsimp [I, U]
  dsimp [I, U] at hIpos hUpos
  field_simp [hIpos.ne', hUpos.ne']

/-- Conditioning a full-lattice Gaussian block to its natural support changes
its law in discrete `L¹` by exactly twice the discarded Gaussian mass. -/
theorem gaussianizedBlockIntProbability_l1_eq
    (m : ℕ) (hm : 0 < m) :
    (∑' j : ℤ,
      |gaussianizedBlockIntProbability m j - fullGaussianBlockProbability m j|) =
      2 * (1 - ∑ j ∈ Finset.Icc (0 : ℤ) m,
        fullGaussianBlockProbability m j) := by
  classical
  let F : Finset ℤ := Finset.Icc (0 : ℤ) m
  let q : ℤ → ℝ := gaussianizedBlockIntProbability m
  let p : ℤ → ℝ := fullGaussianBlockProbability m
  let U : ℝ := ∑ j ∈ F, fullGaussianBlockWeight m j
  let Z : ℝ := ∑' j : ℤ, fullGaussianBlockWeight m j
  let r : ℝ := ∑ j ∈ F, p j
  have hUpos : 0 < U := by
    dsimp [U, F]
    apply Finset.sum_pos
    · intro j hj
      unfold fullGaussianBlockWeight
      exact Real.exp_pos _
    · exact ⟨0, by simp⟩
  have hZpos : 0 < Z := by
    dsimp [Z]
    exact fullGaussianBlockMass_pos m hm
  have hrform : r = U / Z := by
    dsimp [r, p, U, Z, F, fullGaussianBlockProbability]
    rw [Finset.sum_div]
  have hrpos : 0 < r := by rw [hrform]; exact div_pos hUpos hZpos
  have hsummable : Summable p := by
    dsimp [p]
    exact summable_fullGaussianBlockProbability m hm
  have hpnonneg (j : ℤ) : 0 ≤ p j := by
    dsimp [p]
    exact (fullGaussianBlockProbability_nonneg_le_one m hm j).1
  have htotal : ∑' j : ℤ, p j = 1 := by
    dsimp [p]
    exact tsum_fullGaussianBlockProbability m hm
  have hrle : r ≤ 1 := by
    have h := hsummable.sum_le_tsum F (fun j hj => hpnonneg j)
    rw [htotal] at h
    simpa [r] using h
  have hqform (j : ℤ) (hj : j ∈ F) : q j =
      fullGaussianBlockWeight m j / U := by
    dsimp [q, U, F] at *
    simpa [p, U, F] using
      gaussianizedBlockIntProbability_eq_weight_div_sum m hm j hj
  have hpform (j : ℤ) : p j = fullGaussianBlockWeight m j / Z := by
    rfl
  have hrelation (j : ℤ) (hj : j ∈ F) :
      q j - p j = p j * (r⁻¹ - 1) := by
    rw [hqform j hj, hpform j, hrform]
    field_simp [hUpos.ne', hZpos.ne']
  have hinv : 1 ≤ r⁻¹ := by
    rw [← one_div]
    rw [le_div_iff₀ hrpos]
    simpa using hrle
  have hfactor : 0 ≤ r⁻¹ - 1 := sub_nonneg.mpr hinv
  have hfinite : (∑ j ∈ F, |q j - p j|) = 1 - r := by
    calc
      _ = ∑ j ∈ F, |p j * (r⁻¹ - 1)| := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hrelation j hj]
      _ = r * |r⁻¹ - 1| := by
        calc
          _ = ∑ j ∈ F, p j * |r⁻¹ - 1| := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [abs_mul, abs_of_nonneg (hpnonneg j)]
          _ = (∑ j ∈ F, p j) * |r⁻¹ - 1| := by rw [← Finset.sum_mul]
          _ = r * |r⁻¹ - 1| := by rfl
      _ = 1 - r := by
        rw [abs_of_nonneg hfactor]
        have hdiv : r⁻¹ - 1 = (1 - r) / r := by
          field_simp [hrpos.ne']
        rw [hdiv]
        field_simp [hrpos.ne']
  have htail : (∑' j : {j : ℤ // j ∉ F}, p j) = 1 - r := by
    have hsplit := hsummable.sum_add_tsum_subtype_compl F
    rw [htotal] at hsplit
    have hsplit' : r + (∑' j : {j : ℤ // j ∉ F}, p j) = 1 := by
      simpa [r] using hsplit
    linarith
  have hqsum : Summable q := by
    apply summable_of_hasFiniteSupport
    apply (F.finite_toSet).subset
    intro j hj
    by_contra hnot
    have hnot' : ¬ (0 ≤ j ∧ j ≤ (m : ℤ)) := by
      simpa [F, Finset.mem_Icc] using hnot
    have hqzero : q j = 0 := by
      simp [q, gaussianizedBlockIntProbability, hnot']
    exact hj hqzero
  have habs : Summable (fun j : ℤ => |q j - p j|) := by
    simpa [Real.norm_eq_abs] using (hqsum.sub hsummable).norm
  have htailAbs :
      (∑' j : {j : ℤ // j ∉ F}, |q j - p j|) = 1 - r := by
    calc
      _ = ∑' j : {j : ℤ // j ∉ F}, p j := by
        apply tsum_congr
        intro j
        have hnot' : ¬ (0 ≤ j.1 ∧ j.1 ≤ (m : ℤ)) := by
          simpa [F, Finset.mem_Icc] using j.2
        have hqzero : q j.1 = 0 := by
          simp [q, gaussianizedBlockIntProbability, hnot']
        rw [hqzero]
        simp [abs_of_nonneg (hpnonneg j.1)]
      _ = 1 - r := htail
  calc
    _ = (∑ j ∈ F, |q j - p j|) +
        (∑' j : {j : ℤ // j ∉ F}, |q j - p j|) := by
      rw [← habs.sum_add_tsum_subtype_compl F]
    _ = (1 - r) + (1 - r) := by rw [hfinite, htailAbs]
    _ = 2 * (1 - r) := by ring

end Critical2DKPZ.SHF.Moments

end
