/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationReplicaEndpointAverage
import Mathlib.Tactic

/-! # Positive-duration terminal averaging -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.Polymer

/-- A nonnegative product profile supported in a scaled ball is dominated by
an average over strictly positive common walk durations. The positive shift
lets the average feed directly into a CCR boundary vector, whose duration
index starts at one. -/
theorem replicaTerminalProfile_le_positiveWalkHorizonAverage {h N : ℕ}
    (hN : 0 < N) (R M : ℝ) (hM : 0 ≤ M) (f : Fin h → Site → ℝ)
    (hnonneg : ∀ i y, 0 ≤ f i y)
    (hbound : ∀ i y,
      ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane y‖ ≤ R → f i y ≤ M)
    (hzero : ∀ i y,
      ¬ ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane y‖ ≤ R → f i y = 0) :
    ∀ y : Fin h → Site,
      (∏ i, f i (y i)) ≤
        (((2 : ℝ) ^ h) * M ^ h / N) *
          ∑ k ∈ Finset.range N,
            ∑ z ∈ Fintype.piFinset (fun i => endpoints (y i) (k + 1)),
              (if ∀ i,
                    ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2 then
                ∏ i, srwKernel (k + 1) (z i - y i) else 0) := by
  classical
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  let inside : Site → Prop := fun z =>
    ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ≤ R
  let p : ℝ := (1 / 2 : ℝ) ^ h
  let C : ℝ := ((2 : ℝ) ^ h) * M ^ h / N
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpow : ((2 : ℝ) ^ h) * (1 / 2 : ℝ) ^ h = 1 := by
    rw [← mul_pow]
    norm_num
  have hbase : C * ((N : ℝ) * p) = M ^ h := by
    dsimp [C, p]
    calc
      (((2 : ℝ) ^ h) * M ^ h / N) * ((N : ℝ) * (1 / 2 : ℝ) ^ h) =
          (((2 : ℝ) ^ h) * M ^ h) * (1 / 2 : ℝ) ^ h := by
            field_simp [ne_of_gt hNreal]
      _ = M ^ h := by
        calc
          (((2 : ℝ) ^ h) * M ^ h) * (1 / 2 : ℝ) ^ h =
              (((2 : ℝ) ^ h) * (1 / 2 : ℝ) ^ h) * M ^ h := by ring
          _ = M ^ h := by rw [hpow]; ring
  have hsumLower (y : Fin h → Site) (hy : ∀ i, inside (y i)) :
      (N : ℝ) * p ≤
        ∑ k ∈ Finset.range N,
          ∑ z ∈ Fintype.piFinset (fun i => endpoints (y i) (k + 1)),
            (if ∀ i,
                  ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2 then
              ∏ i, srwKernel (k + 1) (z i - y i) else 0) := by
    calc
      (N : ℝ) * p = ∑ _k ∈ Finset.range N, p := by simp [p]
      _ ≤ ∑ k ∈ Finset.range N,
          ∑ z ∈ Fintype.piFinset (fun i => endpoints (y i) (k + 1)),
            (if ∀ i,
                  ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2 then
              ∏ i, srwKernel (k + 1) (z i - y i) else 0) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkN : k + 1 ≤ N := by
          have hk' := Finset.mem_range.mp hk
          omega
        simpa [p, inside] using
          replicaEndpointInside_ball_ge hN hkN y R (fun i => hy i)
  have hsumNonneg (y : Fin h → Site) :
      0 ≤ ∑ k ∈ Finset.range N,
        ∑ z ∈ Fintype.piFinset (fun i => endpoints (y i) (k + 1)),
          (if ∀ i,
                ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2 then
            ∏ i, srwKernel (k + 1) (z i - y i) else 0) := by
    apply Finset.sum_nonneg
    intro k hk
    apply Finset.sum_nonneg
    intro z hz
    split_ifs with hzInside
    · exact Finset.prod_nonneg (fun i hi => kernel_nonneg (k + 1) (z i - y i))
    · exact le_rfl
  intro y
  by_cases hy : ∀ i, inside (y i)
  · have hprofile : (∏ i, f i (y i)) ≤ M ^ h := by
      calc
        (∏ i, f i (y i)) ≤ ∏ _i : Fin h, M :=
          Finset.prod_le_prod₀
            (fun i hi => hnonneg i (y i))
            (fun i hi => hbound i (y i) (hy i))
        _ = M ^ h := by simp
    have hmajor : M ^ h ≤ C *
        (∑ k ∈ Finset.range N,
          ∑ z ∈ Fintype.piFinset (fun i => endpoints (y i) (k + 1)),
            (if ∀ i,
                  ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2 then
              ∏ i, srwKernel (k + 1) (z i - y i) else 0)) := by
      calc
        M ^ h = C * ((N : ℝ) * p) := hbase.symm
        _ ≤ C * _ := mul_le_mul_of_nonneg_left (hsumLower y hy) hC
    exact hprofile.trans hmajor
  · obtain ⟨i, hi⟩ := not_forall.mp hy
    have hprofile : (∏ i, f i (y i)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hzero i (y i) hi
    rw [hprofile]
    exact mul_nonneg hC (hsumNonneg y)

end Critical2DKPZ.SHF.Moments

end
