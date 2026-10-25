/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Endpoints
public import Critical2DKPZ.Polymer.WalkKernel
public import Critical2DKPZ.MomentBounds.CSZ25ReturnWeights
public import Critical2DKPZ.RandomWalk.Estimates
public import Critical2DKPZ.RandomWalk.KernelBridge
import Mathlib.Tactic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Exponential moments of the planar walk kernel -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

private theorem tsum_exp_mul_coord_srwKernel_eq (n : ℕ) (a : Fin 2) (t : ℝ) :
    ∑' z : Site, Real.exp (t * (z a : ℝ)) * srwKernel n z =
      (((Real.exp t + Real.exp (-t) + 2) / 4) ^ n) := by
  let E := Polymer.endpoints (0 : Site) n
  have hsupp : ∀ z ∉ E, Real.exp (t * (z a : ℝ)) * srwKernel n z = 0 := by
    intro z hz
    have h := Polymer.srwKernel_eq_zero_of_not_mem n 0 z hz
    have h' : srwKernel n z = 0 := by simpa only [sub_zero] using h
    simp [h']
  have hend (s : Fin n → Fin 4) : walkPosition 0 s n ∈ E := by
    exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
  have hpath :
      (∑ z ∈ E, Real.exp (t * (z a : ℝ)) *
        ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
          if walkPosition 0 s n = z then 1 else 0) =
        (4 : ℝ)⁻¹ ^ n *
          ∑ s : Fin n → Fin 4, ∏ i : Fin n,
            Real.exp (t * (srwStep (s i) a : ℝ)) := by
    calc
      _ = ∑ z ∈ E, Real.exp (t * (z a : ℝ)) *
          ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
            if walkPosition 0 s n = z then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        have heq : srwKernel n z =
            ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
              if walkPosition 0 s n = z then 1 else 0 := by
          simpa only [sub_zero] using (Polymer.srwKernel_eq_sum n 0 z)
        rfl
      _ = ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
          Real.exp (t * (walkPosition 0 s n a : ℝ)) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s hs
        have hselect :
            ∑ z ∈ E, Real.exp (t * (z a : ℝ)) * ((4 : ℝ)⁻¹ ^ n) *
              (if walkPosition 0 s n = z then 1 else 0) =
              Real.exp (t * (walkPosition 0 s n a : ℝ)) * (4 : ℝ)⁻¹ ^ n := by
          simp [hend s, mul_comm]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hselect
      _ = (4 : ℝ)⁻¹ ^ n *
          ∑ s : Fin n → Fin 4, ∏ i : Fin n,
            Real.exp (t * (srwStep (s i) a : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        have hcoord : (walkPosition 0 s n a : ℝ) =
            ∑ i : Fin n, (srwStep (s i) a : ℝ) := by
          have h := congrArg (fun w : Site => (w a : ℝ)) (walkPosition_endpoint s)
          simpa only [Pi.zero_apply, Int.cast_zero, zero_add, Finset.sum_apply,
            Int.cast_sum] using h
        rw [hcoord]
        have harg : t * ∑ i : Fin n, (srwStep (s i) a : ℝ) =
            ∑ i : Fin n, t * (srwStep (s i) a : ℝ) := by rw [Finset.mul_sum]
        rw [harg, Real.exp_sum]
  have hstep :
      (∑ b : Fin 4, Real.exp (t * (srwStep b a : ℝ))) =
        Real.exp t + Real.exp (-t) + 2 := by
    fin_cases a <;> norm_num [srwStep, Fin.sum_univ_four] <;> ring_nf
  have hkernel :
      (∑ z ∈ E, Real.exp (t * (z a : ℝ)) * srwKernel n z) =
        ∑ z ∈ E, Real.exp (t * (z a : ℝ)) *
          ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
            (if walkPosition 0 s n = z then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro z hz
    have heq : srwKernel n z =
        ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
          (if walkPosition 0 s n = z then 1 else 0) := by
      simpa only [sub_zero] using Polymer.srwKernel_eq_sum n 0 z
    rw [heq]
  calc
    ∑' z : Site, Real.exp (t * (z a : ℝ)) * srwKernel n z =
        ∑ z ∈ E, Real.exp (t * (z a : ℝ)) * srwKernel n z := tsum_eq_sum hsupp
    _ = ∑ z ∈ E, Real.exp (t * (z a : ℝ)) *
          ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
            (if walkPosition 0 s n = z then 1 else 0) := hkernel
    _ = (4 : ℝ)⁻¹ ^ n *
          ∑ s : Fin n → Fin 4, ∏ i : Fin n,
            Real.exp (t * (srwStep (s i) a : ℝ)) := hpath
    _ = ((∑ b : Fin 4, Real.exp (t * (srwStep b a : ℝ))) / 4) ^ n := by
      have hpow : (∑ b : Fin 4, Real.exp (t * (srwStep b a : ℝ))) ^ n =
          ∑ s : Fin n → Fin 4, ∏ i : Fin n, Real.exp (t * (srwStep (s i) a : ℝ)) :=
        Fintype.sum_pow _ _
      rw [← hpow, ← mul_pow]
      congr 1
      simp [div_eq_mul_inv, mul_comm]
    _ = ((Real.exp t + Real.exp (-t) + 2) / 4) ^ n := by rw [hstep]

private theorem endpoints_neg_mem (n : ℕ) (z : Site) :
    z ∈ Polymer.endpoints 0 n ↔ -z ∈ Polymer.endpoints 0 n := by
  have hforward : ∀ z ∈ Polymer.endpoints 0 n, -z ∈ Polymer.endpoints 0 n := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨s, -, hs⟩
    apply Finset.mem_image.mpr
    refine ⟨fun i => Polymer.oppositeStep (s i), Finset.mem_univ _, ?_⟩
    rw [Polymer.walkPosition_opposite, ← hs]
  constructor
  · exact hforward z
  · intro hz
    have h := hforward (-z) hz
    simpa using h

private theorem finite_exp_mul_even_eq_cosh (n : ℕ) (a : Fin 2) (t : ℝ)
    (f : Site → ℝ) (hf : ∀ z, f (-z) = f z) :
    (∑ z ∈ Polymer.endpoints 0 n, Real.exp (t * (z a : ℝ)) * f z) =
      ∑ z ∈ Polymer.endpoints 0 n, Real.cosh (t * (z a : ℝ)) * f z := by
  let E := Polymer.endpoints (0 : Site) n
  have hneg :
      (∑ z ∈ E, Real.exp (t * (z a : ℝ)) * f z) =
        ∑ z ∈ E, Real.exp (-t * (z a : ℝ)) * f z := by
    apply Finset.sum_equiv (Equiv.neg Site)
    · intro z
      exact endpoints_neg_mem n z
    · intro z hz
      rw [← hf z]
      congr 1
      congr 1
      simp only [Equiv.neg_apply, Pi.neg_apply, Int.cast_neg]
      ring
  have hadd :
      (∑ z ∈ E, Real.exp (t * (z a : ℝ)) * f z) +
        ∑ z ∈ E, Real.exp (-t * (z a : ℝ)) * f z =
          2 * ∑ z ∈ E, Real.cosh (t * (z a : ℝ)) * f z := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ z ∈ E, (Real.exp (t * (z a : ℝ)) * f z +
          Real.exp (-t * (z a : ℝ)) * f z)) =
          ∑ z ∈ E, (Real.exp (t * (z a : ℝ)) + Real.exp (-t * (z a : ℝ))) * f z := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _ = ∑ z ∈ E, (2 * Real.cosh (t * (z a : ℝ))) * f z := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [Real.cosh_eq]
        rw [show -t * (z a : ℝ) = -(t * (z a : ℝ)) by ring]
        field_simp
      _ = ∑ z ∈ E, 2 * (Real.cosh (t * (z a : ℝ)) * f z) := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _ = 2 * ∑ z ∈ E, Real.cosh (t * (z a : ℝ)) * f z := by
        rw [Finset.mul_sum]
  calc
    _ = ((∑ z ∈ E, Real.exp (t * (z a : ℝ)) * f z) +
        ∑ z ∈ E, Real.exp (-t * (z a : ℝ)) * f z) / 2 := by rw [hneg]; ring
    _ = _ := by rw [hadd]; ring

private theorem one_add_mul_exp_sub_one_le (C y : ℝ) (hC : 1 ≤ C) :
    1 + C * (Real.exp y - 1) ≤ Real.exp (C * y) := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let w := 1 / C
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp [w]
    rw [div_le_iff₀ hCpos]
    linarith
  have hmix : w * (C * y) + (1 - w) * 0 = y := by
    dsimp [w]
    field_simp
    ring
  have hconv := convexOn_exp.2 (Set.mem_univ (C * y)) (Set.mem_univ (0 : ℝ))
    hw0 (sub_nonneg.mpr hw1) (by dsimp [w]; ring)
  have hcv : Real.exp y ≤ w * Real.exp (C * y) + (1 - w) := by
    simpa only [smul_eq_mul, hmix, Real.exp_zero, mul_one] using hconv
  have hmul := mul_le_mul_of_nonneg_left hcv hCpos.le
  have hwC : C * w = 1 := by dsimp [w]; field_simp
  have hrest : C * (1 - w) = C - 1 := by rw [mul_sub, mul_one, hwC]
  have hmul' : C * Real.exp y ≤ Real.exp (C * y) + C - 1 := by
    calc
      C * Real.exp y ≤ C * (w * Real.exp (C * y) + (1 - w)) := hmul
      _ = Real.exp (C * y) + C - 1 := by
        rw [mul_add, ← mul_assoc, hwC, hrest]
        ring
  nlinarith [hmul']

private theorem srwKernel_le_return_mul :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : Site,
      srwKernel n z ≤ C * srwKernel (2 * n) 0 := by
  obtain ⟨CG, cG, hcG, hG⟩ := srwKernel_gaussianBound
  obtain ⟨aLo, aHi, haLo, _, hret⟩ := srwKernel_two_mul_zero_bounds
  have hCG : 0 ≤ CG := by
    have hgb := hG 2 (by omega) 0
    have hq : 0 < srwKernel 2 0 := srwKernel_two_zero_pos
    have hfactor : 0 < Real.exp (-cG * ‖siteToPlane (0 : Site)‖ ^ 2 / 2) / 2 := by
      positivity
    have hnonneg : 0 ≤ CG *
        (Real.exp (-cG * ‖siteToPlane (0 : Site)‖ ^ 2 / 2) / 2) := by
      have hh : 0 ≤ CG / 2 *
          Real.exp (-cG * ‖siteToPlane (0 : Site)‖ ^ 2 / 2) := hq.le.trans hgb
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
    by_contra hnot
    have hneg : CG < 0 := lt_of_not_ge hnot
    exact (not_lt_of_ge hnonneg) (mul_neg_of_neg_of_pos hneg hfactor)
  let C := max 1 (CG / aLo)
  refine ⟨C, le_max_left _ _, fun n hn z => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have harg : -cG * ‖siteToPlane z‖ ^ 2 / n ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    · exact_mod_cast (show 0 ≤ n by omega)
  have hexp : Real.exp (-cG * ‖siteToPlane z‖ ^ 2 / n) ≤ 1 :=
    Real.exp_le_one_iff.mpr harg
  have hgauss := hG n hn z
  have hqbound : srwKernel n z ≤ CG / n := by
    calc
      srwKernel n z ≤ CG / n * Real.exp (-cG * ‖siteToPlane z‖ ^ 2 / n) := hgauss
      _ ≤ CG / n := by
        simpa using mul_le_mul_of_nonneg_left hexp (div_nonneg hCG hnR.le)
  have hmiddle : CG / n ≤ (CG / aLo) * (aLo / n) := by
    field_simp [ne_of_gt haLo, ne_of_gt hnR]
    exact le_rfl
  have hratio : 0 ≤ CG / aLo := div_nonneg hCG haLo.le
  calc
    srwKernel n z ≤ CG / n := hqbound
    _ ≤ (CG / aLo) * (aLo / n) := hmiddle
    _ ≤ (CG / aLo) * srwKernel (2 * n) 0 :=
      mul_le_mul_of_nonneg_left (hret n hn).1 hratio
    _ ≤ C * srwKernel (2 * n) 0 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (srwKernel_nonneg _ _)

private theorem tsum_exp_mul_coord_srwKernel_first_le :
    ∀ t : ℝ, ∀ a : Fin 2, ∀ n : ℕ,
      ∑' x : Site, Real.exp (t * (x a : ℝ)) * srwKernel n x ≤
        Real.exp (t ^ 2 * n / 2) := by
  intro t a n
  rw [tsum_exp_mul_coord_srwKernel_eq]
  have hbase :
      (Real.exp t + Real.exp (-t) + 2) / 4 = Real.cosh (t / 2) ^ 2 := by
    calc
      (Real.exp t + Real.exp (-t) + 2) / 4 =
          (Real.exp (t / 2) ^ 2 + Real.exp (-(t / 2)) ^ 2 + 2) / 4 := by
        have ht : Real.exp t = Real.exp (t / 2) ^ 2 := by
          rw [show t = t / 2 + t / 2 by ring, Real.exp_add]
          ring_nf
        have hnt : Real.exp (-t) = Real.exp (-(t / 2)) ^ 2 := by
          rw [show -t = -(t / 2) + -(t / 2) by ring, Real.exp_add]
          ring_nf
        rw [ht, hnt]
      _ = ((Real.exp (t / 2) + Real.exp (-(t / 2))) / 2) ^ 2 := by
        have hcross : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by
          rw [← Real.exp_add]
          simp
        have hcross2 : 2 * Real.exp (t / 2) * Real.exp (-(t / 2)) = 2 := by
          calc
            2 * Real.exp (t / 2) * Real.exp (-(t / 2)) =
                2 * (Real.exp (t / 2) * Real.exp (-(t / 2)) : ℝ) := by ring
            _ = 2 := by rw [hcross]; ring
        have hsumSq : (Real.exp (t / 2) + Real.exp (-(t / 2))) ^ 2 =
            Real.exp (t / 2) ^ 2 + Real.exp (-(t / 2)) ^ 2 + 2 := by
          rw [add_sq, hcross2]
          ring
        rw [div_pow, hsumSq]
        field_simp
        ring
      _ = Real.cosh (t / 2) ^ 2 := by rw [Real.cosh_eq]
  rw [hbase]
  have hcosh : Real.cosh (t / 2) ^ 2 ≤ Real.exp ((t / 2) ^ 2) := by
    have h := Real.cosh_le_exp_half_sq (t / 2)
    have hc : 0 ≤ Real.cosh (t / 2) := (Real.cosh_pos _).le
    have he : 0 ≤ Real.exp ((t / 2) ^ 2 / 2) := (Real.exp_pos _).le
    have hdiff : 0 ≤ Real.exp ((t / 2) ^ 2 / 2) - Real.cosh (t / 2) := sub_nonneg.mpr h
    have hsum : 0 ≤ Real.exp ((t / 2) ^ 2 / 2) + Real.cosh (t / 2) := add_nonneg he hc
    have hmul := mul_nonneg hdiff hsum
    have hexpSq : Real.exp ((t / 2) ^ 2 / 2) ^ 2 = Real.exp ((t / 2) ^ 2) := by
      calc
        Real.exp ((t / 2) ^ 2 / 2) ^ 2 =
            Real.exp (2 * ((t / 2) ^ 2 / 2)) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp ((t / 2) ^ 2) := by
          congr 1
          ring
    nlinarith [hmul, hexpSq]
  calc
    (Real.cosh (t / 2) ^ 2) ^ n ≤ Real.exp ((t / 2) ^ 2) ^ n := by
      exact pow_le_pow_left₀ (sq_nonneg _) hcosh n
    _ = Real.exp ((n : ℝ) * t ^ 2 / 4) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (t ^ 2 * n / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg t)]


/-- Exponential moments of the planar walk and its squared kernel. -/
theorem tsum_exp_mul_coord_srwKernel_le :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ t : ℝ, ∀ a : Fin 2, ∀ n : ℕ,
      (∑' x : Site, Real.exp (t * (x a : ℝ)) * srwKernel n x ≤
          Real.exp (c * t ^ 2 * n / 2)) ∧
      (∑' x : Site, Real.exp (t * (x a : ℝ)) * srwKernel n x ^ 2 ≤
          Real.exp (c * t ^ 2 * n / 2) * srwKernel (2 * n) 0) := by
  obtain ⟨C, hC, hcompare⟩ := srwKernel_le_return_mul
  refine ⟨C, hC, fun t a n => ?_⟩
  constructor
  · have hfirst := tsum_exp_mul_coord_srwKernel_first_le t a n
    apply hfirst.trans
    apply Real.exp_le_exp.mpr
    have hfac : 0 ≤ t ^ 2 * n / 2 := by positivity
    calc
      t ^ 2 * n / 2 = 1 * (t ^ 2 * n / 2) := by ring
      _ ≤ C * (t ^ 2 * n / 2) := mul_le_mul_of_nonneg_right hC hfac
      _ = C * t ^ 2 * n / 2 := by ring
  · let E := Polymer.endpoints (0 : Site) n
    let M := ∑' z : Site, Real.exp (t * (z a : ℝ)) * srwKernel n z
    have hfiniteQ : M =
        ∑ z ∈ E, Real.exp (t * (z a : ℝ)) * srwKernel n z := by
      dsimp [M]
      apply tsum_eq_sum
      intro z hz
      have h := Polymer.srwKernel_eq_zero_of_not_mem n 0 z hz
      have hq : srwKernel n z = 0 := by simpa only [sub_zero] using h
      simp [hq]
    have hfiniteQ2 :
        (∑' z : Site, srwKernel n z ^ 2) = ∑ z ∈ E, srwKernel n z ^ 2 := by
      apply tsum_eq_sum
      intro z hz
      have h := Polymer.srwKernel_eq_zero_of_not_mem n 0 z hz
      have hq : srwKernel n z = 0 := by simpa only [sub_zero] using h
      simp [hq]
    have hfiniteExpQ2 :
        (∑' z : Site, Real.exp (t * (z a : ℝ)) * srwKernel n z ^ 2) =
          ∑ z ∈ E, Real.exp (t * (z a : ℝ)) * srwKernel n z ^ 2 := by
      apply tsum_eq_sum
      intro z hz
      have h := Polymer.srwKernel_eq_zero_of_not_mem n 0 z hz
      have hq : srwKernel n z = 0 := by simpa only [sub_zero] using h
      simp [hq]
    have hsumQ : (∑ z ∈ E, srwKernel n z) = 1 := by
      simpa only [sub_zero] using Polymer.sum_srwKernel_endpoints n 0
    have hreturn : (∑ z ∈ E, srwKernel n z ^ 2) = srwKernel (2 * n) 0 := by
      calc
        _ = ∑' z : Site, srwKernel n z ^ 2 := hfiniteQ2.symm
        _ = srwKernel (2 * n) 0 := by
          simpa [pow_two, sub_zero] using Polymer.srwKernel_collision n 0 0
    have hcoshQ :
        (∑ z ∈ E, Real.cosh (t * (z a : ℝ)) * srwKernel n z) = M := by
      calc
        _ = ∑ z ∈ E, Real.exp (t * (z a : ℝ)) * srwKernel n z :=
          (finite_exp_mul_even_eq_cosh n a t (fun z => srwKernel n z)
            (fun z => Polymer.srwKernel_neg n z)).symm
        _ = M := hfiniteQ.symm
    have hcoshQ2 :
        (∑ z ∈ E, Real.cosh (t * (z a : ℝ)) * srwKernel n z ^ 2) =
          ∑ z ∈ E, srwKernel n z ^ 2 +
            ∑ z ∈ E, (Real.cosh (t * (z a : ℝ)) - 1) * srwKernel n z ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    have hcoshQsub :
        (∑ z ∈ E, (Real.cosh (t * (z a : ℝ)) - 1) * srwKernel n z) = M - 1 := by
      calc
        _ = (∑ z ∈ E, Real.cosh (t * (z a : ℝ)) * srwKernel n z) -
              ∑ z ∈ E, srwKernel n z := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro z hz
          ring
        _ = M - 1 := by rw [hcoshQ, hsumQ]
    by_cases hn0 : n = 0
    · subst n
      have hE : Polymer.endpoints (0 : Site) 0 = {0} := by
        ext z
        simp [Polymer.endpoints, walkPosition]
      have hE' : E = {0} := by simpa [E] using hE
      rw [hfiniteExpQ2, hE']
      simp [srwKernel_zero]
    · have hn : 1 ≤ n := by omega
      let R := srwKernel (2 * n) 0
      have hRnonneg : 0 ≤ R := srwKernel_nonneg _ _
      have hcomp (z : Site) : srwKernel n z ≤ C * R := by
        simpa [R] using hcompare n hn z
      have hsq (z : Site) : srwKernel n z ^ 2 ≤ C * R * srwKernel n z := by
        calc
          srwKernel n z ^ 2 = srwKernel n z * srwKernel n z := by ring
          _ ≤ (C * R) * srwKernel n z :=
            mul_le_mul_of_nonneg_right (hcomp z) (srwKernel_nonneg _ _)
      have hcorrection :
          (∑ z ∈ E, (Real.cosh (t * (z a : ℝ)) - 1) * srwKernel n z ^ 2) ≤
            C * R * (M - 1) := by
        calc
          _ ≤ ∑ z ∈ E, (C * R) *
              ((Real.cosh (t * (z a : ℝ)) - 1) * srwKernel n z) := by
            apply Finset.sum_le_sum
            intro z hz
            have hcosh : 0 ≤ Real.cosh (t * (z a : ℝ)) - 1 :=
              sub_nonneg.mpr (Real.one_le_cosh _)
            have hmul := mul_le_mul_of_nonneg_left (hsq z) hcosh
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
          _ = C * R * (∑ z ∈ E,
                (Real.cosh (t * (z a : ℝ)) - 1) * srwKernel n z) := by
            rw [Finset.mul_sum]
          _ = C * R * (M - 1) := by rw [hcoshQsub]
      have hmgf : M ≤ Real.exp (t ^ 2 * n / 2) := by
        dsimp [M]
        exact tsum_exp_mul_coord_srwKernel_first_le t a n
      have hcorrUpper :
          C * R * (M - 1) ≤ C * R * (Real.exp (t ^ 2 * n / 2) - 1) := by
        apply mul_le_mul_of_nonneg_left
        · linarith [hmgf]
        · exact mul_nonneg (le_trans (by norm_num) hC) hRnonneg
      have htotal :
          (∑ z ∈ E, Real.cosh (t * (z a : ℝ)) * srwKernel n z ^ 2) ≤
            R * (1 + C * (Real.exp (t ^ 2 * n / 2) - 1)) := by
        rw [hcoshQ2, hreturn]
        calc
          R + ∑ z ∈ E, (Real.cosh (t * (z a : ℝ)) - 1) * srwKernel n z ^ 2 ≤
              R + C * R * (M - 1) := add_le_add le_rfl hcorrection
          _ ≤ R + C * R * (Real.exp (t ^ 2 * n / 2) - 1) :=
            add_le_add le_rfl hcorrUpper
          _ = R * (1 + C * (Real.exp (t ^ 2 * n / 2) - 1)) := by ring
      calc
        (∑' z : Site, Real.exp (t * (z a : ℝ)) * srwKernel n z ^ 2) =
            ∑ z ∈ E, Real.exp (t * (z a : ℝ)) * srwKernel n z ^ 2 := hfiniteExpQ2
        _ = ∑ z ∈ E, Real.cosh (t * (z a : ℝ)) * srwKernel n z ^ 2 :=
          finite_exp_mul_even_eq_cosh n a t (fun z => srwKernel n z ^ 2)
            (fun z => by simp [Polymer.srwKernel_neg])
        _ ≤ R * (1 + C * (Real.exp (t ^ 2 * n / 2) - 1)) := htotal
        _ ≤ R * Real.exp (C * (t ^ 2 * n / 2)) := by
          exact mul_le_mul_of_nonneg_left
            (one_add_mul_exp_sub_one_le C (t ^ 2 * n / 2) hC)
            hRnonneg
        _ = Real.exp (C * t ^ 2 * n / 2) * srwKernel (2 * n) 0 := by
          rw [show C * (t ^ 2 * n / 2) = C * t ^ 2 * n / 2 by ring]
          simp only [R]
          ring


end Critical2DKPZ.MomentBounds

end
