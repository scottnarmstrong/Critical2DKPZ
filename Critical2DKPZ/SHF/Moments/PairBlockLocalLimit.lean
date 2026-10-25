/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.SpatialRenewal
public import Critical2DKPZ.Renewal.CriticalWindow
public import Critical2DKPZ.Renewal.LocalLimit
import Mathlib.Tactic

/-! # Support and mass of pair-block renewals -/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

private theorem endpoints_compose {u z x : Site} {m r : ℕ}
    (hz : z ∈ Polymer.endpoints u m) (hx : x ∈ Polymer.endpoints z r) :
    x ∈ Polymer.endpoints u (m + r) := by
  obtain ⟨p, hp⟩ := (Polymer.mem_endpoints_iff u z m).mp hz
  obtain ⟨q, hq⟩ := (Polymer.mem_endpoints_iff z x r).mp hx
  apply (Polymer.mem_endpoints_iff u x (m + r)).mpr
  refine ⟨Fin.append p q, ?_⟩
  rw [Polymer.walkPosition_append_end, hp]
  exact hq

/-- A pair-block spatial renewal is supported on the ordinary walk endpoints. -/
theorem spatialRenewal_eq_zero_of_not_mem_endpoints (σ2 : ℝ) :
    ∀ n : ℕ, ∀ x : Site, x ∉ Polymer.endpoints 0 n →
      Collision.spatialRenewal σ2 n x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x hx
      cases n with
      | zero =>
          have hzero : (0 : Site) ∈ Polymer.endpoints 0 0 := by
            apply (Polymer.mem_endpoints_iff 0 0 0).mpr
            exact ⟨Fin.elim0, by simp [Polymer.walkPosition_zero]⟩
          simp only [Collision.spatialRenewal_zero]
          split_ifs with h
          · exact False.elim (hx (by simpa only [h] using hzero))
          · rfl
      | succ k =>
          rw [Collision.spatialRenewal_succ]
          apply Finset.sum_eq_zero
          intro m hm
          have hterm (z : Site) :
              Collision.spatialRenewal σ2 m.val z * σ2 *
                srwKernel (k + 1 - m.val) (x - z) ^ 2 = 0 := by
            by_cases hz : z ∈ Polymer.endpoints 0 m.val
            · have hnot : x ∉ Polymer.endpoints z (k + 1 - m.val) := by
                intro hmem
                have hcomp := endpoints_compose hz hmem
                have htime : m.val + (k + 1 - m.val) = k + 1 := by
                  exact Nat.add_sub_of_le (Nat.le_of_lt m.isLt)
                exact hx (htime ▸ hcomp)
              rw [Polymer.srwKernel_eq_zero_of_not_mem
                (k + 1 - m.val) z x hnot]
              ring
            · rw [ih m.val (by have := m.isLt; omega) z hz]
              ring
          calc
            _ = ∑' z : Site, (0 : ℝ) := by
              apply tsum_congr
              exact hterm
            _ = 0 := by simp

private theorem tsum_sq_srwKernel (r : ℕ) (z : Site) :
    ∑' x : Site, srwKernel r (x - z) ^ 2 = Renewal.returnWeight r := by
  calc
    _ = ∑' x : Site, srwKernel r (x - z) * srwKernel r (x - z) := by
      apply tsum_congr
      intro x
      ring
    _ = srwKernel (2 * r) 0 := by
      simpa only [sub_self] using Polymer.srwKernel_collision r z z
    _ = Renewal.returnWeight r := rfl

private theorem sum_sq_srwKernel_baseEndpoints {n m : ℕ} (hm : m < n)
    {z : Site} (hz : z ∈ Polymer.endpoints 0 m) :
    (∑ x ∈ Polymer.endpoints 0 n, srwKernel (n - m) (x - z) ^ 2) =
      Renewal.returnWeight (n - m) := by
  have hsum :
      (∑ x ∈ Polymer.endpoints 0 n, srwKernel (n - m) (x - z) ^ 2) =
        ∑' x : Site, srwKernel (n - m) (x - z) ^ 2 := by
    symm
    apply tsum_eq_sum
    intro x hx
    have hnot : x ∉ Polymer.endpoints z (n - m) := by
      intro hx'
      have hcomp := endpoints_compose hz hx'
      have htime : m + (n - m) = n := Nat.add_sub_of_le (Nat.le_of_lt hm)
      exact hx (htime ▸ hcomp)
    rw [Polymer.srwKernel_eq_zero_of_not_mem (n - m) z x hnot]
    ring
  rw [hsum, tsum_sq_srwKernel]

private theorem sum_Icc_one_succ_eq_fin {n : ℕ} (f : ℕ → ℝ) :
    ∑ r ∈ Finset.Icc 1 (n + 1), f r = ∑ m : Fin (n + 1), f (n + 1 - m.val) := by
  classical
  refine Finset.sum_bij (fun r hr => ⟨n + 1 - r, ?_⟩) ?_ ?_ ?_ ?_
  · have hr := Finset.mem_Icc.mp hr
    omega
  · intro r hr
    simp
  · intro r₁ hr₁ r₂ hr₂ heq
    have hr₁' : r₁ ≤ n + 1 := (Finset.mem_Icc.mp hr₁).2
    have hr₂' : r₂ ≤ n + 1 := (Finset.mem_Icc.mp hr₂).2
    have hval : n + 1 - r₁ = n + 1 - r₂ := congrArg Fin.val heq
    exact (tsub_right_inj hr₁' hr₂').mp hval
  · intro m hm
    refine ⟨n + 1 - m.val, ?_, ?_⟩
    · have hm' := m.isLt
      simp only [Finset.mem_Icc]
      omega
    · apply Fin.ext
      change n + 1 - (n + 1 - m.val) = m.val
      exact Nat.sub_sub_self (by omega)
  · intro r hr
    have hrle : r ≤ n + 1 := (Finset.mem_Icc.mp hr).2
    change f r = f (n + 1 - (n + 1 - r))
    congr 1
    exact (Nat.sub_sub_self hrle).symm

/-- The total spatial mass of a pair-block renewal is the scalar renewal mass. -/
theorem tsum_spatialRenewal_eq_renewalMass (σ2 : ℝ) (n : ℕ) :
    ∑' x : Site, Collision.spatialRenewal σ2 n x =
      Renewal.renewalMass (fun r => σ2 * Renewal.returnWeight r) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [Collision.spatialRenewal_zero, Renewal.renewalMass_zero, tsum_ite_eq]
      | succ k =>
          let E := Polymer.endpoints (0 : Site) (k + 1)
          have hmass_support :
              ∑' x : Site, Collision.spatialRenewal σ2 (k + 1) x =
                ∑ x ∈ E, Collision.spatialRenewal σ2 (k + 1) x := by
            apply tsum_eq_sum
            intro x hx
            exact spatialRenewal_eq_zero_of_not_mem_endpoints σ2 (k + 1) x
              (by simpa [E] using hx)
          rw [hmass_support]
          calc
            _ = ∑ x ∈ E, ∑ m : Fin (k + 1), ∑' z : Site,
                  Collision.spatialRenewal σ2 m.val z * σ2 *
                    srwKernel (k + 1 - m.val) (x - z) ^ 2 := by
              apply Finset.sum_congr rfl
              intro x hx
              exact Collision.spatialRenewal_succ σ2 k x
            _ = ∑ m : Fin (k + 1), ∑ x ∈ E, ∑' z : Site,
                  Collision.spatialRenewal σ2 m.val z * σ2 *
                    srwKernel (k + 1 - m.val) (x - z) ^ 2 := by
              rw [Finset.sum_comm]
            _ = ∑ m : Fin (k + 1), ∑ x ∈ E, ∑ z ∈ Polymer.endpoints 0 m.val,
                  Collision.spatialRenewal σ2 m.val z * σ2 *
                    srwKernel (k + 1 - m.val) (x - z) ^ 2 := by
              apply Finset.sum_congr rfl
              intro m hm
              apply Finset.sum_congr rfl
              intro x hx
              apply tsum_eq_sum
              intro z hz
              rw [spatialRenewal_eq_zero_of_not_mem_endpoints σ2 m.val z hz]
              ring
            _ = ∑ m : Fin (k + 1), ∑ z ∈ Polymer.endpoints 0 m.val, ∑ x ∈ E,
                  Collision.spatialRenewal σ2 m.val z * σ2 *
                    srwKernel (k + 1 - m.val) (x - z) ^ 2 := by
              apply Finset.sum_congr rfl
              intro m hm
              rw [Finset.sum_comm]
            _ = ∑ m : Fin (k + 1), ∑ z ∈ Polymer.endpoints 0 m.val,
                  Collision.spatialRenewal σ2 m.val z * σ2 *
                    Renewal.returnWeight (k + 1 - m.val) := by
              apply Finset.sum_congr rfl
              intro m hm
              apply Finset.sum_congr rfl
              intro z hz
              have hq := sum_sq_srwKernel_baseEndpoints
                (n := k + 1) (m := m.val) (by have := m.isLt; omega) hz
              calc
                _ = ∑ x ∈ E, (Collision.spatialRenewal σ2 m.val z * σ2) *
                    srwKernel (k + 1 - m.val) (x - z) ^ 2 := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  ring
                _ = (Collision.spatialRenewal σ2 m.val z * σ2) *
                    (∑ x ∈ E, srwKernel (k + 1 - m.val) (x - z) ^ 2) := by
                  rw [← Finset.mul_sum]
                _ = Collision.spatialRenewal σ2 m.val z * σ2 *
                    Renewal.returnWeight (k + 1 - m.val) := by
                  rw [show (∑ x ∈ E, srwKernel (k + 1 - m.val) (x - z) ^ 2) =
                    Renewal.returnWeight (k + 1 - m.val) by simpa only [E] using hq]
            _ = ∑ m : Fin (k + 1),
                  (σ2 * Renewal.returnWeight (k + 1 - m.val)) *
                    (∑ z ∈ Polymer.endpoints 0 m.val,
                      Collision.spatialRenewal σ2 m.val z) := by
              apply Finset.sum_congr rfl
              intro m hm
              calc
                _ = ∑ z ∈ Polymer.endpoints 0 m.val,
                    (σ2 * Renewal.returnWeight (k + 1 - m.val)) *
                      Collision.spatialRenewal σ2 m.val z := by
                  apply Finset.sum_congr rfl
                  intro z hz
                  ring
                _ = (σ2 * Renewal.returnWeight (k + 1 - m.val)) *
                    (∑ z ∈ Polymer.endpoints 0 m.val,
                      Collision.spatialRenewal σ2 m.val z) := by
                  rw [← Finset.mul_sum]
            _ = ∑ m : Fin (k + 1),
                  (σ2 * Renewal.returnWeight (k + 1 - m.val)) *
                    Renewal.renewalMass (fun r => σ2 * Renewal.returnWeight r) m.val := by
              apply Finset.sum_congr rfl
              intro m hm
              have hsupport :
                  ∑' z : Site, Collision.spatialRenewal σ2 m.val z =
                    ∑ z ∈ Polymer.endpoints 0 m.val, Collision.spatialRenewal σ2 m.val z := by
                apply tsum_eq_sum
                intro z hz
                exact spatialRenewal_eq_zero_of_not_mem_endpoints σ2 m.val z hz
              rw [← hsupport]
              rw [ih m.val (by have := m.isLt; omega)]
            _ = Renewal.renewalMass (fun r => σ2 * Renewal.returnWeight r) (k + 1) := by
              let w : ℕ → ℝ := fun r => σ2 * Renewal.returnWeight r
              let f : ℕ → ℝ := fun r => w r *
                Renewal.renewalMass w (k + 1 - r)
              calc
                _ = ∑ m : Fin (k + 1), f (k + 1 - m.val) := by
                  apply Finset.sum_congr rfl
                  intro m hm
                  simp only [f, w]
                  rw [Nat.sub_sub_self (Nat.le_of_lt m.isLt)]
                _ = ∑ r ∈ Finset.Icc 1 (k + 1), f r :=
                  (sum_Icc_one_succ_eq_fin (n := k) f).symm
                _ = Renewal.renewalMass w (k + 1) := by
                  rw [Renewal.renewalMass_succ]
                _ = Renewal.renewalMass
                    (fun r => σ2 * Renewal.returnWeight r) (k + 1) := by
                  rfl




end Critical2DKPZ.SHF.Moments

end
