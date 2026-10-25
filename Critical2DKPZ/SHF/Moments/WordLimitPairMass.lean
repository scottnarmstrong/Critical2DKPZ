/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitTerminalGeneral
public import Critical2DKPZ.SHF.Moments.WordLimitTerminalSpectators
public import Critical2DKPZ.SHF.Moments.PairBlockLocalLimit
import Mathlib.Tactic

/-! # Exact row masses of a single collision block -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Summing the terminal configuration of a two-particle run leaves its scalar renewal mass. -/
theorem tsum_pairTwo_runFactor (β : ℝ) (r : ℕ) (u : Fin 2 → Site) :
    (∑' v : Fin 2 → Site, collisionWordUndampedPairRunFactor β pairTwo r u v) =
      if u 0 = u 1 then sigmaSq β *
        Renewal.renewalMass (fun k => sigmaSq β * Renewal.returnWeight k) r else 0 := by
  classical
  by_cases hu : u 0 = u 1
  · simp only [ite_eq_left hu]
    have hterm (v : Fin 2 → Site) :
        collisionWordUndampedPairRunFactor β pairTwo r u v =
          if v 0 = v 1 then sigmaSq β *
            Collision.spatialRenewal (sigmaSq β) r (v 0 - u 0) else 0 := by
      simp [collisionWordUndampedPairRunFactor, pairTwo, hu, Fin.prod_univ_two]
    have hmass :
        (∑ z ∈ endpoints (u 0) r,
          Collision.spatialRenewal (sigmaSq β) r (z - u 0)) =
          Renewal.renewalMass (fun k => sigmaSq β * Renewal.returnWeight k) r := by
      calc
        _ = ∑' z : Site, Collision.spatialRenewal (sigmaSq β) r (z - u 0) := by
          symm
          apply tsum_eq_sum
          intro z hz
          by_contra hne
          exact hz (spatialRenewal_nonzero_endpoint hne)
        _ = ∑' z : Site, Collision.spatialRenewal (sigmaSq β) r z := by
          simpa only [Equiv.coe_addRight, add_sub_cancel_right] using
            (Equiv.tsum_eq (Equiv.addRight (u 0))
              (fun z : Site => Collision.spatialRenewal (sigmaSq β) r (z - u 0))).symm
        _ = _ := tsum_spatialRenewal_eq_renewalMass (sigmaSq β) r
    calc
      _ = ∑ v ∈ Fintype.piFinset (fun i : Fin 2 => endpoints (u i) r),
          collisionWordUndampedPairRunFactor β pairTwo r u v := by
        apply tsum_eq_sum
        intro v hv
        exact collisionWord_runFactor_zero_of_not_endpoints β pairTwo r u v hv
      _ = ∑ z ∈ endpoints (u 0) r ∩ endpoints (u 1) r,
          sigmaSq β * Collision.spatialRenewal (sigmaSq β) r (z - u 0) := by
        simp_rw [hterm]
        have hD : (fun i : Fin 2 => endpoints (u i) r) =
            fun i : Fin 2 => if i = 0 then endpoints (u 0) r else endpoints (u 1) r := by
          funext i
          fin_cases i <;> rfl
        rw [hD]
        exact sum_pairTwo_config_diagonal _ _
          (fun v => sigmaSq β * Collision.spatialRenewal (sigmaSq β) r (v 0 - u 0))
      _ = sigmaSq β *
          ∑ z ∈ endpoints (u 0) r, Collision.spatialRenewal (sigmaSq β) r (z - u 0) := by
        have hE : endpoints (u 1) r = endpoints (u 0) r := congrArg (fun z => endpoints z r) hu.symm
        rw [hE, Finset.inter_self, Finset.mul_sum]
      _ = _ := by rw [hmass]
  · simp [collisionWordUndampedPairRunFactor, pairTwo, hu]

/-- A constant terminal pair collision test leaves the two-walk entrance mass. -/
theorem tsum_pairTwo_entrance_constant (s : ℕ) (x : Fin 2 → Site) (C : ℝ) :
    (∑' u : Fin 2 → Site,
      (∏ i, srwKernel s (u i - x i)) * (if u 0 = u 1 then C else 0)) =
      srwKernel (2 * s) (x 1 - x 0) * C := by
  classical
  let D : Fin 2 → Finset Site := fun i => endpoints (x i) s
  have hterm (u : Fin 2 → Site) :
      (∏ i, srwKernel s (u i - x i)) * (if u 0 = u 1 then C else 0) =
        if u 0 = u 1 then (srwKernel s (u 0 - x 0) * srwKernel s (u 1 - x 1)) * C else 0 := by
    split_ifs <;> simp only [Fin.prod_univ_two, mul_zero]
  calc
    _ = ∑ u ∈ Fintype.piFinset D,
        (∏ i, srwKernel s (u i - x i)) * (if u 0 = u 1 then C else 0) := by
      apply tsum_eq_sum
      intro u hu
      rw [collisionWord_freeProduct_zero_of_not_endpoints s x u hu, zero_mul]
    _ = ∑ z ∈ endpoints (x 0) s ∩ endpoints (x 1) s,
        (srwKernel s (z - x 0) * srwKernel s (z - x 1)) * C := by
      simp_rw [hterm]
      have hD : D = fun i : Fin 2 =>
          if i = 0 then endpoints (x 0) s else endpoints (x 1) s := by
        funext i
        fin_cases i <;> rfl
      rw [hD]
      exact sum_pairTwo_config_diagonal _ _
        (fun u => (srwKernel s (u 0 - x 0) * srwKernel s (u 1 - x 1)) * C)
    _ = (∑' z : Site, srwKernel s (z - x 0) * srwKernel s (z - x 1)) * C := by
      rw [← Finset.sum_mul]
      congr 1
      symm
      apply tsum_eq_sum
      intro z hz
      by_cases h₀ : z ∈ endpoints (x 0) s
      · have h₁ : z ∉ endpoints (x 1) s := by
          intro hmem
          exact hz (Finset.mem_inter.mpr ⟨h₀, hmem⟩)
        rw [srwKernel_eq_zero_of_not_mem s (x 1) z h₁, mul_zero]
      · rw [srwKernel_eq_zero_of_not_mem s (x 0) z h₀, zero_mul]
    _ = _ := by rw [srwKernel_collision]

/-- The one-letter row mass is the entrance collision mass followed by the scalar renewal mass. -/
theorem wordTerminalTest_pairTwo_one_eq (N : ℕ) (β : ℝ) (n : ℕ) (x : Fin 2 → Site) :
    wordTerminalTest N (sigmaSq β) [pairTwo] n x (fun _ => 1) =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        srwKernel (2 * s) (x 1 - x 0) *
          (sigmaSq β * Renewal.renewalMass
            (fun k => sigmaSq β * Renewal.returnWeight k) r) := by
  rw [wordTerminalTest_cons]
  simp only [wordTerminalTest_nil_one, mul_one]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  calc
    _ = ∑' u : Fin 2 → Site,
        (∏ i, srwKernel s (u i - x i)) *
          ∑' v : Fin 2 → Site, collisionWordUndampedPairRunFactor β pairTwo r u v := by
      apply tsum_congr
      intro u
      exact tsum_mul_left
    _ = _ := by
      simp_rw [tsum_pairTwo_runFactor]
      exact tsum_pairTwo_entrance_constant s x _

/-- The one-letter mass at any replica count is a single sum of the entrance
mass times the cumulative scalar renewal function. -/
theorem wordTerminalTest_single_one_eq {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (n : ℕ) (x : Fin h → Site) :
    wordTerminalTest N (sigmaSq β) [α] n x (fun _ => 1) =
      ∑ s ∈ Finset.Icc 1 n, srwKernel (2 * s) (x α.1.2 - x α.1.1) *
        (sigmaSq β * Renewal.renewalFunction
          (fun k => sigmaSq β * Renewal.returnWeight k) (n - s)) := by
  rw [wordTerminalTest_single_one_eq_pair, wordTerminalTest_pairTwo_one_eq]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [pairRestrict, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Finset.mul_sum, ← Finset.mul_sum, Renewal.sum_renewalMass_range]

end Critical2DKPZ.SHF.Moments
