/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationWeightedBoundaryProfiles
public import Critical2DKPZ.SHF.Moments.WordDominationWeightedCollisionProfile
public import Critical2DKPZ.SHF.Moments.WordDominationWeightedBoundaryScaling
public import Critical2DKPZ.SHF.Moments.WordDominationWeightedOperatorConstants
import Mathlib.Tactic

/-! # Uniform product of the two weighted boundary costs -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- The product of the weighted initial and terminal boundary norms is bounded by `C * N^h`, with `C` independent of `N`. -/
theorem exists_collisionWord_weightedBoundary_product_le (h : ℕ) (hh : 2 ≤ h)
    (B : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N L : ℕ}, 1 ≤ N → L ≤ B * N →
      ∀ (s : Finset (LatticeConfiguration h)) (I J : ReplicaPartition h),
        I ≠ ⊥ → J ≠ ⊥ →
        finiteLpNorm s 2 (fun x => hattedReplicaBoundaryVector L I
          (collisionWordScaledBallSites N R)
          (fun y => if y ∈ collisionWordScaledBallSites N R then (1 : ℝ) else 0) x /
          replicaExponentialWeight ((Real.sqrt (N : ℝ))⁻¹) x) *
        finiteLpNorm s 2 (fun x => replicaExponentialWeight ((Real.sqrt (N : ℝ))⁻¹) x *
          collisionIndicator J x) ≤ C * (N : ℝ) ^ h := by
  classical
  obtain ⟨Cb, hCb, hboundary⟩ := finiteLpNorm_weighted_hattedBoundary_indicator_le h hh
  obtain ⟨Cc, hCc, hcollision⟩ := finiteLpNorm_weight_collisionIndicator_two_le
  obtain ⟨Cball, hCball, hcard⟩ := card_collisionWordScaledBallSites_le
  let K := Cball * (R + 2) ^ 2
  let D := 2 * Cb * Real.exp (Cb * B) * Real.exp (R + 2) ^ h
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCc0 : 0 ≤ Cc := zero_le_one.trans hCc
  refine ⟨D * K * (Real.sqrt K * Cc) ^ (h - 1), by positivity, ?_⟩
  intro N L hN hL s I J hI hJ
  let A := collisionWordScaledBallSites N R
  let t := (Real.sqrt (N : ℝ))⁻¹
  have hscale := collisionWord_inv_sqrt_scale hN
  have htime := collisionWord_inv_sqrt_time_le hN hL
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
  have hr : ∀ y ∈ A, t * ‖siteToPlane y‖ ≤ R + 2 := by
    intro y hy
    have hy' : ‖siteToPlane y‖ ≤ (R + 2) * Real.sqrt (N : ℝ) :=
      (Finset.mem_filter.mp hy).2
    calc
      _ ≤ t * ((R + 2) * Real.sqrt (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hy' hscale.1.le
      _ = _ := by dsimp [t]; field_simp
  have hb := hboundary t hscale.1.le L A (R + 2) hr s I hI
  have hcost : Real.exp (Cb * t ^ 2 * L) ≤ Real.exp (Cb * B) := by
    apply Real.exp_le_exp.mpr
    have hCb0 : 0 ≤ Cb := zero_le_one.trans hCb
    nlinarith only [mul_le_mul_of_nonneg_left htime hCb0]
  have hleft : finiteLpNorm s 2 (fun x => hattedReplicaBoundaryVector L I A
      (fun y => if y ∈ A then (1 : ℝ) else 0) x / replicaExponentialWeight t x) ≤
      D * (A.card : ℝ) * Real.sqrt (A.card : ℝ) ^ (h - 1) := by
    apply hb.trans
    dsimp [D]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcost (by positivity)) (by positivity))
        (Nat.cast_nonneg _)) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hright := hcollision h (by omega) t hscale.1 hscale.2.1 s J hJ
  have hright' : finiteLpNorm s 2 (fun x => replicaExponentialWeight t x * collisionIndicator J x) ≤
      (Cc * Real.sqrt (N : ℝ)) ^ (h - 1) := by
    simpa only [t, div_inv_eq_mul] using hright
  calc
    _ ≤ (D * (A.card : ℝ) * Real.sqrt (A.card : ℝ) ^ (h - 1)) *
        (Cc * Real.sqrt (N : ℝ)) ^ (h - 1) :=
      mul_le_mul hleft hright' (finiteLpNorm_nonneg _ _ _)
        (by positivity)
    _ = D * ((A.card : ℝ) * Real.sqrt (A.card : ℝ) ^ (h - 1) *
        (Cc * Real.sqrt (N : ℝ)) ^ (h - 1)) := by ring
    _ ≤ D * (K * (Real.sqrt K * Cc) ^ (h - 1) * (N : ℝ) ^ h) := by
      apply mul_le_mul_of_nonneg_left _ hD
      exact collisionWord_weightedBoundary_cardinality_scale (by omega) (N : ℝ) K Cc
        (A.card : ℝ) hNpos.le hK hCc0 (hcard hN hR)
    _ = _ := by ring

end Critical2DKPZ.SHF.Moments

end
