/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.FirstCollision
import Mathlib.Tactic

/-! # Polarization of the first-collision identity for finite initial profiles -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Polymer

/-- A flat-terminal profile partition function is the profile-weighted sum of point-to-plane partition functions. -/
theorem profileP2Fun_flat_eq_sum (β : ℝ) (a n : ℕ) (ν : Site → ℝ)
    (A : Finset Site) (hν : ∀ w ∉ A, ν w = 0) (ω : Disorder) :
    profileP2Fun β a (a + n) ν (fun _ => 1) ω =
      ∑ w ∈ A, ν w * pointToPlane β a n w ω := by
  rw [profileP2Fun_eq_sum β a (a + n) ν (fun _ => 1) A hν]
  simp only [Nat.add_sub_cancel_left, mul_one, tsum_pointToPoint]

/-- The product expectation of finite-profile partition functions expands as a finite kernel sum. -/
theorem integral_profile_product_finset (β : ℝ) (a n : ℕ) (ν ν' : Site → ℝ)
    (A B : Finset Site) (hν : ∀ w ∉ A, ν w = 0) (hν' : ∀ v ∉ B, ν' v = 0) :
    (∫ ω, profileP2Fun β a (a + n) ν (fun _ => 1) ω *
      profileP2Fun β a (a + n) ν' (fun _ => 1) ω ∂disorderLaw) =
      ∑ w ∈ A, ∑ v ∈ B, ν w * ν' v * pairMoment β n w v := by
  have heq (ω : Disorder) :
      profileP2Fun β a (a + n) ν (fun _ => 1) ω *
      profileP2Fun β a (a + n) ν' (fun _ => 1) ω =
        ∑ w ∈ A, ∑ v ∈ B, (ν w * ν' v) *
          (pointToPlane β a n w ω * pointToPlane β a n v ω) := by
    rw [profileP2Fun_flat_eq_sum β a n ν A hν,
      profileP2Fun_flat_eq_sum β a n ν' B hν', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  simp_rw [heq]
  rw [integral_finsetSum _ fun w _ =>
    integrable_finsetSum _ fun v _ => (integrable_pairProduct β a n w v).const_mul _]
  apply Finset.sum_congr rfl
  intro w _
  rw [integral_finsetSum _ fun v _ => (integrable_pairProduct β a n w v).const_mul _]
  simp_rw [integral_const_mul, integral_pairMoment]

/-- For finitely supported initial profiles, the mixed second moment minus the product of their masses expands over the first selected replica collision. -/
theorem profile_firstCollision_finset (β : ℝ) (a n : ℕ) (ν ν' : Site → ℝ)
    (A B : Finset Site) (hν : ∀ w ∉ A, ν w = 0) (hν' : ∀ v ∉ B, ν' v = 0) :
    (∫ ω, profileP2Fun β a (a + n) ν (fun _ => 1) ω *
      profileP2Fun β a (a + n) ν' (fun _ => 1) ω ∂disorderLaw) -
        (∑ w ∈ A, ν w) * (∑ v ∈ B, ν' v) =
      ∑ r ∈ Finset.Icc 1 n, ∑ w ∈ A, ∑ v ∈ B,
        ν w * ν' v * srwKernel (2 * r) (v - w) * sigmaSq β *
          (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by
  rw [integral_profile_product_finset β a n ν ν' A B hν hν']
  have hc (w v : Site) :
      ν w * ν' v * pairMoment β n w v =
        ν w * ν' v + ∑ r ∈ Finset.Icc 1 n,
          ν w * ν' v * srwKernel (2 * r) (v - w) * sigmaSq β *
            (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by
    rw [pairMoment_firstCollision, mul_add, mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [pairMoment_eq_secondMoment]
    ring
  simp_rw [hc, Finset.sum_add_distrib]
  have hm : (∑ w ∈ A, ∑ v ∈ B, ν w * ν' v) =
      (∑ w ∈ A, ν w) * (∑ v ∈ B, ν' v) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    exact (Finset.mul_sum _ _ _).symm
  rw [hm, add_sub_cancel_left]
  calc
    _ = ∑ w ∈ A, ∑ r ∈ Finset.Icc 1 n, ∑ v ∈ B,
        ν w * ν' v * srwKernel (2 * r) (v - w) * sigmaSq β *
          (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by
      apply Finset.sum_congr rfl
      intro w _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- For finitely supported initial profiles of total mass one, the finite first-collision expansion has unit constant term. -/
theorem probability_profile_firstCollision_finset (β : ℝ) (a n : ℕ) (ν ν' : Site → ℝ)
    (A B : Finset Site) (hν : ∀ w ∉ A, ν w = 0) (hν' : ∀ v ∉ B, ν' v = 0)
    (hm : (∑ w ∈ A, ν w) = 1) (hm' : (∑ v ∈ B, ν' v) = 1) :
    (∫ ω, profileP2Fun β a (a + n) ν (fun _ => 1) ω *
      profileP2Fun β a (a + n) ν' (fun _ => 1) ω ∂disorderLaw) - 1 =
      ∑ r ∈ Finset.Icc 1 n, ∑ w ∈ A, ∑ v ∈ B,
        ν w * ν' v * srwKernel (2 * r) (v - w) * sigmaSq β *
          (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by
  simpa only [hm, hm', one_mul] using profile_firstCollision_finset β a n ν ν' A B hν hν'

end Critical2DKPZ.Polymer
