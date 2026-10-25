/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.SeriesProduct
public import Critical2DKPZ.Polymer.ProfileCovariance
import Mathlib.Tactic

/-! # First-collision identity for arbitrary absolutely summable initial profiles -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Critical2DKPZ.Polymer

/-- Each simple-walk transition probability is at most one. -/
theorem srwKernel_le_one (n : ℕ) (z : Site) : srwKernel n z ≤ 1 := by
  unfold srwKernel
  apply le_trans (Finset.sum_le_sum (g := fun _ : Fin n → Fin 4 => (4 : ℝ)⁻¹ ^ n) ?_)
    (sum_walkProbability n).le
  intro s _
  split_ifs
  · rw [mul_one]
  · rw [mul_zero]
    positivity

/-- The product expectation of summable-profile partition functions expands as the double profile sum. -/
theorem integral_profile_product_summable (β : ℝ) (a n : ℕ) (ν ν' : Site → ℝ)
    (hν : Summable (fun w => |ν w|)) (hν' : Summable (fun v => |ν' v|)) :
    (∫ ω, profileP2Fun β a (a + n) ν (fun _ => 1) ω *
      profileP2Fun β a (a + n) ν' (fun _ => 1) ω ∂disorderLaw) =
      ∑' xy : Site × Site, ν xy.1 * ν' xy.2 * pairMoment β n xy.1 xy.2 := by
  have hf (ν₀ : Site → ℝ) (hν₀ : Summable (fun w => |ν₀ w|)) :
      ∑' w, eLpNorm (fun ω => ν₀ w * pointToPlane β a n w ω) 2 disorderLaw ≠ ∞ := by
    simpa only [Nat.add_sub_cancel_left, mul_one, tsum_pointToPoint] using
      profile_term_norms_ne_top β a (a + n) ν₀ (fun _ => 1) hν₀ 1 zero_le_one
        (fun _ => by norm_num) 2 (by norm_num)
  have h := integral_mul_series (fun w ω => ν w * pointToPlane β a n w ω)
    (fun v ω => ν' v * pointToPlane β a n v ω)
    (fun w => (memLp_pointToPlane β a n w 2 (by norm_num)).const_mul _)
    (fun v => (memLp_pointToPlane β a n v 2 (by norm_num)).const_mul _)
    (hf ν hν) (hf ν' hν')
  change (∫ ω, (∑' w, ν w * ∑' z, pointToPoint β a ((a + n) - a) w z ω * 1) *
    (∑' v, ν' v * ∑' z, pointToPoint β a ((a + n) - a) v z ω * 1) ∂disorderLaw) = _
  simp only [Nat.add_sub_cancel_left, mul_one, tsum_pointToPoint]
  rw [h]
  apply tsum_congr
  intro xy
  have heq (ω : Disorder) :
      (ν xy.1 * pointToPlane β a n xy.1 ω) *
        (ν' xy.2 * pointToPlane β a n xy.2 ω) =
      (ν xy.1 * ν' xy.2) *
        (pointToPlane β a n xy.1 ω * pointToPlane β a n xy.2 ω) := by ring
  simp_rw [heq]
  rw [integral_const_mul, integral_pairMoment]

/-- The first-collision coefficient is summable under the profile assumptions. -/
theorem summable_collision_coefficient (β : ℝ) (n r : ℕ) (ν ν' : Site → ℝ)
    (hν : Summable (fun w => |ν w|)) (hν' : Summable (fun v => |ν' v|)) :
    Summable (fun xy : Site × Site =>
      ν xy.1 * ν' xy.2 * srwKernel (2 * r) (xy.2 - xy.1) *
        sigmaSq β * pairMoment β (n - r) 0 0) := by
  have hAbs := hν.mul_of_nonneg hν' (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  apply (hAbs.mul_right (|sigmaSq β| * |pairMoment β (n - r) 0 0|)).of_norm_bounded
  intro xy
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (kernel_nonneg _ _)]
  calc
    _ ≤ (|ν xy.1| * |ν' xy.2|) * 1 * |sigmaSq β| *
        |pairMoment β (n - r) 0 0| := by
      gcongr
      exact srwKernel_le_one _ _
    _ = _ := by ring

/-- Summable-profile product moments have the stated first-collision expansion. -/
theorem profile_firstCollision_summable (β : ℝ) (a n : ℕ) (ν ν' : Site → ℝ)
    (hν : Summable (fun w => |ν w|)) (hν' : Summable (fun v => |ν' v|)) :
    (∫ ω, profileP2Fun β a (a + n) ν (fun _ => 1) ω *
      profileP2Fun β a (a + n) ν' (fun _ => 1) ω ∂disorderLaw) -
        (∑' w, ν w) * (∑' v, ν' v) =
      ∑ r ∈ Finset.Icc 1 n, ∑' xy : Site × Site,
        ν xy.1 * ν' xy.2 * srwKernel (2 * r) (xy.2 - xy.1) *
          sigmaSq β * pairMoment β (n - r) 0 0 := by
  rw [integral_profile_product_summable β a n ν ν' hν hν']
  have hbase : Summable (fun xy : Site × Site => ν xy.1 * ν' xy.2) :=
    summable_mul_of_summable_norm
      (by simpa only [Real.norm_eq_abs] using hν)
      (by simpa only [Real.norm_eq_abs] using hν')
  have hsum (S : Finset ℕ) :
      Summable (fun xy : Site × Site => ∑ r ∈ S,
        ν xy.1 * ν' xy.2 * srwKernel (2 * r) (xy.2 - xy.1) *
          sigmaSq β * pairMoment β (n - r) 0 0) := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact summable_zero
    | @insert r S hr ih =>
      simp only [Finset.sum_insert hr]
      exact (summable_collision_coefficient β n r ν ν' hν hν').add ih
  have heq (xy : Site × Site) :
      ν xy.1 * ν' xy.2 * pairMoment β n xy.1 xy.2 =
        ν xy.1 * ν' xy.2 +
        ∑ r ∈ Finset.Icc 1 n,
          ν xy.1 * ν' xy.2 * srwKernel (2 * r) (xy.2 - xy.1) *
            sigmaSq β * pairMoment β (n - r) 0 0 := by
    rw [pairMoment_firstCollision, mul_add, mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp_rw [heq]
  rw [hbase.tsum_add (hsum _)]
  rw [← tsum_mul_tsum_of_summable_norm
    (by simpa only [Real.norm_eq_abs] using hν)
    (by simpa only [Real.norm_eq_abs] using hν'), add_sub_cancel_left]
  exact Summable.tsum_finsetSum (fun r _ =>
    summable_collision_coefficient β n r ν ν' hν hν')

/-- For absolutely summable initial profiles of total mass one, the first-collision expansion has unit constant term. -/
theorem probability_profile_firstCollision (β : ℝ) (s n : ℕ) (hs : s ≤ n)
    (ν ν' : Site → ℝ) (hν : Summable (fun w => |ν w|))
    (hν' : Summable (fun v => |ν' v|))
    (hm : (∑' w, ν w) = 1) (hm' : (∑' v, ν' v) = 1) :
    (∫ ω, profileP2Fun β s n ν (fun _ => 1) ω *
      profileP2Fun β s n ν' (fun _ => 1) ω ∂disorderLaw) - 1 =
      ∑ r ∈ Finset.Icc 1 (n - s), ∑' xy : Site × Site,
        ν xy.1 * ν' xy.2 * srwKernel (2 * r) (xy.2 - xy.1) *
          sigmaSq β * (∫ ω, pointToPlane β 0 (n - s - r) 0 ω ^ 2 ∂disorderLaw) := by
  have h := profile_firstCollision_summable β s (n - s) ν ν' hν hν'
  simpa only [Nat.add_sub_of_le hs, hm, hm', one_mul, pairMoment_eq_secondMoment] using h

end Critical2DKPZ.Polymer
