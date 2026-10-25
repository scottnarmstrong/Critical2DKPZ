/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25RunExpansionBase
public import Critical2DKPZ.MomentBounds.CCR25TimedRunEndpointSupport
import Mathlib.Tactic

/-! # Finite spatial boxes for CCR25 walk paths -/

@[expose] public section

namespace Critical2DKPZ.MomentBounds

private theorem ccr25_srwStep_coordinate_abs_le_one (d : Fin 4) (j : Fin 2) :
    -1 ≤ Critical2DKPZ.srwStep d j ∧ Critical2DKPZ.srwStep d j ≤ 1 := by
  fin_cases d <;> fin_cases j <;> norm_num [Critical2DKPZ.srwStep]

/-- A walk endpoint differs from its start by at most the elapsed number of
steps in each lattice coordinate. -/
theorem ccr25WalkEndpoint_coordinate_distance_le (n : ℕ) (z x : Site)
    (hx : x ∈ Critical2DKPZ.Polymer.endpoints z n) (j : Fin 2) :
    -(n : ℤ) ≤ x j - z j ∧ x j - z j ≤ n := by
  obtain ⟨s, hs⟩ :=
    (Critical2DKPZ.Polymer.mem_endpoints_iff z x n).mp hx
  have hsumLo : -(n : ℤ) ≤
      ∑ i : Fin n, Critical2DKPZ.srwStep (s i) j := by
    calc
      -(n : ℤ) = ∑ _i : Fin n, (-1 : ℤ) := by simp
      _ ≤ ∑ i : Fin n, Critical2DKPZ.srwStep (s i) j :=
        Finset.sum_le_sum fun i _ =>
          (ccr25_srwStep_coordinate_abs_le_one (s i) j).1
  have hsumHi :
      ∑ i : Fin n, Critical2DKPZ.srwStep (s i) j ≤ (n : ℤ) := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℤ) :=
        Finset.sum_le_sum fun i _ =>
          (ccr25_srwStep_coordinate_abs_le_one (s i) j).2
      _ = n := by simp
  rw [Critical2DKPZ.Polymer.walkPosition_end] at hs
  have hj' : z j + ∑ i : Fin n, Critical2DKPZ.srwStep (s i) j = x j := by
    simpa only [Pi.add_apply, Finset.sum_apply] using congrFun hs j
  constructor <;> omega

/-- Enlarging the site box by the walk duration contains every endpoint of a
walk started in the original box. -/
theorem ccr25SiteBox_endpoint_subset {A : Finset Site} {r d : ℕ}
    {z x : Site} (hz : z ∈ siteBox A r)
    (hx : x ∈ Critical2DKPZ.Polymer.endpoints z d) :
    x ∈ siteBox A (r + d) := by
  obtain ⟨a, ha, hzbox⟩ := Finset.mem_biUnion.mp hz
  apply Finset.mem_biUnion.mpr
  refine ⟨a, ha, Fintype.mem_piFinset.mpr ?_⟩
  intro j
  have hzj : z j ∈ Finset.Icc (a j - (r : ℤ)) (a j + (r : ℤ)) :=
    Fintype.mem_piFinset.mp hzbox j
  rcases Finset.mem_Icc.mp hzj with ⟨hzlo, hzhi⟩
  have hdist := ccr25WalkEndpoint_coordinate_distance_le d z x hx j
  apply Finset.mem_Icc.mpr
  constructor
  · simp only [Nat.cast_add]
    omega
  · simp only [Nat.cast_add]
    omega

/-- Site boxes increase with their radius. -/
theorem ccr25SiteBox_mono {A : Finset Site} {r s : ℕ} (hrs : r ≤ s) :
    siteBox A r ⊆ siteBox A s := by
  intro x hx
  obtain ⟨a, ha, hxbox⟩ := Finset.mem_biUnion.mp hx
  apply Finset.mem_biUnion.mpr
  refine ⟨a, ha, Fintype.mem_piFinset.mpr ?_⟩
  intro j
  rcases Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hxbox j) with
    ⟨hxlo, hxhi⟩
  apply Finset.mem_Icc.mpr
  have hrs' : (r : ℤ) ≤ s := by exact_mod_cast hrs
  omega

/-- Configuration boxes increase with their radius. -/
theorem ccr25ConfigBox_mono {h : ℕ} {A : Finset Site} {r s : ℕ}
    (hrs : r ≤ s) : configBox h A r ⊆ configBox h A s := by
  intro x hx
  apply Fintype.mem_piFinset.mpr
  intro i
  exact ccr25SiteBox_mono hrs (Fintype.mem_piFinset.mp hx i)

/-- Enlarging the configuration box by the walk duration contains every
coordinatewise replica endpoint. -/
theorem ccr25ConfigBox_endpoint_subset {h : ℕ} {A : Finset Site} {r d : ℕ}
    {z x : LatticeConfiguration h} (hz : z ∈ configBox h A r)
    (hx : x ∈ Fintype.piFinset fun i : Fin h =>
      Critical2DKPZ.Polymer.endpoints (z i) d) :
    x ∈ configBox h A (r + d) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  exact ccr25SiteBox_endpoint_subset (Fintype.mem_piFinset.mp hz i)
    (Fintype.mem_piFinset.mp hx i)

/-- A free replica transition vanishes outside the configuration box reached
from its starting box in the prescribed duration. -/
theorem freeReplicaKernel_zero_of_not_configBox {h : ℕ} {A : Finset Site}
    {r d : ℕ} {z x : LatticeConfiguration h}
    (hz : z ∈ configBox h A r) (hx : x ∉ configBox h A (r + d))
    (I J : ReplicaPartition h) :
    freeReplicaKernel d I J z x = 0 := by
  have hnotall : ¬ ∀ i : Fin h,
      x i ∈ Critical2DKPZ.Polymer.endpoints (z i) d := by
    intro hall
    apply hx
    exact ccr25ConfigBox_endpoint_subset hz (Fintype.mem_piFinset.mpr hall)
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  have hq : Critical2DKPZ.srwKernel d (x i - z i) = 0 :=
    Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem d (z i) (x i) hi
  have hprod :
      (∏ j : Fin h, Critical2DKPZ.srwKernel d (x j - z j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hq
  simp [freeReplicaKernel, hprod]

/-- A one-time CCR25 boundary vector is supported on the box reached from its
finite start set in that many steps. -/
theorem replicaBoundaryVector_zero_of_not_configBox {h : ℕ} (n : ℕ)
    (I : ReplicaPartition h) (A : Finset Site) (φ : Site → ℝ)
    {x : LatticeConfiguration h} (hx : x ∉ configBox h A n) :
    replicaBoundaryVector n I A φ x = 0 := by
  have hnotall : ¬ ∀ i : Fin h, x i ∈ siteBox A n := by
    intro hall
    exact hx (Fintype.mem_piFinset.mpr hall)
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  have hconv : finiteBoundaryConvolution n A φ (x i) = 0 := by
    unfold finiteBoundaryConvolution
    apply Finset.sum_eq_zero
    intro y hy
    have hybox : y ∈ siteBox A 0 := by
      apply Finset.mem_biUnion.mpr
      refine ⟨y, hy, Fintype.mem_piFinset.mpr ?_⟩
      intro j
      simp
    have hnotend : x i ∉ Critical2DKPZ.Polymer.endpoints y n := by
      intro hreach
      obtain ⟨a, ha, hya⟩ := Finset.mem_biUnion.mp hybox
      have hyaeq : y = a := by
        funext j
        rcases Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hya j) with
          ⟨hlo, hhi⟩
        simp only [Nat.cast_zero, sub_zero, add_zero] at hlo hhi
        exact le_antisymm hhi hlo
      have hreach' : x i ∈ Critical2DKPZ.Polymer.endpoints a n := by
        simpa [hyaeq] using hreach
      have hsite : x i ∈ siteBox A n := by
        apply Finset.mem_biUnion.mpr
        refine ⟨a, ha, Fintype.mem_piFinset.mpr ?_⟩
        intro j
        have hdist := ccr25WalkEndpoint_coordinate_distance_le n a (x i) hreach' j
        apply Finset.mem_Icc.mpr
        omega
      exact hi hsite
    rw [Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem n y (x i) hnotend]
    simp
  unfold replicaBoundaryVector
  split_ifs with hcollision
  · exact Finset.prod_eq_zero (Finset.mem_univ i) hconv
  · rfl

/-- The horizon-summed boundary vector is supported on the radius-`L`
configuration box. -/
theorem hattedReplicaBoundaryVector_zero_of_not_configBox {h : ℕ}
    (L : ℕ) (I : ReplicaPartition h) (A : Finset Site) (φ : Site → ℝ)
    {x : LatticeConfiguration h} (hx : x ∉ configBox h A L) :
    hattedReplicaBoundaryVector L I A φ x = 0 := by
  unfold hattedReplicaBoundaryVector
  apply Finset.sum_eq_zero
  intro n hn
  have hnL : n + 1 ≤ L := by
    exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hn)
  have hx' : x ∉ configBox h A (n + 1) := by
    intro hx'
    exact hx (ccr25ConfigBox_mono hnL hx')
  exact replicaBoundaryVector_zero_of_not_configBox
    (n + 1) I A φ hx'


/-- A timed interaction run stays inside the spatial box enlarged by its
total prescribed duration. -/
theorem ccr25TimedRunTargetConfigurations_subset_configBox {h : ℕ}
    {A : Finset Site} {r : ℕ} (gaps : List ℕ)
    {z : LatticeConfiguration h} (hz : z ∈ configBox h A r) :
    ccr25TimedRunTargetConfigurations gaps z ⊆
      configBox h A (r + gaps.sum) := by
  intro x hx
  apply ccr25ConfigBox_endpoint_subset hz
  exact ccr25TimedRunTargetConfigurations_subset_endpoints gaps z hx

/-- A prescribed timed interaction run vanishes outside the configuration
box reached from its starting box in the total run duration. -/
theorem ccr25TimedInteractionRunAbs_zero_of_not_configBox {h : ℕ}
    {A : Finset Site} {r : ℕ} (β : ℝ) (I : ReplicaPartition h)
    (gaps : List ℕ) {z x : LatticeConfiguration h}
    (hz : z ∈ configBox h A r)
    (hx : x ∉ configBox h A (r + gaps.sum)) :
    ccr25TimedInteractionRunAbs β I gaps z x = 0 := by
  apply ccr25TimedInteractionRunAbs_zero_of_not_target β I gaps z x
  intro htarget
  exact hx (ccr25TimedRunTargetConfigurations_subset_configBox gaps hz htarget)




end Critical2DKPZ.MomentBounds

end
