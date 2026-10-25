/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25Operators
public import Critical2DKPZ.MomentBounds.CCR25IndependentDurationSum
public import Critical2DKPZ.MomentBounds.CCR25FreeKernelSemigroup
import Mathlib.Tactic

/-! # Starting profiles as CCR25 boundary vectors -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

private theorem collisionConfig_bot {h : ℕ} (z : LatticeConfiguration h) :
    IsCollisionConfiguration (⊥ : ReplicaPartition h) z := by
  constructor
  · intro i j hij
    have hij' : i = j := by simpa using hij
    exact congrArg z hij'
  · intro i j hi _ _
    obtain ⟨k, hik, hrel⟩ := hi
    have heq : i = k := by simpa using hrel
    exact (hik heq.symm).elim

private def replicaEndpointConfigurations {h : ℕ} (n : ℕ)
    (z : LatticeConfiguration h) : Finset (LatticeConfiguration h) :=
  Fintype.piFinset fun i : Fin h => Critical2DKPZ.Polymer.endpoints (z i) n

private theorem freeReplicaKernel_zero_of_not_endpoint_targets {h : ℕ}
    (n : ℕ) (I J : ReplicaPartition h) (z y : LatticeConfiguration h)
    (hy : y ∉ replicaEndpointConfigurations n z) :
    freeReplicaKernel n I J z y = 0 := by
  have hmissing : ∃ i : Fin h,
      y i ∉ Critical2DKPZ.Polymer.endpoints (z i) n := by
    by_contra hnot
    apply hy
    apply Fintype.mem_piFinset.mpr
    intro i
    by_contra hi
    exact hnot ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hmissing
  have hq : Critical2DKPZ.srwKernel n (y i - z i) = 0 :=
    Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem n (z i) (y i) hi
  have hprod : (∏ j : Fin h, Critical2DKPZ.srwKernel n (y j - z j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hq
  simp [freeReplicaKernel, hprod]

/-- Summing a product starting profile against a free replica kernel gives the
CCR25 left boundary vector. The collision restriction is imposed only at the
terminal configuration. -/
theorem finite_sum_startProfile_mul_freeReplicaKernel_eq_boundaryVector
    {h : ℕ} (n : ℕ) (I : ReplicaPartition h) (A : Finset Site)
    (φ : Site → ℝ) (x : LatticeConfiguration h) :
    (∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
      (∏ i : Fin h, φ (w i)) * freeReplicaKernel n ⊥ I w x) =
      replicaBoundaryVector n I A φ x := by
  classical
  by_cases hI : IsCollisionConfiguration I x
  · have hfactor :
        (∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
          ∏ i : Fin h, (φ (w i) * Critical2DKPZ.srwKernel n (x i - w i))) =
          ∏ i : Fin h, ∑ y ∈ A,
            φ y * Critical2DKPZ.srwKernel n (x i - y) := by
      exact finite_sum_product_over_piFinset_eq_product_sums
        (fun _ : Fin h => A)
        (fun i y => φ y * Critical2DKPZ.srwKernel n (x i - y))
    calc
      _ = ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
            ∏ i : Fin h, (φ (w i) * Critical2DKPZ.srwKernel n (x i - w i)) := by
          apply Finset.sum_congr rfl
          intro w hw
          have hgood : IsCollisionConfiguration (⊥ : ReplicaPartition h) w ∧
              IsCollisionConfiguration I x := ⟨collisionConfig_bot w, hI⟩
          rw [freeReplicaKernel, ite_eq_left hgood]
          rw [← Finset.prod_mul_distrib]
      _ = ∏ i : Fin h, ∑ y ∈ A,
            φ y * Critical2DKPZ.srwKernel n (x i - y) := hfactor
      _ = replicaBoundaryVector n I A φ x := by
          rw [replicaBoundaryVector, ite_eq_left hI]
          apply Finset.prod_congr rfl
          intro i hi
          simp [finiteBoundaryConvolution, mul_comm]
  · rw [replicaBoundaryVector, ite_eq_right hI]
    apply Finset.sum_eq_zero
    intro w hw
    rw [freeReplicaKernel]
    have hnot : ¬ (IsCollisionConfiguration (⊥ : ReplicaPartition h) w ∧
        IsCollisionConfiguration I x) := by
      rintro ⟨_, hc⟩
      exact hI hc
    rw [ite_eq_right hnot]
    simp

/-- A finitely supported product start profile, propagated by a free replica
kernel and tested against any continuation, equals the corresponding CCR25
boundary pairing. The final endpoint sum is finite by walk reachability. -/
theorem finite_sum_startProfile_freeReplicaKernel_pairing_eq_boundaryVector
    {h : ℕ} (n : ℕ) (I : ReplicaPartition h) (A : Finset Site)
    (φ : Site → ℝ) (f : LatticeConfiguration h → ℝ) :
    (∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
      (∏ i : Fin h, φ (w i)) *
        (∑' x : LatticeConfiguration h,
          freeReplicaKernel n ⊥ I w x * f x)) =
      ∑' x : LatticeConfiguration h,
        replicaBoundaryVector n I A φ x * f x := by
  classical
  let S := Fintype.piFinset (fun _ : Fin h => A)
  let U := S.biUnion fun w => replicaEndpointConfigurations n w
  have hzero (w x : LatticeConfiguration h) (hw : w ∈ S) (hx : x ∉ U) :
      freeReplicaKernel n ⊥ I w x = 0 := by
    exact freeReplicaKernel_zero_of_not_endpoint_targets n ⊥ I w x (by
      intro hxend
      apply hx
      exact Finset.mem_biUnion.mpr ⟨w, hw, by
        simpa [replicaEndpointConfigurations] using hxend⟩)
  have hleft :
      (∑ w ∈ S,
        (∏ i : Fin h, φ (w i)) *
          (∑' x : LatticeConfiguration h,
            freeReplicaKernel n ⊥ I w x * f x)) =
        ∑ w ∈ S,
          (∏ i : Fin h, φ (w i)) *
            (∑ x ∈ U, freeReplicaKernel n ⊥ I w x * f x) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [tsum_eq_sum (s := U) (fun x hx => by rw [hzero w x hw hx]; simp)]
  have hswap :
      (∑ w ∈ S,
        (∏ i : Fin h, φ (w i)) *
          (∑ x ∈ U, freeReplicaKernel n ⊥ I w x * f x)) =
        ∑ x ∈ U,
          (∑ w ∈ S,
            (∏ i : Fin h, φ (w i)) * freeReplicaKernel n ⊥ I w x) * f x := by
    calc
      _ = ∑ w ∈ S, ∑ x ∈ U,
            ((∏ i : Fin h, φ (w i)) * freeReplicaKernel n ⊥ I w x) * f x := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = ∑ x ∈ U, ∑ w ∈ S,
            ((∏ i : Fin h, φ (w i)) * freeReplicaKernel n ⊥ I w x) * f x :=
        Finset.sum_comm
      _ = ∑ x ∈ U,
            (∑ w ∈ S,
              (∏ i : Fin h, φ (w i)) * freeReplicaKernel n ⊥ I w x) * f x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_mul]
  have hboundary (x : LatticeConfiguration h) :
      (∑ w ∈ S,
        (∏ i : Fin h, φ (w i)) * freeReplicaKernel n ⊥ I w x) =
        replicaBoundaryVector n I A φ x := by
    simpa [S] using
      finite_sum_startProfile_mul_freeReplicaKernel_eq_boundaryVector n I A φ x
  have hboundZero (x : LatticeConfiguration h) (hx : x ∉ U) :
      replicaBoundaryVector n I A φ x = 0 := by
    rw [← hboundary x]
    apply Finset.sum_eq_zero
    intro w hw
    rw [hzero w x hw hx]
    ring
  calc
    _ = ∑ x ∈ U,
        (∑ w ∈ S,
          (∏ i : Fin h, φ (w i)) * freeReplicaKernel n ⊥ I w x) * f x :=
      hleft.trans hswap
    _ = ∑ x ∈ U, replicaBoundaryVector n I A φ x * f x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hboundary]
    _ = ∑' x : LatticeConfiguration h,
        replicaBoundaryVector n I A φ x * f x := by
      exact (tsum_eq_sum (s := U)
        (fun x hx => by rw [hboundZero x hx]; simp)).symm


/-- Summing the first free interval over the horizon and against a product
start profile is exactly pairing with the hatted CCR25 boundary vector. -/
theorem finite_sum_startProfile_hattedFreeReplicaKernel_pairing_eq_hattedBoundaryVector
    {h : ℕ} (L : ℕ) (I : ReplicaPartition h) (A : Finset Site)
    (φ : Site → ℝ) (f : LatticeConfiguration h → ℝ) :
    (∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
      (∏ i : Fin h, φ (w i)) *
        (∑' x : LatticeConfiguration h,
          hattedFreeReplicaKernel L ⊥ I w x * f x)) =
      ∑' x : LatticeConfiguration h,
        hattedReplicaBoundaryVector L I A φ x * f x := by
  classical
  let S : Finset (LatticeConfiguration h) :=
    Fintype.piFinset (fun _ : Fin h => A)
  let U : Finset (LatticeConfiguration h) :=
    (Finset.range L).biUnion fun n =>
      S.biUnion fun w => replicaEndpointConfigurations (n + 1) w
  have hfreeZero (n : ℕ) (hn : n ∈ Finset.range L)
      (w : LatticeConfiguration h) (hw : w ∈ S)
      (x : LatticeConfiguration h) (hx : x ∉ U) :
      freeReplicaKernel (n + 1) ⊥ I w x = 0 := by
    apply freeReplicaKernel_zero_of_not_endpoint_targets
    intro hmem
    exact hx (Finset.mem_biUnion.mpr ⟨n, hn,
      Finset.mem_biUnion.mpr ⟨w, hw, hmem⟩⟩)
  have hboundaryZero (n : ℕ) (hn : n ∈ Finset.range L)
      (x : LatticeConfiguration h) (hx : x ∉ U) :
      replicaBoundaryVector (n + 1) I A φ x = 0 := by
    rw [← finite_sum_startProfile_mul_freeReplicaKernel_eq_boundaryVector]
    apply Finset.sum_eq_zero
    intro w hw
    rw [hfreeZero n hn w (by simpa [S] using hw) x hx]
    simp
  have hhatBoundaryZero (x : LatticeConfiguration h) (hx : x ∉ U) :
      hattedReplicaBoundaryVector L I A φ x = 0 := by
    unfold hattedReplicaBoundaryVector
    apply Finset.sum_eq_zero
    intro n hn
    exact hboundaryZero n hn x hx
  have hfreeSummable (n : ℕ) (w : LatticeConfiguration h) :
      Summable (fun x : LatticeConfiguration h =>
        freeReplicaKernel (n + 1) ⊥ I w x * f x) := by
    apply summable_of_ne_finset_zero (s := replicaEndpointConfigurations (n + 1) w)
    intro x hx
    rw [freeReplicaKernel_zero_of_not_endpoint_targets (n + 1) ⊥ I w x hx]
    simp
  have hboundarySummable (n : ℕ) (hn : n ∈ Finset.range L) :
      Summable (fun x : LatticeConfiguration h =>
        replicaBoundaryVector (n + 1) I A φ x * f x) := by
    apply summable_of_ne_finset_zero (s := U)
    intro x hx
    rw [hboundaryZero n hn x hx]
    simp
  have hfreeHat (w : LatticeConfiguration h) :
      (∑' x : LatticeConfiguration h,
        hattedFreeReplicaKernel L ⊥ I w x * f x) =
        ∑ n ∈ Finset.range L,
          ∑' x : LatticeConfiguration h,
            freeReplicaKernel (n + 1) ⊥ I w x * f x := by
    calc
      _ = ∑' x : LatticeConfiguration h,
          ∑ n ∈ Finset.range L,
            freeReplicaKernel (n + 1) ⊥ I w x * f x := by
          apply tsum_congr
          intro x
          simp only [hattedFreeReplicaKernel, Finset.sum_mul]
      _ = _ := Summable.tsum_finsetSum (fun n hn => hfreeSummable n w)
  have hboundaryHat :
      (∑ n ∈ Finset.range L,
        ∑' x : LatticeConfiguration h,
          replicaBoundaryVector (n + 1) I A φ x * f x) =
        ∑' x : LatticeConfiguration h,
          hattedReplicaBoundaryVector L I A φ x * f x := by
    calc
      _ = ∑' x : LatticeConfiguration h,
          ∑ n ∈ Finset.range L,
            replicaBoundaryVector (n + 1) I A φ x * f x :=
          (Summable.tsum_finsetSum fun n hn => hboundarySummable n hn).symm
      _ = _ := by
          apply tsum_congr
          intro x
          simp only [hattedReplicaBoundaryVector, Finset.sum_mul]
  calc
    _ = ∑ w ∈ S,
        (∏ i : Fin h, φ (w i)) *
          ∑ n ∈ Finset.range L,
            ∑' x : LatticeConfiguration h,
              freeReplicaKernel (n + 1) ⊥ I w x * f x := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [hfreeHat]
    _ = ∑ w ∈ S,
        ∑ n ∈ Finset.range L,
          (∏ i : Fin h, φ (w i)) *
            ∑' x : LatticeConfiguration h,
              freeReplicaKernel (n + 1) ⊥ I w x * f x := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [Finset.mul_sum]
    _ = ∑ n ∈ Finset.range L,
        ∑ w ∈ S,
          (∏ i : Fin h, φ (w i)) *
            ∑' x : LatticeConfiguration h,
              freeReplicaKernel (n + 1) ⊥ I w x * f x := Finset.sum_comm
    _ = ∑ n ∈ Finset.range L,
        ∑' x : LatticeConfiguration h,
          replicaBoundaryVector (n + 1) I A φ x * f x := by
          apply Finset.sum_congr rfl
          intro n hn
          simpa [S] using
            finite_sum_startProfile_freeReplicaKernel_pairing_eq_boundaryVector
              (n + 1) I A φ f
    _ = _ := hboundaryHat


end Critical2DKPZ.MomentBounds
