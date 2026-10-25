/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationPairKernelExact
import Mathlib.Tactic

/-! # Exact CCR renewal kernel on one pair stratum -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

attribute [local instance] Classical.propDecidable

private theorem pairPartition_collision_iff_exact {h : ℕ} (α : CollisionPair h)
    (x : LatticeConfiguration h) :
    IsCollisionConfiguration (pairPartition α) x ↔ x α.1.1 = x α.1.2 := by
  constructor
  · intro hx
    exact (isEqualityConfiguration_pair_iff α x).mp hx.1
  · intro hpair
    refine ⟨(isEqualityConfiguration_pair_iff α x).mpr hpair, ?_⟩
    intro i j hi hj hnot
    obtain ⟨i', hi'ne, hi'rel⟩ := hi
    obtain ⟨j', hj'ne, hj'rel⟩ := hj
    have hipair : i = α.1.1 ∨ i = α.1.2 := by
      have hrel := (pairPartition_rel α i i').mp hi'rel
      rcases hrel with hEq | ⟨hleft, _⟩
      · exact (hi'ne hEq.symm).elim
      · exact hleft
    have hjpair : j = α.1.1 ∨ j = α.1.2 := by
      have hrel := (pairPartition_rel α j j').mp hj'rel
      rcases hrel with hEq | ⟨hleft, _⟩
      · exact (hj'ne hEq.symm).elim
      · exact hleft
    have hij : (pairPartition α).r i j :=
      (pairPartition_rel α i j).mpr (Or.inr ⟨hipair, hjpair⟩)
    exact (hnot hij).elim


private theorem pairPartition_zeroFactor_product {h : ℕ}
    (α : CollisionPair h) (z x : LatticeConfiguration h)
    (hz : z α.1.1 = z α.1.2) (hx : x α.1.1 = x α.1.2) :
    (if x α.1.1 - z α.1.1 = 0 then (1 : ℝ) else 0) *
      (∏ i : Fin h, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ)
        else srwKernel 0 (x i - z i)) = if z = x then 1 else 0 := by
  classical
  by_cases hza : z α.1.1 = x α.1.1
  · have hdelta : (if x α.1.1 - z α.1.1 = 0 then (1 : ℝ) else 0) = 1 := by
      simp [hza]
    have hprod : (∏ i : Fin h,
        if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ)
          else srwKernel 0 (x i - z i)) = if z = x then 1 else 0 := by
      by_cases hzx : z = x
      · subst z
        simp
      · have hex : ∃ i : Fin h, z i ≠ x i := by
          by_contra hnone
          apply hzx
          funext i
          exact not_not.mp (not_exists.mp hnone i)
        obtain ⟨i, hi⟩ := hex
        have hnotPair : ¬ (i = α.1.1 ∨ i = α.1.2) := by
          rintro (rfl | rfl)
          · exact hi hza
          · exact hi (hz.symm.trans (hza.trans hx))
        have hsub : x i - z i ≠ 0 := by
          intro hsub
          exact hi ((sub_eq_zero.mp hsub).symm)
        have hprod_zero :
            (∏ j : Fin h,
              if j = α.1.1 ∨ j = α.1.2 then (1 : ℝ)
                else srwKernel 0 (x j - z j)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hnotPair, hsub])
        have hprod_zero' :
            (∏ j : Fin h,
              if j = α.1.1 ∨ j = α.1.2 then (1 : ℝ)
                else if x j - z j = 0 then 1 else 0) = 0 := by
          simpa only [Polymer.srwKernel_zero] using hprod_zero
        simp [hzx, hprod_zero']
    rw [hdelta, hprod]
    ring
  · have hzx : z ≠ x := fun h => hza (congrFun h α.1.1)
    have hdelta : (if x α.1.1 - z α.1.1 = 0 then (1 : ℝ) else 0) = 0 := by
      simp [sub_eq_zero, eq_comm, hza]
    rw [hdelta]
    simp [hzx]

private theorem spatialRenewalKernel_shift_pairCCR (σ2 : ℝ) (k r : ℕ)
    (z x : Site) :
    (∑' v : Site,
      Collision.spatialRenewal σ2 k (v - z) * srwKernel r (x - v) ^ 2) =
      ∑' u : Site,
        Collision.spatialRenewal σ2 k u * srwKernel r ((x - z) - u) ^ 2 := by
  calc
    _ = ∑' u : Site,
          Collision.spatialRenewal σ2 k ((Equiv.addLeft z u) - z) *
            srwKernel r (x - Equiv.addLeft z u) ^ 2 :=
      (Equiv.addLeft z).tsum_eq _ |>.symm
    _ = _ := by
      apply tsum_congr
      intro u
      have h1 : (Equiv.addLeft z u) - z = u := by simp [Equiv.addLeft]
      have h2 : x - Equiv.addLeft z u = (x - z) - u := by
        simp [Equiv.addLeft]
        abel
      rw [h1, h2]

private theorem pairPartition_spatialRenewal_succ_sum (σ2 : ℝ) (m : ℕ)
    (z x : Site) :
    (∑ n ∈ Finset.range (m + 1),
      ∑' v : Site,
        Collision.spatialRenewal σ2 (m - n) (v - z) * σ2 *
          srwKernel (n + 1) (x - v) ^ 2) =
      Collision.spatialRenewal σ2 (m + 1) (x - z) := by
  rw [Collision.spatialRenewal_succ]
  refine Finset.sum_bij (fun n hn => ⟨m - n, by
    have hn' := Finset.mem_range.mp hn
    omega⟩) ?_ ?_ ?_ ?_
  · intro n hn
    simp
  · intro n hn n' hn' heq
    have hnle : n ≤ m := by have := Finset.mem_range.mp hn; omega
    have hn'le : n' ≤ m := by have := Finset.mem_range.mp hn'; omega
    apply (tsub_right_inj hnle hn'le).mp
    exact congrArg Fin.val heq
  · intro j hj
    refine ⟨m - j.val, Finset.mem_range.mpr ?_, ?_⟩
    · have hjle : j.val ≤ m := by omega
      omega
    · apply Fin.ext
      exact Nat.sub_sub_self (by omega : j.val ≤ m)
  · intro n hn
    have hnle : n ≤ m := by have := Finset.mem_range.mp hn; omega
    have htime : m + 1 - (m - n) = n + 1 := by omega
    rw [htime]
    have hindex : (⟨m - n, by
        have hn' := Finset.mem_range.mp hn
        omega⟩ : Fin (m + 1)).val = m - n := rfl
    rw [hindex]
    calc
      _ = σ2 * ∑' v : Site,
            Collision.spatialRenewal σ2 (m - n) (v - z) *
              srwKernel (n + 1) (x - v) ^ 2 := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro v
          ring
      _ = σ2 * ∑' u : Site,
            Collision.spatialRenewal σ2 (m - n) u *
              srwKernel (n + 1) ((x - z) - u) ^ 2 := by
          rw [spatialRenewalKernel_shift_pairCCR]
      _ = ∑' u : Site,
            Collision.spatialRenewal σ2 (m - n) u * σ2 *
              srwKernel (n + 1) ((x - z) - u) ^ 2 := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro u
          ring

/-- The absolute interaction kernel on a pair partition is supported on the
pair-collision stratum at both endpoints. -/
theorem interactingReplicaKernelAbs_pairPartition_zero_of_endpoint_offStratum
    {h : ℕ} (β : ℝ) (α : CollisionPair h) (m : ℕ)
    (z x : LatticeConfiguration h)
    (hoff : z α.1.1 ≠ z α.1.2 ∨ x α.1.1 ≠ x α.1.2) :
    interactingReplicaKernelAbs β (pairPartition α) m z x = 0 := by
  classical
  induction m using Nat.strong_induction_on generalizing z x with
  | h m ih =>
      cases m with
      | zero =>
          rw [interactingReplicaKernelAbs]
          by_cases hzx : z = x
          · subst z
            rcases hoff with hz | hx
            · simp [pairPartition_collision_iff_exact α x, hz]
            · simp [pairPartition_collision_iff_exact α x, hx]
          · simp [hzx]
      | succ m =>
          rw [interactingReplicaKernelAbs]
          have hterm (n : ℕ) (hn : n ∈ Finset.range (m + 1)) :
              (∑' y : LatticeConfiguration h,
                interactingReplicaKernelAbs β (pairPartition α) (m - n) z y *
                  freeReplicaKernel (n + 1)
                    (pairPartition α) (pairPartition α) y x) = 0 := by
            have hpoint (y : LatticeConfiguration h) :
                interactingReplicaKernelAbs β (pairPartition α) (m - n) z y *
                  freeReplicaKernel (n + 1)
                    (pairPartition α) (pairPartition α) y x = 0 := by
              rcases hoff with hz | hx
              · have hprevious :
                    interactingReplicaKernelAbs β (pairPartition α) (m - n) z y = 0 :=
                  ih (m - n) (by
                    have hn' := Finset.mem_range.mp hn
                    omega) z y (Or.inl hz)
                simp [hprevious]
              · have hfree :
                    freeReplicaKernel (n + 1)
                      (pairPartition α) (pairPartition α) y x = 0 := by
                  unfold freeReplicaKernel
                  rw [pairPartition_collision_iff_exact α x]
                  simp [hx]
                simp [hfree]
            calc
              _ = ∑' _y : LatticeConfiguration h, (0 : ℝ) := tsum_congr hpoint
              _ = 0 := tsum_zero
          have hsum :
              (∑ n ∈ Finset.range (m + 1),
                ∑' y : LatticeConfiguration h,
                  interactingReplicaKernelAbs β (pairPartition α) (m - n) z y *
                    freeReplicaKernel (n + 1)
                      (pairPartition α) (pairPartition α) y x) = 0 := by
            apply Finset.sum_eq_zero
            intro n hn
            exact hterm n hn
          rw [hsum]
          simp

/-- On the pair-collision stratum at both endpoints, the absolute CCR interaction kernel equals the spatial-renewal kernel times the free spectator transitions. -/
theorem interactingReplicaKernelAbs_pairPartition_eq_on_strata {h : ℕ}
    (β : ℝ) (α : CollisionPair h) (m : ℕ)
    (z x : LatticeConfiguration h)
    (hz : z α.1.1 = z α.1.2) (hx : x α.1.1 = x α.1.2) :
    interactingReplicaKernelAbs β (pairPartition α) m z x =
      Collision.spatialRenewal (sigmaSq β) m (x α.1.1 - z α.1.1) *
        otherBlocksFreeKernel (pairPartition α) α.1.1 m z x := by
  classical
  induction m using Nat.strong_induction_on generalizing z x with
  | h m ih =>
      cases m with
      | zero =>
          rw [interactingReplicaKernelAbs, Collision.spatialRenewal_zero,
            otherBlocksFreeKernel_pairPartition_eq]
          have hcollision : IsCollisionConfiguration (pairPartition α) x :=
            (pairPartition_collision_iff_exact α x).2 hx
          simp only [hcollision, and_true]
          have hfactor := pairPartition_zeroFactor_product α z x hz hx
          rw [← hfactor]
      | succ m =>
          have hσ : 0 ≤ sigmaSq β := sigmaSq_nonneg β
          have hmoment :
              |replicaPartitionDisorderMoment β (pairPartition α)| = sigmaSq β := by
            rw [pairPartition_disorderMoment_eq_sigmaSq]
            exact abs_of_nonneg hσ
          rw [interactingReplicaKernelAbs, hmoment]
          let M : ℕ → ℝ := fun n =>
            ∑' v : Site,
              Collision.spatialRenewal (sigmaSq β) (m - n) (v - z α.1.1) *
                srwKernel (n + 1) (x α.1.1 - v) ^ 2
          have hinner (n : ℕ) (hn : n ∈ Finset.range (m + 1)) :
              (∑' y : LatticeConfiguration h,
                interactingReplicaKernelAbs β (pairPartition α) (m - n) z y *
                  freeReplicaKernel (n + 1) (pairPartition α) (pairPartition α) y x) =
                M n * otherBlocksFreeKernel (pairPartition α) α.1.1
                  (m - n + (n + 1)) z x := by
            calc
              _ = ∑' y : LatticeConfiguration h,
                    Collision.spatialRenewal (sigmaSq β) (m - n)
                        (y α.1.1 - z α.1.1) *
                      otherBlocksFreeKernel (pairPartition α) α.1.1 (m - n) z y *
                      freeReplicaKernel (n + 1)
                        (pairPartition α) (pairPartition α) y x := by
                  apply tsum_congr
                  intro y
                  by_cases hy : y α.1.1 = y α.1.2
                  · rw [ih (m - n) (by
                        have hn' := Finset.mem_range.mp hn
                        omega) z y hz hy]
                  · have hfree :
                        freeReplicaKernel (n + 1) (pairPartition α)
                          (pairPartition α) y x = 0 := by
                      unfold freeReplicaKernel
                      rw [pairPartition_collision_iff_exact α y,
                        pairPartition_collision_iff_exact α x]
                      simp [hy, hx]
                    rw [hfree]
                    simp
                    
              _ = M n * otherBlocksFreeKernel (pairPartition α) α.1.1
                    (m - n + (n + 1)) z x := by
                  rw [spatialRenewal_kernelStep_pairPartition_eq α
                    (sigmaSq β) (m - n) (n + 1) z x hx]
          have hsum :
              (∑ n ∈ Finset.range (m + 1),
                ∑' y : LatticeConfiguration h,
                  interactingReplicaKernelAbs β (pairPartition α) (m - n) z y *
                    freeReplicaKernel (n + 1) (pairPartition α) (pairPartition α) y x) =
                (∑ n ∈ Finset.range (m + 1), M n) *
                  otherBlocksFreeKernel (pairPartition α) α.1.1 (m + 1) z x := by
            calc
              _ = ∑ n ∈ Finset.range (m + 1),
                    M n * otherBlocksFreeKernel (pairPartition α) α.1.1
                      (m - n + (n + 1)) z x := by
                  apply Finset.sum_congr rfl
                  intro n hn
                  exact hinner n hn
              _ = ∑ n ∈ Finset.range (m + 1),
                    M n * otherBlocksFreeKernel (pairPartition α) α.1.1
                      (m + 1) z x := by
                  apply Finset.sum_congr rfl
                  intro n hn
                  have hn' : n ≤ m := by
                    have hn'' := Finset.mem_range.mp hn
                    omega
                  rw [show m - n + (n + 1) = m + 1 by omega]
              _ = _ := by rw [← Finset.sum_mul]
          calc
            _ = sigmaSq β *
                  ((∑ n ∈ Finset.range (m + 1), M n) *
                    otherBlocksFreeKernel (pairPartition α) α.1.1 (m + 1) z x) := by
                rw [hsum]
            _ = Collision.spatialRenewal (sigmaSq β) (m + 1)
                  (x α.1.1 - z α.1.1) *
                  otherBlocksFreeKernel (pairPartition α) α.1.1 (m + 1) z x := by
                have hM : sigmaSq β *
                    (∑ n ∈ Finset.range (m + 1), M n) =
                    Collision.spatialRenewal (sigmaSq β) (m + 1)
                      (x α.1.1 - z α.1.1) := by
                  dsimp [M]
                  calc
                    _ = ∑ n ∈ Finset.range (m + 1),
                          ∑' v : Site,
                            Collision.spatialRenewal (sigmaSq β) (m - n)
                                (v - z α.1.1) * sigmaSq β *
                              srwKernel (n + 1) (x α.1.1 - v) ^ 2 := by
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro n hn
                        rw [← tsum_mul_left]
                        apply tsum_congr
                        intro v
                        ring
                    _ = _ := pairPartition_spatialRenewal_succ_sum
                      (sigmaSq β) m (z α.1.1) (x α.1.1)
                calc
                  _ = (sigmaSq β *
                      (∑ n ∈ Finset.range (m + 1), M n)) *
                      otherBlocksFreeKernel (pairPartition α) α.1.1 (m + 1) z x := by
                    ring
                  _ = _ := by rw [hM]

end Critical2DKPZ.SHF.Moments

end
