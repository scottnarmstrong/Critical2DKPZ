/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationFreeHorizonExtension
public import Critical2DKPZ.SHF.Moments.WordDominationDampedProfileSum
public import Critical2DKPZ.SHF.Moments.WordDominationVariancePathFactor
import Mathlib.Tactic

/-! # Summed terminal horizon for collision words -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

attribute [local instance] Classical.propDecidable

private theorem isCollisionConfiguration_pairPartition_iff_for_horizon_extension {h : ℕ}
    (α : CollisionPair h) (x : LatticeConfiguration h) :
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

private theorem tsum_supported_kernel_pair_eq_finite_sum_for_horizon_extension {h : ℕ}
    (A : LatticeConfiguration h → ℝ)
    (R : LatticeConfiguration h → LatticeConfiguration h → ℝ)
    (U : Finset (LatticeConfiguration h))
    (V : LatticeConfiguration h → Finset (LatticeConfiguration h))
    (hAzero : ∀ u, u ∉ U → A u = 0)
    (hRzero : ∀ u v, v ∉ V u → R u v = 0)
    (F : LatticeConfiguration h → ℝ) :
    (∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
      (A u * R u v) * F v) =
      ∑ u ∈ U, ∑ v ∈ V u, (A u * R u v) * F v := by
  have hVsum (u : LatticeConfiguration h) :
      (∑' v : LatticeConfiguration h, (A u * R u v) * F v) =
        ∑ v ∈ V u, (A u * R u v) * F v := by
    apply tsum_eq_sum
    intro v hv
    rw [hRzero u v hv]
    simp
  rw [tsum_eq_sum (s := U)]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [hVsum u]
  · intro u hu
    rw [hAzero u hu]
    simp

/-- Summing the terminal free-walk horizon is bounded by the final time-summed free transition, with a constant independent of the number of averaged durations. Finite endpoint support is supplied by `blockWordKernel_zero_of_endpoint_not_mem` and `collisionWord_terminalWalkProduct_zero_of_not_endpoints`. -/
theorem blockWordKernel_positiveHorizonExtension_le_varianceHattedPath
    {h : ℕ} (β lam : ℝ) (hlam : 0 ≤ lam) :
    ∀ (previous : ReplicaPartition h) (w : List (CollisionPair h))
      {n K L : ℕ}, 1 ≤ K → n + K ≤ L →
      ∀ x y : LatticeConfiguration h,
        IsCollisionConfiguration previous x →
        (∑ k ∈ Finset.range K,
          ∑' z : LatticeConfiguration h,
            blockWordKernel (sigmaSq β) w n x z *
              ∏ i, srwKernel (k + 1) (y i - z i)) ≤
          Real.exp ((lam / (L : ℝ)) * ((n + K : ℕ) : ℝ)) *
            varianceWeightedHattedPairWordPath L (lam / (L : ℝ)) β
              previous w x y := by
  intro previous w
  induction w generalizing previous with
  | nil =>
      intro n K L hK hcut x y hstart
      exact collisionWord_freeHorizonExtension_le_hattedFree hK hcut β lam hlam
        previous x y hstart
  | cons α w ih =>
      intro n K L hK hcut x y hstart
      let κ : ℝ := lam / (L : ℝ)
      let F : LatticeConfiguration h → ℝ := fun v =>
        varianceWeightedHattedPairWordPath L κ β (pairPartition α) w v y
      let U : Finset (LatticeConfiguration h) :=
        (Finset.Icc 1 n).biUnion (fun s => collisionWordConfigurationEndpointSet s x)
      let V : LatticeConfiguration h → Finset (LatticeConfiguration h) := fun u =>
        (Finset.range (n + 1)).biUnion (fun r => collisionWordConfigurationEndpointSet r u)
      let V0 : Finset (LatticeConfiguration h) := U.biUnion V
      let A : ℕ → LatticeConfiguration h → ℝ := fun s u =>
        ∏ i, srwKernel s (u i - x i)
      let R : ℕ → LatticeConfiguration h → LatticeConfiguration h → ℝ := fun r u v =>
        collisionWordUndampedPairRunFactor β α r u v
      have hFnonneg (v : LatticeConfiguration h) : 0 ≤ F v := by
        exact varianceWeightedHattedPairWordPath_nonneg L κ β
          (pairPartition α) w v y
      have hAzero (s : ℕ) (hs : s ∈ Finset.Icc 1 n)
          (u : LatticeConfiguration h) (hu : u ∉ U) : A s u = 0 := by
        apply collisionWord_freeProduct_zero_of_not_endpoints s x u
        intro huend
        apply hu
        exact Finset.mem_biUnion.mpr ⟨s, hs, huend⟩
      have hRzero (s r : ℕ) (hs : s ∈ Finset.Icc 1 n)
          (hr : r ∈ Finset.range (n - s + 1))
          (u v : LatticeConfiguration h) (hv : v ∉ V u) : R r u v = 0 := by
        apply collisionWord_runFactor_zero_of_not_endpoints β α r u v
        intro hvend
        apply hv
        have hrn : r ∈ Finset.range (n + 1) := by
          have hs' := (Finset.mem_Icc.mp hs).2
          have hr' := Finset.mem_range.mp hr
          simp only [Finset.mem_range]
          omega
        exact Finset.mem_biUnion.mpr ⟨r, hrn, hvend⟩
      have hcoeffNonneg (s r : ℕ) (u v : LatticeConfiguration h) :
          0 ≤ A s u * R r u v := by
        apply mul_nonneg
        · dsimp [A]
          exact Finset.prod_nonneg fun i hi => srwKernel_nonneg s (u i - x i)
        · dsimp [R, collisionWordUndampedPairRunFactor]
          rw [pairRunFactor_eq_sigmaSq_mul_interactingReplicaKernelAbs]
          exact mul_nonneg (sigmaSq_nonneg β)
            (interactingReplicaKernelAbs_nonneg β (pairPartition α) r u v)
      have hRecSum :
          (∑ k ∈ Finset.range K,
            ∑' z : LatticeConfiguration h,
              blockWordKernel (sigmaSq β) (α :: w) n x z *
                ∏ i, srwKernel (k + 1) (y i - z i)) =
          ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
            ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
              (A s u * R r u v) *
                (∑ k ∈ Finset.range K,
                  ∑' z : LatticeConfiguration h,
                    blockWordKernel (sigmaSq β) w (n - s - r) v z *
                      ∏ i, srwKernel (k + 1) (y i - z i)) := by
        calc
          _ = ∑ k ∈ Finset.range K,
                ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
                  ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
                    (A s u * R r u v) *
                      (∑' z : LatticeConfiguration h,
                        blockWordKernel (sigmaSq β) w (n - s - r) v z *
                          ∏ i, srwKernel (k + 1) (y i - z i)) := by
              apply Finset.sum_congr rfl
              intro k hk
              simpa [A, R, collisionWordUndampedPairRunFactor,
                Nat.add_assoc, mul_assoc] using
                (blockWordKernel_cons_terminalExtension_eq β α w x y)
          _ = ∑ s ∈ Finset.Icc 1 n, ∑ k ∈ Finset.range K,
                ∑ r ∈ Finset.range (n - s + 1),
                  ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
                    (A s u * R r u v) *
                      (∑' z : LatticeConfiguration h,
                        blockWordKernel (sigmaSq β) w (n - s - r) v z *
                          ∏ i, srwKernel (k + 1) (y i - z i)) := by
              exact Finset.sum_comm
          _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
                ∑ k ∈ Finset.range K,
                  ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
                    (A s u * R r u v) *
                      (∑' z : LatticeConfiguration h,
                        blockWordKernel (sigmaSq β) w (n - s - r) v z *
                          ∏ i, srwKernel (k + 1) (y i - z i)) := by
              apply Finset.sum_congr rfl
              intro s hs
              exact Finset.sum_comm
          _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
                ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
                  (A s u * R r u v) *
                    (∑ k ∈ Finset.range K,
                      ∑' z : LatticeConfiguration h,
                        blockWordKernel (sigmaSq β) w (n - s - r) v z *
                          ∏ i, srwKernel (k + 1) (y i - z i)) := by
              apply Finset.sum_congr rfl
              intro s hs
              apply Finset.sum_congr rfl
              intro r hr
              let f : ℕ → LatticeConfiguration h → LatticeConfiguration h → ℝ :=
                fun k u v => (A s u * R r u v) *
                  (∑' z : LatticeConfiguration h,
                    blockWordKernel (sigmaSq β) w (n - s - r) v z *
                      ∏ i, srwKernel (k + 1) (y i - z i))
              have hfU : ∀ k ∈ Finset.range K, ∀ u ∉ U, ∀ v, f k u v = 0 := by
                intro k hk u hu v
                change (A s u * R r u v) * _ = 0
                rw [hAzero s hs u hu]
                simp
              have hfV : ∀ k ∈ Finset.range K, ∀ u, ∀ v ∉ V0, f k u v = 0 := by
                intro k hk u v hv
                change (A s u * R r u v) * _ = 0
                by_cases hu : u ∈ U
                · have hv' : v ∉ V u := by
                    intro hv'
                    exact hv (Finset.mem_biUnion.mpr ⟨u, hu, hv'⟩)
                  rw [hRzero s r hs hr u v hv']
                  simp
                · rw [hAzero s hs u hu]
                  simp
              have hswap := sum_tsum_tsum_eq_tsum_tsum_sum_of_support
                (s := Finset.range K) (Rβ := U) (Rγ := V0)
                (f := f) hfU hfV
              calc
                _ = ∑ k ∈ Finset.range K, ∑' u : LatticeConfiguration h,
                      ∑' v : LatticeConfiguration h, f k u v := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        rfl
                _ = ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
                      ∑ k ∈ Finset.range K, f k u v := hswap
                _ = ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
                      (A s u * R r u v) *
                        (∑ k ∈ Finset.range K,
                          ∑' z : LatticeConfiguration h,
                            blockWordKernel (sigmaSq β) w (n - s - r) v z *
                              ∏ i, srwKernel (k + 1) (y i - z i)) := by
                    apply tsum_congr
                    intro u
                    apply tsum_congr
                    intro v
                    dsimp [f]
                    rw [← Finset.mul_sum]
          _ = _ := by
              apply Finset.sum_congr rfl
              intro s hs
              apply Finset.sum_congr rfl
              intro r hr
              apply tsum_congr
              intro u
              apply tsum_congr
              intro v
              dsimp [A, R]
      have htermBound (s : ℕ) (hs : s ∈ Finset.Icc 1 n)
          (r : ℕ) (hr : r ∈ Finset.range (n - s + 1)) :
          (∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
            (A s u * R r u v) *
              (∑ k ∈ Finset.range K,
                ∑' z : LatticeConfiguration h,
                  blockWordKernel (sigmaSq β) w (n - s - r) v z *
                    ∏ i, srwKernel (k + 1) (y i - z i))) ≤
          ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
            (A s u * R r u v) *
              (Real.exp (κ * ((n - s - r + K : ℕ) : ℝ)) * F v) := by
        rw [tsum_supported_kernel_pair_eq_finite_sum_for_horizon_extension
          (A := A s) (R := R r) (U := U) (V := V)
          (hAzero s hs) (hRzero s r hs hr)]
        rw [tsum_supported_kernel_pair_eq_finite_sum_for_horizon_extension
          (A := A s) (R := R r) (U := U) (V := V)
          (hAzero s hs) (hRzero s r hs hr)]
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        have hsle : s ≤ n := (Finset.mem_Icc.mp hs).2
        have hrle : r ≤ n - s := by
          have hr' := Finset.mem_range.mp hr
          omega
        have htailtime : n - s - r + K ≤ L := by omega
        have hfactorNonneg : 0 ≤ A s u * R r u v := hcoeffNonneg s r u v
        have hfactorBound :
            (A s u * R r u v) *
                (∑ k ∈ Finset.range K,
                  ∑' z : LatticeConfiguration h,
                    blockWordKernel (sigmaSq β) w (n - s - r) v z *
                      ∏ i, srwKernel (k + 1) (y i - z i)) ≤
              (A s u * R r u v) *
                (Real.exp (κ * ((n - s - r + K : ℕ) : ℝ)) * F v) := by
          by_cases hvα : v α.1.1 = v α.1.2
          · have hpair : IsCollisionConfiguration (pairPartition α) v :=
              (isCollisionConfiguration_pairPartition_iff_for_horizon_extension α v).mpr hvα
            have hind := ih (previous := pairPartition α)
              (n := n - s - r) (K := K) (L := L) hK htailtime v y hpair
            exact mul_le_mul_of_nonneg_left hind hfactorNonneg
          · have hR0 : R r u v = 0 := by
              dsimp [R, collisionWordUndampedPairRunFactor]
              simp [hvα]
            rw [hR0]
            simp
        exact hfactorBound
      have hprofile := collisionWord_freeRunDuration_profile_sum_le
        (n := n) (k := K) (L := L) hK hcut β lam hlam α x F hFnonneg
      have hrewrite :
          (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
            ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
              (A s u * R r u v) *
                (Real.exp (κ * ((n - s - r + K : ℕ) : ℝ)) * F v)) =
          (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
            ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
              ((∏ i, srwKernel s (u i - x i)) *
                collisionWordUndampedPairRunFactor β α r u v) *
                Real.exp ((lam / (L : ℝ)) * ((n - s - r + K : ℕ) : ℝ)) * F v) := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro r hr
        apply tsum_congr
        intro u
        apply tsum_congr
        intro v
        simp only [A, R, F, κ]
        ring
      have hpathEq :
          varianceWeightedHattedPairWordPath L κ β previous (α :: w) x y =
            ∑' u : LatticeConfiguration h,
              hattedFreeReplicaKernel L previous (pairPartition α) x u *
                ∑' v : LatticeConfiguration h,
                  (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
                    (pairPartition α) u v) * F v := by
        rfl
      have hfreeEq (u : LatticeConfiguration h) :
          hattedFreeReplicaKernel L previous (pairPartition α) x u =
            hattedFreeReplicaKernel L ⊥ (pairPartition α) x u := by
        unfold hattedFreeReplicaKernel
        apply Finset.sum_congr rfl
        intro d hd
        exact (freeReplicaKernel_bot_start_eq_of_collision
          (d + 1) previous (pairPartition α) x u hstart).symm
      have hstartEq :
          (∑' u : LatticeConfiguration h,
            hattedFreeReplicaKernel L previous (pairPartition α) x u *
              ∑' v : LatticeConfiguration h,
                (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
                  (pairPartition α) u v) * F v) =
          (∑' u : LatticeConfiguration h,
            hattedFreeReplicaKernel L ⊥ (pairPartition α) x u *
              ∑' v : LatticeConfiguration h,
                (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
                  (pairPartition α) u v) * F v) := by
        apply tsum_congr
        intro u
        rw [hfreeEq u]
      rw [hRecSum]
      calc
        _ ≤ ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
              ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
                (A s u * R r u v) *
                  (Real.exp (κ * ((n - s - r + K : ℕ) : ℝ)) * F v) := by
            apply Finset.sum_le_sum
            intro s hs
            apply Finset.sum_le_sum
            intro r hr
            exact htermBound s hs r hr
        _ ≤ Real.exp (κ * ((n + K : ℕ) : ℝ)) *
              varianceWeightedHattedPairWordPath L κ β previous (α :: w) x y := by
            rw [hrewrite, hpathEq]
            rw [hstartEq]
            simpa [κ, F] using hprofile

end Critical2DKPZ.SHF.Moments

end
