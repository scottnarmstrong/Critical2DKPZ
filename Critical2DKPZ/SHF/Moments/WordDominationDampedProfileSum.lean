/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationFreeRunDurationBound
public import Critical2DKPZ.SHF.Moments.WordDominationTerminalRecursion
public import Critical2DKPZ.MomentBounds.CCR25HattedInteractionSupport
import Mathlib.Tactic

/-! # Damped duration contraction with a terminal profile -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

attribute [local instance] Classical.propDecidable

private theorem collisionWord_summable_mul_hattedInteractingReplicaKernelAbs {h L : ℕ}
    (lam β : ℝ) (I : ReplicaPartition h) (u : LatticeConfiguration h)
    (F : LatticeConfiguration h → ℝ) :
    Summable (fun v => hattedInteractingReplicaKernelAbs L lam β I u v * F v) := by
  let A := ccr25ConfigurationCenterSites u
  apply summable_of_ne_finset_zero (s := configBox h A L)
  intro v hv
  have hu := ccr25_mem_configBox_centerSites u
  rw [hattedInteractingReplicaKernelAbs_zero_of_not_configBox lam β I hu
    (by simpa [A] using hv)]
  simp

/-- After summing the free entrance and the pair renewal duration, a
nonnegative terminal profile is bounded by one hatted free transition and one
hatted pair interaction. The only exchanges of lattice sums use the exact
finite endpoint supports of the free and run factors. -/
theorem collisionWord_freeRunDuration_profile_sum_le
    {h n k L : ℕ} (hk : 1 ≤ k) (hcut : n + k ≤ L)
    (β lam : ℝ) (hlam : 0 ≤ lam) (α : CollisionPair h)
    (x : LatticeConfiguration h) (F : LatticeConfiguration h → ℝ)
    (hF : ∀ v, 0 ≤ F v) :
    (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
      ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
        ((∏ i, srwKernel s (u i - x i)) *
          collisionWordUndampedPairRunFactor β α r u v) *
          Real.exp ((lam / (L : ℝ)) * ((n - s - r + k : ℕ) : ℝ)) * F v) ≤
      Real.exp ((lam / (L : ℝ)) * ((n + k : ℕ) : ℝ)) *
        ∑' u : LatticeConfiguration h,
          hattedFreeReplicaKernel L ⊥ (pairPartition α) x u *
            ∑' v : LatticeConfiguration h,
              (sigmaSq β * hattedInteractingReplicaKernelAbs L
                (lam / (L : ℝ)) β (pairPartition α) u v) * F v := by
  classical
  let S : Finset ℕ := Finset.Icc 1 n
  let U : Finset (LatticeConfiguration h) :=
    S.biUnion (fun s => collisionWordConfigurationEndpointSet s x)
  let V : LatticeConfiguration h → Finset (LatticeConfiguration h) := fun u =>
    (Finset.range (n + 1)).biUnion (fun r => collisionWordConfigurationEndpointSet r u)
  let A : ℕ → LatticeConfiguration h → ℝ := fun s u =>
    ∏ i, srwKernel s (u i - x i)
  let R : ℕ → LatticeConfiguration h → LatticeConfiguration h → ℝ := fun r u v =>
    collisionWordUndampedPairRunFactor β α r u v
  let E : ℕ → ℕ → ℝ := fun s r =>
    Real.exp ((lam / (L : ℝ)) * ((n - s - r + k : ℕ) : ℝ))
  let κ : ℝ := lam / (L : ℝ)
  have hL : 1 ≤ L := by omega
  have hσ : 0 ≤ sigmaSq β := sigmaSq_nonneg β
  have hAzero (s : ℕ) (hs : s ∈ S) (u : LatticeConfiguration h) (hu : u ∉ U) :
      A s u = 0 := by
    apply collisionWord_freeProduct_zero_of_not_endpoints s x u
    intro huend
    apply hu
    exact Finset.mem_biUnion.mpr ⟨s, hs, by simpa [U] using huend⟩
  have hRzero (s r : ℕ) (hs : s ∈ S) (hr : r ∈ Finset.range (n - s + 1))
      (u v : LatticeConfiguration h) (hv : v ∉ V u) : R r u v = 0 := by
    apply collisionWord_runFactor_zero_of_not_endpoints β α r u v
    intro hvend
    apply hv
    have hrn : r ∈ Finset.range (n + 1) := by
      have hs' := (Finset.mem_Icc.mp (by simpa [S] using hs)).2
      have hr' := Finset.mem_range.mp hr
      simp only [Finset.mem_range]
      omega
    exact Finset.mem_biUnion.mpr ⟨r, hrn, by simpa [V] using hvend⟩
  have hconfigSum (s r : ℕ) (hs : s ∈ S)
      (hr : r ∈ Finset.range (n - s + 1)) :
      (∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
        (A s u * R r u v) * E s r * F v) =
        ∑ u ∈ U, ∑ v ∈ V u, (A s u * R r u v) * E s r * F v := by
    have hvsum (u : LatticeConfiguration h) :
        (∑' v : LatticeConfiguration h,
          (A s u * R r u v) * E s r * F v) =
          ∑ v ∈ V u, (A s u * R r u v) * E s r * F v := by
      apply tsum_eq_sum
      intro v hv
      rw [hRzero s r hs hr u v hv]
      simp
    rw [tsum_eq_sum (s := U)]
    · apply Finset.sum_congr rfl
      intro u hu
      rw [hvsum u]
    · intro u hu
      rw [hAzero s hs u hu]
      simp
  have hreorder :
      (∑ s ∈ S, ∑ r ∈ Finset.range (n - s + 1),
        ∑ u ∈ U, ∑ v ∈ V u, (A s u * R r u v) * E s r * F v) =
      ∑ u ∈ U, ∑ v ∈ V u,
        ∑ s ∈ S, ∑ r ∈ Finset.range (n - s + 1),
          (A s u * R r u v) * E s r * F v := by
    calc
      _ = ∑ s ∈ S, ∑ u ∈ U, ∑ r ∈ Finset.range (n - s + 1),
            ∑ v ∈ V u, (A s u * R r u v) * E s r * F v := by
          apply Finset.sum_congr rfl
          intro s hs
          exact Finset.sum_comm
      _ = ∑ s ∈ S, ∑ u ∈ U, ∑ v ∈ V u,
            ∑ r ∈ Finset.range (n - s + 1),
              (A s u * R r u v) * E s r * F v := by
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro u hu
          exact Finset.sum_comm
      _ = ∑ u ∈ U, ∑ s ∈ S, ∑ v ∈ V u,
            ∑ r ∈ Finset.range (n - s + 1),
              (A s u * R r u v) * E s r * F v := by
          exact Finset.sum_comm
      _ = ∑ u ∈ U, ∑ v ∈ V u, ∑ s ∈ S,
            ∑ r ∈ Finset.range (n - s + 1),
              (A s u * R r u v) * E s r * F v := by
          apply Finset.sum_congr rfl
          intro u hu
          exact Finset.sum_comm
  have hcontract (u v : LatticeConfiguration h) :
      (∑ s ∈ S, ∑ r ∈ Finset.range (n - s + 1),
        (A s u * R r u v) * E s r) ≤
        Real.exp (κ * ((n + k : ℕ) : ℝ)) *
          hattedFreeReplicaKernel L ⊥ (pairPartition α) x u *
            (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
              (pairPartition α) u v) := by
    have hsumEq :
        (∑ s ∈ S, ∑ r ∈ Finset.range (n - s + 1),
          (A s u * R r u v) * E s r) =
          ∑ s ∈ Finset.Icc 1 n,
            (∏ i, srwKernel s (u i - x i)) *
              ∑ r ∈ Finset.range (n - s + 1),
                collisionWordUndampedPairRunFactor β α r u v *
                  Real.exp (κ * ((n - s - r + k : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      simp only [A, R, E, κ]
      ring
    have hsumEq' :
        (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          (A s u * R r u v) * E s r) =
          ∑ s ∈ Finset.Icc 1 n,
            (∏ i, srwKernel s (u i - x i)) *
              ∑ r ∈ Finset.range (n - s + 1),
                collisionWordUndampedPairRunFactor β α r u v *
                  Real.exp (κ * ((n - s - r + k : ℕ) : ℝ)) := by
      simpa only [S] using hsumEq
    rw [hsumEq']
    simpa only [κ] using
      collisionWord_freeRunDuration_sum_le_hatted hk hcut β lam hlam α x u v
  let G : LatticeConfiguration h → ℝ := fun u =>
    ∑' v : LatticeConfiguration h,
      (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
        (pairPartition α) u v) * F v
  have hGnonneg (u : LatticeConfiguration h) : 0 ≤ G u := by
    apply tsum_nonneg
    intro v
    exact mul_nonneg
      (mul_nonneg hσ
        (hattedInteractingReplicaKernelAbs_nonneg L κ β (pairPartition α) u v))
      (hF v)
  have hGsum (u : LatticeConfiguration h) :
      Summable (fun v : LatticeConfiguration h =>
        (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
          (pairPartition α) u v) * F v) := by
    have hrow := collisionWord_summable_mul_hattedInteractingReplicaKernelAbs (L := L)
      κ β (pairPartition α) u F
    simpa [mul_assoc] using hrow.mul_left (sigmaSq β)
  have houterSummable :
      Summable (fun u : LatticeConfiguration h =>
        hattedFreeReplicaKernel L ⊥ (pairPartition α) x u * G u) :=
    summable_mul_hattedFreeReplicaKernel_row_any L ⊥ (pairPartition α) x G
  have hVle (u : LatticeConfiguration h) :
      (∑ v ∈ V u,
        (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
          (pairPartition α) u v) * F v) ≤ G u := by
    apply (hGsum u).sum_le_tsum (V u)
    intro v hv
    exact mul_nonneg
      (mul_nonneg hσ
        (hattedInteractingReplicaKernelAbs_nonneg L κ β (pairPartition α) u v))
      (hF v)
  have hUle :
      (∑ u ∈ U,
        hattedFreeReplicaKernel L ⊥ (pairPartition α) x u * G u) ≤
        ∑' u : LatticeConfiguration h,
          hattedFreeReplicaKernel L ⊥ (pairPartition α) x u * G u :=
    houterSummable.sum_le_tsum U (fun u _ =>
      mul_nonneg (hattedFreeReplicaKernel_nonneg L ⊥ (pairPartition α) x u)
        (hGnonneg u))
  calc
    _ = ∑ s ∈ S, ∑ r ∈ Finset.range (n - s + 1),
        ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
          (A s u * R r u v) * E s r * F v := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      simp only [A, R, E, collisionWordUndampedPairRunFactor]
    _ = ∑ s ∈ S, ∑ r ∈ Finset.range (n - s + 1),
        ∑ u ∈ U, ∑ v ∈ V u, (A s u * R r u v) * E s r * F v := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      exact hconfigSum s r hs hr
    _ = ∑ u ∈ U, ∑ v ∈ V u,
        ∑ s ∈ S, ∑ r ∈ Finset.range (n - s + 1),
          (A s u * R r u v) * E s r * F v := hreorder
    _ ≤ ∑ u ∈ U, ∑ v ∈ V u,
        (Real.exp (κ * ((n + k : ℕ) : ℝ)) *
          hattedFreeReplicaKernel L ⊥ (pairPartition α) x u *
          (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
            (pairPartition α) u v)) * F v := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      have hnonneg : 0 ≤ F v := hF v
      have hfactor :
          (∑ s ∈ S, ∑ r ∈ Finset.range (n - s + 1),
            (A s u * R r u v) * E s r * F v) =
          (∑ s ∈ S, ∑ r ∈ Finset.range (n - s + 1),
            (A s u * R r u v) * E s r) * F v := by
        calc
          _ = ∑ s ∈ S,
                ((∑ r ∈ Finset.range (n - s + 1),
                  (A s u * R r u v) * E s r) * F v) := by
              apply Finset.sum_congr rfl
              intro s hs
              rw [Finset.sum_mul]
          _ = _ := by rw [Finset.sum_mul]
      calc
        (∑ s ∈ S, ∑ r ∈ Finset.range (n - s + 1),
          (A s u * R r u v) * E s r * F v) =
            (∑ s ∈ S, ∑ r ∈ Finset.range (n - s + 1),
              (A s u * R r u v) * E s r) * F v := hfactor
        _ ≤ Real.exp (κ * ((n + k : ℕ) : ℝ)) *
              hattedFreeReplicaKernel L ⊥ (pairPartition α) x u *
              (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
                (pairPartition α) u v) * F v :=
            mul_le_mul_of_nonneg_right (hcontract u v) hnonneg
        _ = _ := by ring
    _ = Real.exp (κ * ((n + k : ℕ) : ℝ)) *
        ∑ u ∈ U, hattedFreeReplicaKernel L ⊥ (pairPartition α) x u *
          ∑ v ∈ V u,
            (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
              (pairPartition α) u v) * F v := by
      have hinner (u : LatticeConfiguration h) :
          (∑ v ∈ V u,
            (Real.exp (κ * ((n + k : ℕ) : ℝ)) *
              hattedFreeReplicaKernel L ⊥ (pairPartition α) x u *
              (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
                (pairPartition α) u v)) * F v) =
            (Real.exp (κ * ((n + k : ℕ) : ℝ)) *
              hattedFreeReplicaKernel L ⊥ (pairPartition α) x u) *
              ∑ v ∈ V u,
                (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
                  (pairPartition α) u v) * F v := by
        calc
          _ = ∑ v ∈ V u,
                (Real.exp (κ * ((n + k : ℕ) : ℝ)) *
                  hattedFreeReplicaKernel L ⊥ (pairPartition α) x u) *
                  ((sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
                    (pairPartition α) u v) * F v) := by
              apply Finset.sum_congr rfl
              intro v hv
              ring
          _ = _ := by rw [Finset.mul_sum]
      calc
        _ = ∑ u ∈ U,
              (Real.exp (κ * ((n + k : ℕ) : ℝ)) *
                hattedFreeReplicaKernel L ⊥ (pairPartition α) x u) *
                ∑ v ∈ V u,
                  (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
                    (pairPartition α) u v) * F v := by
            apply Finset.sum_congr rfl
            intro u hu
            exact hinner u
        _ = _ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u hu
            ring
    _ ≤ Real.exp (κ * ((n + k : ℕ) : ℝ)) *
        ∑ u ∈ U, hattedFreeReplicaKernel L ⊥ (pairPartition α) x u * G u := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (hVle u)
        (hattedFreeReplicaKernel_nonneg L ⊥ (pairPartition α) x u)
    _ ≤ Real.exp (κ * ((n + k : ℕ) : ℝ)) *
        ∑' u : LatticeConfiguration h,
          hattedFreeReplicaKernel L ⊥ (pairPartition α) x u * G u :=
      mul_le_mul_of_nonneg_left hUle (Real.exp_nonneg _)
    _ = _ := by
      simp only [G, κ]

end Critical2DKPZ.SHF.Moments

end
