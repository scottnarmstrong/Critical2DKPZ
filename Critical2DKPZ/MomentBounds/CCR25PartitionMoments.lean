/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25GaussianMoments
public import Critical2DKPZ.MomentBounds.CCR25PartitionWords
import Mathlib.Tactic

/-! # Full-support Gaussian moment bounds for CCR25 partition words -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- Labels in nonsingleton equivalence classes of a replica partition. -/
def ccr25PartitionCollisionLabels {h : ℕ} (I : ReplicaPartition h) :
    Finset (Fin h) := by
  classical
  exact
  Finset.univ.filter (fun i => InCollisionBlock I i)

/-- The full equivalence class represented by a replica label. -/
def ccr25ReplicaBlockLabels {h : ℕ} (I : ReplicaPartition h) (r : Fin h) :
    Finset (Fin h) := by
  classical
  exact
  Finset.univ.filter (fun i => I.r r i)

/-- Nontrivial equivalence-class representatives in a replica partition. -/
def ccr25NontrivialBlockRepresentatives {h : ℕ} (I : ReplicaPartition h) :
    Finset (Fin h) := by
  classical
  exact
  (replicaBlockRepresentatives I).filter (fun r => 2 ≤ replicaBlockSize I r)

/-- Every equivalence class has a least-label representative. -/
theorem exists_replicaBlockRepresentative {h : ℕ} (I : ReplicaPartition h)
    (i : Fin h) :
    ∃ r ∈ replicaBlockRepresentatives I, I.r r i := by
  classical
  let S : Finset (Fin h) := Finset.univ.filter (fun j => I.r j i)
  have hS : S.Nonempty := ⟨i, by simp [S]⟩
  let r := S.min' hS
  have hrS : r ∈ S := Finset.min'_mem S hS
  have hri : I.r r i := (Finset.mem_filter.mp hrS).2
  have hleast : ∀ j, I.r r j → r ≤ j := by
    intro j hrj
    apply Finset.min'_le
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact I.trans (I.symm' hrj) hri
  refine ⟨r, ?_, hri⟩
  change r ∈ Finset.univ.filter (fun x => ∀ j, I.r x j → x ≤ j)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hleast

private theorem replicaBlockSize_ge_two_of_inCollisionBlock {h : ℕ}
    (I : ReplicaPartition h) (r i : Fin h)
    (hri : I.r r i) (hi : InCollisionBlock I i) :
    2 ≤ replicaBlockSize I r := by
  classical
  obtain ⟨j, hji, hij⟩ := hi
  have hrj : I.r r j := I.trans hri hij
  have hsubset : ({i, j} : Finset (Fin h)) ⊆ ccr25ReplicaBlockLabels I r := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hri⟩
    · simp only [Finset.mem_singleton] at hx
      subst x
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrj⟩
  have hcard := Finset.card_le_card hsubset
  have hpair : ({i, j} : Finset (Fin h)).card = 2 := by
    simp [Ne.symm hji]
  have hclass : 2 ≤ (ccr25ReplicaBlockLabels I r).card := by
    rw [← hpair]
    exact hcard
  simpa [ccr25ReplicaBlockLabels, replicaBlockSize] using hclass

private theorem ccr25PartitionCollisionLabels_card_ge_two {h : ℕ}
    (I : ReplicaPartition h) (hI : I ≠ ⊥) :
    2 ≤ (ccr25PartitionCollisionLabels I).card := by
  classical
  obtain ⟨α, hα⟩ := exists_collisionPair_of_ne_discrete I hI
  have hne : α.val.1 ≠ α.val.2 := ne_of_lt α.property
  have hfirst : InCollisionBlock I α.val.1 := ⟨α.val.2, hne.symm, hα⟩
  have hsecond : InCollisionBlock I α.val.2 := ⟨α.val.1, hne, I.symm' hα⟩
  have hsubset : ({α.val.1, α.val.2} : Finset (Fin h)) ⊆
      ccr25PartitionCollisionLabels I := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst⟩
    · simp only [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsecond⟩
  have hcard := Finset.card_le_card hsubset
  have hpair : ({α.val.1, α.val.2} : Finset (Fin h)).card = 2 := by
    simp [hne]
  rw [← hpair]
  exact hcard

/-- The nonsingleton representative classes cover exactly the collision-label
set. The cardinal estimate below only needs the covering direction. -/
private theorem collisionLabels_subset_representativeBlocks {h : ℕ}
    (I : ReplicaPartition h) :
    ccr25PartitionCollisionLabels I ⊆
      (ccr25NontrivialBlockRepresentatives I).biUnion
        (ccr25ReplicaBlockLabels I) := by
  classical
  intro i hi
  obtain ⟨r, hr, hri⟩ := exists_replicaBlockRepresentative I i
  have hsize := replicaBlockSize_ge_two_of_inCollisionBlock I r i hri
    ((Finset.mem_filter.mp hi).2)
  have hr' : r ∈ ccr25NontrivialBlockRepresentatives I :=
    Finset.mem_filter.mpr ⟨hr, hsize⟩
  have hi' : i ∈ ccr25ReplicaBlockLabels I r := by
    simp [ccr25ReplicaBlockLabels, hri]
  exact Finset.mem_biUnion.mpr ⟨r, hr', hi'⟩


/-- The disorder moment of one partition pays one factor of the small Gaussian
standard deviation for each label in its nonsingleton classes. -/
theorem abs_replicaPartitionDisorderMoment_le_supportPower {h : ℕ}
    (β : ℝ) (I : ReplicaPartition h)
    (hσ : Critical2DKPZ.Polymer.sigmaSq β ≤ 1) :
    |replicaPartitionDisorderMoment β I| ≤
      (max 1 (ccr25GaussianMomentUniformConstant h)) ^ h *
        Real.sqrt (Critical2DKPZ.Polymer.sigmaSq β) ^
          (ccr25PartitionCollisionLabels I).card := by
  classical
  let reps := replicaBlockRepresentatives I
  let nontriv := ccr25NontrivialBlockRepresentatives I
  let σ := Real.sqrt (Critical2DKPZ.Polymer.sigmaSq β)
  let C := max 1 (ccr25GaussianMomentUniformConstant h)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 1) hC1
  have hCgauss : ccr25GaussianMomentUniformConstant h ≤ C := le_max_right _ _
  have hβsqrt : |β| ≤ σ := Real.abs_le_sqrt
    (Critical2DKPZ.MomentBounds.beta_sq_le_sigmaSq β)
  have hσ0 : 0 ≤ σ := by dsimp [σ]; positivity
  have hσ1 : σ ≤ 1 := by
    dsimp [σ]
    simpa using Real.sqrt_le_sqrt hσ
  have hfactor (r : Fin h) (hr : r ∈ reps) :
      |(if 2 ≤ replicaBlockSize I r then
          gaussianDisorderMoment β (replicaBlockSize I r) else 1)| ≤
        C * σ ^ (if 2 ≤ replicaBlockSize I r then replicaBlockSize I r else 0) := by
    by_cases hs : 2 ≤ replicaBlockSize I r
    · have hrsize : replicaBlockSize I r ≤ h := by
        unfold replicaBlockSize
        simpa using Finset.card_le_univ
          (Finset.univ.filter (fun j : Fin h => I.r r j))
      have hβ1 : |β| ≤ 1 := hβsqrt.trans hσ1
      have hmoment := abs_gaussianDisorderMoment_le_beta_pow β
        (replicaBlockSize I r) hβ1
      have hpow := pow_le_pow_left₀ (abs_nonneg β) hβsqrt
        (replicaBlockSize I r)
      simpa [hs] using (calc
        |gaussianDisorderMoment β (replicaBlockSize I r)| ≤
            ccr25GaussianMomentConstant (replicaBlockSize I r) *
              |β| ^ (replicaBlockSize I r) := hmoment
      _ ≤ C * σ ^ (replicaBlockSize I r) := by
          exact mul_le_mul
            (le_trans (ccr25GaussianMomentUniformConstant_le_of_le hrsize) hCgauss)
            hpow (pow_nonneg (abs_nonneg β) _) hC0)
    · simp only [ite_eq_right hs, abs_one, pow_zero, mul_one]
      exact hC1
  have hprod :
      (∏ r ∈ reps,
        |if 2 ≤ replicaBlockSize I r then
          gaussianDisorderMoment β (replicaBlockSize I r) else 1|) ≤
        ∏ r ∈ reps,
          C * σ ^ (if 2 ≤ replicaBlockSize I r then replicaBlockSize I r else 0) := by
    apply Finset.prod_le_prod₀
    · intro r hr
      exact abs_nonneg _
    · intro r hr
      exact hfactor r hr
  have hprodEq :
      (∏ r ∈ reps,
        C * σ ^ (if 2 ≤ replicaBlockSize I r then replicaBlockSize I r else 0)) =
        C ^ reps.card *
          σ ^ (∑ r ∈ reps,
            if 2 ≤ replicaBlockSize I r then replicaBlockSize I r else 0) := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.prod_pow_eq_pow_sum]
  have hsumEq :
      (∑ r ∈ reps,
        if 2 ≤ replicaBlockSize I r then replicaBlockSize I r else 0) =
        ∑ r ∈ nontriv, replicaBlockSize I r := by
    simp [nontriv, reps, ccr25NontrivialBlockRepresentatives, Finset.sum_filter]
  have hcover := collisionLabels_subset_representativeBlocks I
  have hcoverCard : (ccr25PartitionCollisionLabels I).card ≤
      ∑ r ∈ nontriv, replicaBlockSize I r := by
    calc
      (ccr25PartitionCollisionLabels I).card ≤
          ((nontriv).biUnion (ccr25ReplicaBlockLabels I)).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ r ∈ nontriv, (ccr25ReplicaBlockLabels I r).card := by
        simpa using (Finset.card_biUnion_le
          (s := nontriv) (t := ccr25ReplicaBlockLabels I))
      _ = ∑ r ∈ nontriv, replicaBlockSize I r := by
        simp [ccr25ReplicaBlockLabels, replicaBlockSize]
  have hrepCard : reps.card ≤ h := by
    calc
      reps.card ≤ Fintype.card (Fin h) := Finset.card_le_univ _
      _ = h := by simp
  have hCpow : C ^ reps.card ≤ C ^ h := pow_le_pow_right₀ hC1 hrepCard
  have hσpow : σ ^ (∑ r ∈ reps,
      if 2 ≤ replicaBlockSize I r then replicaBlockSize I r else 0) ≤
      σ ^ (ccr25PartitionCollisionLabels I).card := by
    rw [hsumEq]
    exact pow_le_pow_of_le_one hσ0 hσ1 hcoverCard
  calc
    |replicaPartitionDisorderMoment β I| =
        ∏ r ∈ reps,
          |if 2 ≤ replicaBlockSize I r then
            gaussianDisorderMoment β (replicaBlockSize I r) else 1| := by
      simp [replicaPartitionDisorderMoment, reps, Finset.abs_prod]
    _ ≤ ∏ r ∈ reps,
          C * σ ^ (if 2 ≤ replicaBlockSize I r then replicaBlockSize I r else 0) := hprod
    _ = C ^ reps.card *
          σ ^ (∑ r ∈ reps,
            if 2 ≤ replicaBlockSize I r then replicaBlockSize I r else 0) := hprodEq
    _ ≤ C ^ h * σ ^ (ccr25PartitionCollisionLabels I).card :=
      mul_le_mul hCpow hσpow
        (pow_nonneg hσ0 _) (pow_nonneg hC0 _)


/-- Gaussian full-support bound for a word of nontrivial replica partitions.
The collision-label sets are the blocks in the incidence estimate, so the
power is exactly `max(2r,h)`. -/
theorem ccr25_gaussian_partitionWord_moment_bound {h n : ℕ} (β : ℝ)
    (I : Fin (n + 1) → ReplicaPartition h)
    (hpart : ∀ j, I j ≠ ⊥)
    (hfull : ccr25WordFullSupport I)
    (hσ : Critical2DKPZ.Polymer.sigmaSq β ≤ 1) :
    |∏ j : Fin (n + 1), replicaPartitionDisorderMoment β (I j)| ≤
      (max 1 (ccr25GaussianMomentUniformConstant h)) ^ (h * (n + 1)) *
        Real.sqrt (Critical2DKPZ.Polymer.sigmaSq β) ^ Nat.max (2 * (n + 1)) h := by
  let blocks : Fin (n + 1) → Finset (Fin h) :=
    fun j => ccr25PartitionCollisionLabels (I j)
  have hnontrivial : ∀ j, 2 ≤ (blocks j).card := by
    intro j
    exact ccr25PartitionCollisionLabels_card_ge_two (I j) (hpart j)
  have hsupport : ∀ i : Fin h, ∃ j : Fin (n + 1), i ∈ blocks j := by
    intro i
    obtain ⟨j, hcoll⟩ := hfull i
    exact ⟨j, by simpa [blocks, ccr25PartitionCollisionLabels] using hcoll⟩
  have hmom : ∀ j : Fin (n + 1),
      |replicaPartitionDisorderMoment β (I j)| ≤
        (max 1 (ccr25GaussianMomentUniformConstant h)) ^ h *
          Real.sqrt (Critical2DKPZ.Polymer.sigmaSq β) ^ (blocks j).card := by
    intro j
    simpa [blocks] using abs_replicaPartitionDisorderMoment_le_supportPower β (I j) hσ
  have hbase := ccr25_fullSupport_product_bound blocks
    (fun j => replicaPartitionDisorderMoment β (I j))
    ((max 1 (ccr25GaussianMomentUniformConstant h)) ^ h)
    (Real.sqrt (Critical2DKPZ.Polymer.sigmaSq β))
    (pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (le_max_left _ _)) _)
    (Real.sqrt_nonneg _) (by simpa using Real.sqrt_le_sqrt hσ)
    hnontrivial hsupport hmom
  have hconst :
      ((max 1 (ccr25GaussianMomentUniformConstant h)) ^ h) ^ (n + 1) =
        (max 1 (ccr25GaussianMomentUniformConstant h)) ^ (h * (n + 1)) := by
    rw [← pow_mul]
  simpa [hconst, blocks] using hbase

end

end Critical2DKPZ.MomentBounds
