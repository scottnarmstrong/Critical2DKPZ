/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25PartitionMoments
public import Critical2DKPZ.MomentBounds.PairCrossLabels
public import Critical2DKPZ.MomentBounds.PairSelection
public import Critical2DKPZ.Renewal.CriticalWindow
import Mathlib.Tactic

/-! # The extra variance power of non-pair partition moments -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Critical2DKPZ.Renewal Polymer

/-- A nontrivial partition other than a single pair has at least three
labels in nonsingleton blocks. -/
theorem nonpairPartition_collisionLabels_card_ge_three {h : ℕ}
    (I : ReplicaPartition h) (hI : I ≠ ⊥)
    (hpair : ∀ α : CollisionPair h, I ≠ pairPartition α) :
    3 ≤ (ccr25PartitionCollisionLabels I).card := by
  classical
  obtain ⟨α, β, hα, hβ, hαβ⟩ := exists_distinct_collisionPairs I I hI hI
    (by intro α hboth; exact hpair α hboth.1)
  obtain ⟨k, l, m, n, hkl, hmn, hkout, hmout⟩ := exists_pairCrossLabels α β hαβ
  have hmem (i : Fin h) (hi : InCollisionBlock I i) :
      i ∈ ccr25PartitionCollisionLabels I :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have hk : k ∈ ccr25PartitionCollisionLabels I := by
    rcases hkl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmem _ ⟨α.1.2, (ne_of_lt α.2).symm, hα⟩
    · exact hmem _ ⟨α.1.1, ne_of_lt α.2, I.symm' hα⟩
  have hb1 : β.1.1 ∈ ccr25PartitionCollisionLabels I :=
    hmem _ ⟨β.1.2, (ne_of_lt β.2).symm, hβ⟩
  have hb2 : β.1.2 ∈ ccr25PartitionCollisionLabels I :=
    hmem _ ⟨β.1.1, ne_of_lt β.2, I.symm' hβ⟩
  have hkb1 : k ≠ β.1.1 := by
    intro he
    apply hkout
    simp [collisionPairLabels, he]
  have hkb2 : k ≠ β.1.2 := by
    intro he
    apply hkout
    simp [collisionPairLabels, he]
  have hsub : ({k, β.1.1, β.1.2} : Finset (Fin h)) ⊆
      ccr25PartitionCollisionLabels I := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact hk
    · exact hb1
    · exact hb2
  have hcard : ({k, β.1.1, β.1.2} : Finset (Fin h)).card = 3 := by
    simp [hkb1, hkb2, ne_of_lt β.2]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- The Gaussian moment of a non-pair partition has an extra square-root
variance factor compared with a single pair, uniformly in the partition. -/
theorem abs_nonpairPartitionDisorderMoment_le (h : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (I : ReplicaPartition h), sigmaSq β ≤ 1 →
      I ≠ ⊥ → (∀ α : CollisionPair h, I ≠ pairPartition α) →
      |replicaPartitionDisorderMoment β I| ≤
        C * sigmaSq β * Real.sqrt (sigmaSq β) := by
  let C : ℝ := (max 1 (ccr25GaussianMomentUniformConstant h)) ^ h
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro β I hσ hI hpair
  have hsqrt : 0 ≤ Real.sqrt (sigmaSq β) := Real.sqrt_nonneg _
  have hsqrt1 : Real.sqrt (sigmaSq β) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hσ
  have hcard := nonpairPartition_collisionLabels_card_ge_three I hI hpair
  calc
    _ ≤ C * Real.sqrt (sigmaSq β) ^ (ccr25PartitionCollisionLabels I).card :=
      abs_replicaPartitionDisorderMoment_le_supportPower β I hσ
    _ ≤ C * Real.sqrt (sigmaSq β) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hsqrt hsqrt1 hcard) hC
    _ = C * sigmaSq β * Real.sqrt (sigmaSq β) := by
      rw [pow_succ, Real.sq_sqrt (sigmaSq_nonneg β)]
      ring

/-- At critical tuning, every non-pair partition moment is uniformly
negligible relative to the pair variance. -/
theorem eventually_nonpairPartitionDisorderMoment_le_epsilon_sigmaSq
    (h : ℕ) (ϑ ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ I : ReplicaPartition h, I ≠ ⊥ →
      (∀ α : CollisionPair h, I ≠ pairPartition α) →
      |replicaPartitionDisorderMoment (criticalBeta ϑ N) I| ≤
        ε * sigmaSq (criticalBeta ϑ N) := by
  obtain ⟨C, hC, hmoment⟩ := abs_nonpairPartitionDisorderMoment_le h
  have hsqrt : Tendsto (fun N => Real.sqrt (criticalSigmaSq ϑ N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp (tendsto_sigma_zero ϑ)
  have hsmall := (tendsto_order.mp hsqrt).2 (ε / (C + 1)) (by positivity)
  have hσone := (tendsto_order.mp (tendsto_sigma_zero ϑ)).2 1 (by norm_num)
  filter_upwards [hsmall, hσone, criticalBeta_spec ϑ] with N hsmall hσone hβ
  intro I hI hpair
  have hβeq : sigmaSq (criticalBeta ϑ N) = criticalSigmaSq ϑ N := by
    simpa [sigmaSq] using hβ
  have hσ : 0 ≤ sigmaSq (criticalBeta ϑ N) := sigmaSq_nonneg _
  have hCsmall : C * Real.sqrt (sigmaSq (criticalBeta ϑ N)) ≤ ε := by
    rw [hβeq]
    have hmul := (le_div_iff₀ (show 0 < C + 1 by positivity)).mp hsmall.le
    nlinarith only [hmul, Real.sqrt_nonneg (criticalSigmaSq ϑ N)]
  calc
    _ ≤ C * sigmaSq (criticalBeta ϑ N) * Real.sqrt (sigmaSq (criticalBeta ϑ N)) :=
      hmoment _ I (by rw [hβeq]; exact hσone.le) hI hpair
    _ = sigmaSq (criticalBeta ϑ N) *
        (C * Real.sqrt (sigmaSq (criticalBeta ϑ N))) := by ring
    _ ≤ sigmaSq (criticalBeta ϑ N) * ε := mul_le_mul_of_nonneg_left hCsmall hσ
    _ = _ := mul_comm _ _

end Critical2DKPZ.SHF.Moments

end
