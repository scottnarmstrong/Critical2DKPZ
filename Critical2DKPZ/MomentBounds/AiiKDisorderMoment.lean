/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25PartitionMoments
import Mathlib.Tactic

/-! # Small disorder moments for nontrivial replica partitions -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

private theorem pairPartition_disorderMoment_eq_sigmaSq {h : ℕ}
    (β : ℝ) (α : DeltaBose.CollisionPair h) :
    replicaPartitionDisorderMoment β (pairPartition α) = Polymer.sigmaSq β := by
  classical
  let a := α.val.1
  let b := α.val.2
  have hab : a < b := α.property
  have hsize (r : Fin h) :
      replicaBlockSize (pairPartition α) r = if r = a ∨ r = b then 2 else 1 := by
    unfold replicaBlockSize
    have hclass :
        (Finset.univ.filter (fun j : Fin h => (pairPartition α).r r j)) =
          if r = a ∨ r = b then ({a, b} : Finset (Fin h)) else {r} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (r = j ∨ (r = a ∨ r = b) ∧ (j = a ∨ j = b)) ↔
        j ∈ (if r = a ∨ r = b then ({a, b} : Finset (Fin h))
          else ({r} : Finset (Fin h)))
      by_cases hr : r = a ∨ r = b
      · rcases hr with hr | hr
        · subst r
          simp [hab.ne, eq_comm]
        · subst r
          simp [hab.ne, eq_comm]
          intro hj
          exact Or.inr hj
      · have hra : r ≠ a := fun h => hr (Or.inl h)
        have hrb : r ≠ b := fun h => hr (Or.inr h)
        simp [hra, hrb, eq_comm]
    rw [hclass]
    by_cases hr : r = a ∨ r = b <;> simp [hr, hab.ne]
  have hfilter :
      (replicaBlockRepresentatives (pairPartition α)).filter
          (fun r => 2 ≤ replicaBlockSize (pairPartition α) r) = {a} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hrmem, hs⟩
      rw [hsize] at hs
      by_cases hendpoint : r = a ∨ r = b
      · rcases hendpoint with hr | hr
        · exact hr
        · subst r
          have hleast := (Finset.mem_filter.mp hrmem).2 a
          have hrel : (pairPartition α).r b a := by
            change (b = a ∨ (b = a ∨ b = b) ∧ (a = a ∨ a = b))
            exact Or.inr ⟨Or.inr rfl, Or.inl rfl⟩
          have hle := hleast hrel
          omega
      · simp [hendpoint] at hs
    · intro hr
      subst r
      refine ⟨?_, ?_⟩
      · simp only [replicaBlockRepresentatives, Finset.mem_filter,
          Finset.mem_univ, true_and]
        intro j hj
        have hj' : j = a ∨ j = b := by
          change (a = j ∨ (a = a ∨ a = b) ∧ (j = a ∨ j = b)) at hj
          rcases hj with h | ⟨_, hj⟩
          · exact Or.inl h.symm
          · exact hj
        rcases hj' with rfl | rfl <;> omega
      · rw [hsize]
        simp
  have hmoment :
      replicaPartitionDisorderMoment β (pairPartition α) =
        gaussianDisorderMoment β 2 := by
    unfold replicaPartitionDisorderMoment
    rw [← Finset.prod_filter]
    rw [hfilter]
    simp [hsize]
  rw [hmoment]
  change (∫ ω : Disorder, Polymer.xi β (0, 0) ω ^ 2 ∂disorderLaw) = _
  exact Polymer.integral_xi_sq β (0, 0)

private theorem partition_eq_pair_of_collisionLabels_card_two {h : ℕ}
    (I : ReplicaPartition h) (hI : I ≠ ⊥)
    (hcard : (ccr25PartitionCollisionLabels I).card = 2) :
    ∃ α : DeltaBose.CollisionPair h, I = pairPartition α := by
  classical
  obtain ⟨α, hα⟩ := exists_collisionPair_of_ne_discrete I hI
  let a := α.val.1
  let b := α.val.2
  have hab : a < b := α.property
  have ha : InCollisionBlock I a := ⟨b, (ne_of_lt hab).symm, hα⟩
  have hb : InCollisionBlock I b := ⟨a, ne_of_lt hab, I.symm' hα⟩
  have hpairSubset : ({a, b} : Finset (Fin h)) ⊆ ccr25PartitionCollisionLabels I := by
    intro i hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · simpa [ccr25PartitionCollisionLabels, hi] using ha
    · have hi : i = b := (Finset.mem_singleton.mp hi)
      subst i
      simpa [ccr25PartitionCollisionLabels] using hb
  have hlabels : ({a, b} : Finset (Fin h)) = ccr25PartitionCollisionLabels I :=
    Finset.eq_of_subset_of_card_le hpairSubset (by simp [hab.ne, hcard])
  refine ⟨α, ?_⟩
  apply Setoid.ext
  intro i j
  change I.r i j ↔ i = j ∨ (i = a ∨ i = b) ∧ (j = a ∨ j = b)
  constructor
  · intro hij
    by_cases heq : i = j
    · exact Or.inl heq
    · have hi : i ∈ ccr25PartitionCollisionLabels I := by
        have hji : j ≠ i := fun hji => heq hji.symm
        simpa [ccr25PartitionCollisionLabels] using
          (show InCollisionBlock I i from ⟨j, hji, hij⟩)
      have hj : j ∈ ccr25PartitionCollisionLabels I := by
        have hij' : i ≠ j := fun hij' => heq hij'
        simpa [ccr25PartitionCollisionLabels] using
          (show InCollisionBlock I j from ⟨i, hij', I.symm' hij⟩)
      rw [← hlabels] at hi hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact (heq (hi.trans hj.symm)).elim
      · exact Or.inr ⟨Or.inl hi, Or.inr hj⟩
      · exact Or.inr ⟨Or.inr hi, Or.inl hj⟩
      · exact (heq (hi.trans hj.symm)).elim
  · intro hij
    rcases hij with hij | ⟨hi, hj⟩
    · subst j
      exact I.refl' i
    · rcases hi with hi | hi <;> rcases hj with hj | hj
      · subst i; subst j; exact I.refl' a
      · subst i; subst j; exact hα
      · subst i; subst j; exact I.symm' hα
      · subst i; subst j; exact I.refl' b

private theorem collisionLabels_card_ge_three_of_not_pair {h : ℕ}
    (I : ReplicaPartition h) (hI : I ≠ ⊥)
    (hpair : ∀ α : DeltaBose.CollisionPair h, I ≠ pairPartition α) :
    3 ≤ (ccr25PartitionCollisionLabels I).card := by
  by_contra hn
  have hge2 : 2 ≤ (ccr25PartitionCollisionLabels I).card := by
    obtain ⟨α, hα⟩ := exists_collisionPair_of_ne_discrete I hI
    let a := α.val.1
    let b := α.val.2
    have hab : a < b := α.property
    have ha : InCollisionBlock I a := ⟨b, (ne_of_lt hab).symm, hα⟩
    have hb : InCollisionBlock I b := ⟨a, ne_of_lt hab, I.symm' hα⟩
    have hsub : ({a, b} : Finset (Fin h)) ⊆ ccr25PartitionCollisionLabels I := by
      intro i hi
      rcases Finset.mem_insert.mp hi with hi | hi
      · simpa [ccr25PartitionCollisionLabels, hi] using ha
      · have hi : i = b := Finset.mem_singleton.mp hi
        subst i
        simpa [ccr25PartitionCollisionLabels] using hb
    calc
      2 = ({a, b} : Finset (Fin h)).card := by simp [hab.ne]
      _ ≤ (ccr25PartitionCollisionLabels I).card := Finset.card_le_card hsub
  have hcard : (ccr25PartitionCollisionLabels I).card = 2 := by omega
  obtain ⟨α, heq⟩ := partition_eq_pair_of_collisionLabels_card_two I hI hcard
  exact hpair α heq

/-- A nontrivial partition disorder moment is at most one variance factor when
the Gaussian variance parameter is sufficiently small, uniformly over the
partition. -/
theorem abs_replicaPartitionDisorderMoment_le_sigmaSq (h : ℕ) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ β : ℝ, Polymer.sigmaSq β ≤ σ₀ →
      ∀ I : ReplicaPartition h, I ≠ ⊥ →
        |replicaPartitionDisorderMoment β I| ≤ Polymer.sigmaSq β := by
  let C : ℝ := max 1 (ccr25GaussianMomentUniformConstant h)
  let σ₀ : ℝ := (C ^ h)⁻¹ ^ 2
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC1
  have hChpos : 0 < C ^ h := pow_pos hCpos _
  refine ⟨σ₀, by positivity, fun β hσ I hI => ?_⟩
  have hσnonneg : 0 ≤ Polymer.sigmaSq β := sigmaSq_nonneg β
  have hsqrt : Real.sqrt (Polymer.sigmaSq β) ≤ (C ^ h)⁻¹ := by
    calc
      Real.sqrt (Polymer.sigmaSq β) ≤ Real.sqrt σ₀ := Real.sqrt_le_sqrt hσ
      _ = (C ^ h)⁻¹ := by
        rw [show σ₀ = ((C ^ h)⁻¹) ^ 2 by rfl, Real.sqrt_sq_eq_abs,
          abs_of_pos (inv_pos.mpr hChpos)]
  have hσle1 : Real.sqrt (Polymer.sigmaSq β) ≤ 1 :=
    hsqrt.trans (by
      rw [inv_le_one₀ hChpos]
      exact one_le_pow₀ hC1)
  by_cases hpair : ∃ α : DeltaBose.CollisionPair h, I = pairPartition α
  · obtain ⟨α, rfl⟩ := hpair
    rw [pairPartition_disorderMoment_eq_sigmaSq]
    exact le_of_eq (abs_of_nonneg hσnonneg)
  · have hcard : 3 ≤ (ccr25PartitionCollisionLabels I).card :=
      collisionLabels_card_ge_three_of_not_pair I hI (by
        intro α hα
        exact hpair ⟨α, hα⟩)
    have hsupport := abs_replicaPartitionDisorderMoment_le_supportPower β I
      (hσ.trans (by
        have : σ₀ ≤ 1 := by
          dsimp [σ₀]
          have hinv : (C ^ h)⁻¹ ≤ 1 := by
            rw [inv_le_one₀ hChpos]
            exact one_le_pow₀ hC1
          calc
            ((C ^ h)⁻¹) ^ 2 ≤ 1 ^ 2 :=
              pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt hChpos)) hinv 2
            _ = 1 := by norm_num
        exact this))
    have hCpow : 0 ≤ C ^ h := pow_nonneg (le_trans (by norm_num) hC1) _
    have hσpow :
        Real.sqrt (Polymer.sigmaSq β) ^ (ccr25PartitionCollisionLabels I).card ≤
          Real.sqrt (Polymer.sigmaSq β) ^ 3 :=
      pow_le_pow_of_le_one (Real.sqrt_nonneg _) hσle1 hcard
    have hCσ : C ^ h * Real.sqrt (Polymer.sigmaSq β) ≤ 1 := by
      calc
        C ^ h * Real.sqrt (Polymer.sigmaSq β) ≤ C ^ h * (C ^ h)⁻¹ :=
          mul_le_mul_of_nonneg_left hsqrt hCpow
        _ = 1 := by field_simp
    calc
      |replicaPartitionDisorderMoment β I| ≤
          C ^ h * Real.sqrt (Polymer.sigmaSq β) ^
            (ccr25PartitionCollisionLabels I).card := by
          simpa [C] using hsupport
      _ ≤ C ^ h * Real.sqrt (Polymer.sigmaSq β) ^ 3 :=
        mul_le_mul_of_nonneg_left hσpow hCpow
      _ = (Real.sqrt (Polymer.sigmaSq β) ^ 2) *
          (C ^ h * Real.sqrt (Polymer.sigmaSq β)) := by ring
      _ ≤ (Real.sqrt (Polymer.sigmaSq β) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hCσ (sq_nonneg _)
      _ = Polymer.sigmaSq β := by simp [Real.sq_sqrt hσnonneg]

end Critical2DKPZ.MomentBounds

end
