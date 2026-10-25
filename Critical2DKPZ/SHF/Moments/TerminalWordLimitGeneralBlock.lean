/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitDominationBlock
public import Critical2DKPZ.SHF.Moments.WordPotentialInduction
public import Critical2DKPZ.SHF.Moments.WordLimitDominationTimeEnvelope
public import Critical2DKPZ.SHF.Moments.WordLimitTerminalFirstBlock

/-! # First-block gap smoothing for arbitrary replica counts

For two distinct collision pairs, at least one label of the second pair is a spectator of the first, independently of the total number of replicas. -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

/-- Free-coordinate smoothing depends only on whether one or both tested
labels are free; all other coordinates integrate to unit mass. -/
private theorem exists_split_free_gap_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {h : ℕ} (S : Finset (Fin h)) (β : CollisionPair h),
      ¬ (β.1.1 ∈ S ∧ β.1.2 ∈ S) → ∀ (m n : ℕ) (x : LatticeConfiguration h)
      (p : LatticeConfiguration S.card),
      let xC : LatticeConfiguration Sᶜ.card := fun j => x (Sᶜ.orderEmbOfFin rfl j)
      let e := Tsai.splitFinsetCoordinates S Site
      (∑ q ∈ collisionWordConfigurationEndpointSet m xC,
        (∏ j, srwKernel m (q j - xC j)) *
          wordGapPotential n ((e.symm (p, q)) β.1.2 - (e.symm (p, q)) β.1.1)) ≤
        C * wordGapTimeEnvelope m := by
  obtain ⟨C₁, hC₁, hone⟩ := exists_freeReplicaKernel_oneGapPotential_bound_explicit
  obtain ⟨C₂, hC₂, htwo⟩ := exists_freeReplicaKernel_pairGapPotential_bound_explicit
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, fun {h} S β hnotboth m n x p => ?_⟩
  classical
  let xC : LatticeConfiguration Sᶜ.card := fun j => x (Sᶜ.orderEmbOfFin rfl j)
  let e := Tsai.splitFinsetCoordinates S Site
  let R := wordGapTimeEnvelope m
  have hR : 0 ≤ R := wordGapTimeEnvelope_nonneg _
  have hbound₁ : C₁ * R ≤ (C₁ + C₂) * R :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂.le) hR
  have hbound₂ : C₂ * R ≤ (C₁ + C₂) * R :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁.le) hR
  have hidx (D : Finset (Fin h)) (i : Fin h) (hi : i ∈ D) :
      ∃ j : Fin D.card, D.orderEmbOfFin rfl j = i := by
    change i ∈ Set.range (D.orderEmbOfFin rfl)
    simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using hi
  change (∑ q ∈ collisionWordConfigurationEndpointSet m xC,
    (∏ j, srwKernel m (q j - xC j)) *
      wordGapPotential n ((e.symm (p, q)) β.1.2 - (e.symm (p, q)) β.1.1)) ≤ (C₁ + C₂) * R
  by_cases hb₁ : β.1.1 ∈ S
  · have hb₂ : β.1.2 ∉ S := fun hb₂ => hnotboth ⟨hb₁, hb₂⟩
    obtain ⟨jS, hjS⟩ := hidx S β.1.1 hb₁
    obtain ⟨jC, hjC⟩ := hidx Sᶜ β.1.2 (Finset.mem_compl.mpr hb₂)
    have hc₁ (q : LatticeConfiguration Sᶜ.card) : (e.symm (p, q)) β.1.1 = p jS := by
      rw [← hjS]
      exact splitSubsetConfig_symm_selected S p q jS
    have hc₂ (q : LatticeConfiguration Sᶜ.card) : (e.symm (p, q)) β.1.2 = q jC := by
      rw [← hjC]
      exact splitSubsetConfig_symm_complement S p q jC
    simp_rw [hc₁, hc₂]
    exact (hone m n xC jC (p jS)).trans hbound₁
  · by_cases hb₂ : β.1.2 ∈ S
    · obtain ⟨jC, hjC⟩ := hidx Sᶜ β.1.1 (Finset.mem_compl.mpr hb₁)
      obtain ⟨jS, hjS⟩ := hidx S β.1.2 hb₂
      have hc₁ (q : LatticeConfiguration Sᶜ.card) : (e.symm (p, q)) β.1.1 = q jC := by
        rw [← hjC]
        exact splitSubsetConfig_symm_complement S p q jC
      have hc₂ (q : LatticeConfiguration Sᶜ.card) : (e.symm (p, q)) β.1.2 = p jS := by
        rw [← hjS]
        exact splitSubsetConfig_symm_selected S p q jS
      have hgap (q : LatticeConfiguration Sᶜ.card) :
          wordGapPotential n (p jS - q jC) = wordGapPotential n (q jC - p jS) := by
        simpa only [neg_sub] using wordGapPotential_neg n (q jC - p jS)
      simp_rw [hc₁, hc₂, hgap]
      exact (hone m n xC jC (p jS)).trans hbound₁
    · have hbC₁ : β.1.1 ∈ Sᶜ := Finset.mem_compl.mpr hb₁
      have hbC₂ : β.1.2 ∈ Sᶜ := Finset.mem_compl.mpr hb₂
      let γ := Tsai.collisionPairWithin Sᶜ β hbC₁ hbC₂
      have hc₁ (q : LatticeConfiguration Sᶜ.card) : (e.symm (p, q)) β.1.1 = q γ.1.1 := by
        rw [← Tsai.orderEmb_collisionPairWithin_fst Sᶜ β hbC₁ hbC₂]
        exact splitSubsetConfig_symm_complement S p q γ.1.1
      have hc₂ (q : LatticeConfiguration Sᶜ.card) : (e.symm (p, q)) β.1.2 = q γ.1.2 := by
        rw [← Tsai.orderEmb_collisionPairWithin_snd Sᶜ β hbC₁ hbC₂]
        exact splitSubsetConfig_symm_complement S p q γ.1.2
      simp_rw [hc₁, hc₂]
      exact (htwo γ m n xC).trans hbound₂


/-- A distinct next pair has a free endpoint in every replica count. -/
private theorem pair_not_both_active {h : ℕ} (α β : CollisionPair h) (hne : α ≠ β) :
    ¬ (β.1.1 ∈ ({α.1.1, α.1.2} : Finset (Fin h)) ∧
      β.1.2 ∈ ({α.1.1, α.1.2} : Finset (Fin h))) := by
  rintro ⟨hb₁, hb₂⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb₁ hb₂
  have ha := α.2
  have hb := β.2
  have h₁ : β.1.1 = α.1.1 := by
    rcases hb₁ with h₁ | h₁ <;> rcases hb₂ with h₂ | h₂ <;> omega
  have h₂ : β.1.2 = α.1.2 := by
    rcases hb₁ with h₁ | h₁ <;> rcases hb₂ with h₂ | h₂ <;> omega
  exact hne (Subtype.ext (Prod.ext h₁.symm h₂.symm))

/-- First-block smoothing with a constant uniform in every label count. -/
theorem exists_wordFirstBlock_gapPotential_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {h : ℕ}, ∀ (ρ : ℝ) (α β : CollisionPair h), α ≠ β →
      ∀ (s r n : ℕ) (x : LatticeConfiguration h),
      (∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        wordFirstBlockKernel ρ α s r x v * wordGapPotential n (v β.1.2 - v β.1.1)) ≤
        (C / Real.sqrt ((s : ℝ) + r + 1)) *
          (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
            (sigmaSq ρ * Renewal.renewalMass
              (fun k => sigmaSq ρ * Renewal.returnWeight k) r)) := by
  obtain ⟨D, hD, hfree⟩ := exists_split_free_gap_bound
  refine ⟨D * 4, mul_pos hD (by norm_num), fun {h} ρ α β hne s r n x => ?_⟩
  classical
  let S : Finset (Fin h) := {α.1.1, α.1.2}
  have hblock := wordFirstBlockKernel_test_le_of_free_average S ρ α
    (by simp [S]) (by simp [S]) s r x
    (fun v => wordGapPotential n (v β.1.2 - v β.1.1)) (D * wordGapTimeEnvelope (s + r))
    (fun p _ => hfree S β (pair_not_both_active α β hne) (s + r) n x p)
  have hmass : 0 ≤ srwKernel (2 * s) (x α.1.2 - x α.1.1) *
      (sigmaSq ρ * Renewal.renewalMass (fun k => sigmaSq ρ * Renewal.returnWeight k) r) := by
    rw [← sum_wordFirstBlockKernel ρ α s r x]
    exact Finset.sum_nonneg (fun v _ => wordFirstBlockKernel_nonneg ρ α s r x v)
  have ht := wordGapTimeEnvelope_le (s + r)
  simp only [Nat.cast_add] at ht
  apply hblock.trans
  convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hD.le) hmass using 1
  ring

end Critical2DKPZ.SHF.Moments
