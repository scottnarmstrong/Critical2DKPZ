/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitFirstBlockAverage
public import Critical2DKPZ.SHF.Moments.WordLimitFreePair
public import Critical2DKPZ.SHF.Moments.WordLimitDominationLabels

/-! # One collision block acting on the next pair's gap potential -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- A single constant controls free-coordinate smoothing of a distinct next-pair gap at all replica orders up to four, uniformly in the coupling, durations and starting configuration. -/
theorem exists_wordFirstBlock_gapPotential_bound_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ {h : ℕ}, h ≤ 4 → ∀ (ρ : ℝ) (α β : CollisionPair h), α ≠ β →
      ∀ (s r n : ℕ) (x : LatticeConfiguration h),
      (∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        wordFirstBlockKernel ρ α s r x v * wordGapPotential n (v β.1.2 - v β.1.1)) ≤
        (C * wordGapTimeEnvelope (s + r)) *
          (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
            (sigmaSq ρ * Renewal.renewalMass (fun k => sigmaSq ρ * Renewal.returnWeight k) r)) := by
  obtain ⟨C₁, hC₁, hone⟩ := exists_freeReplicaKernel_oneGapPotential_bound_explicit
  obtain ⟨C₂, hC₂, htwo⟩ := exists_freeReplicaKernel_pairGapPotential_bound_explicit
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, fun {h} hh ρ α β hαβ s r n x => ?_⟩
  classical
  let S : Finset (Fin h) := {α.1.1, α.1.2}
  let xC : LatticeConfiguration Sᶜ.card := fun j => x (Sᶜ.orderEmbOfFin rfl j)
  let e := Tsai.splitFinsetCoordinates S Site
  let R := wordGapTimeEnvelope (s + r)
  have hR : 0 ≤ R := wordGapTimeEnvelope_nonneg _
  have hbound₁ : C₁ * R ≤ (C₁ + C₂) * R :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂.le) hR
  have hbound₂ : C₂ * R ≤ (C₁ + C₂) * R :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁.le) hR
  have hidx (D : Finset (Fin h)) (i : Fin h) (hi : i ∈ D) :
      ∃ j : Fin D.card, D.orderEmbOfFin rfl j = i := by
    change i ∈ Set.range (D.orderEmbOfFin rfl)
    simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using hi
  obtain ⟨i, hiβ, hi₁, hi₂⟩ := collisionPair_free_endpoint_of_le_four hh α β hαβ
  have hiS : i ∉ S := by simp [S, hi₁, hi₂]
  have hnotboth : ¬ (β.1.1 ∈ S ∧ β.1.2 ∈ S) := by
    rintro ⟨hb₁, hb₂⟩
    apply hiS
    rcases hiβ with rfl | rfl
    · exact hb₁
    · exact hb₂
  refine wordFirstBlockKernel_test_le_of_free_average S ρ α
    (by simp [S]) (by simp [S]) s r x
    (fun v => wordGapPotential n (v β.1.2 - v β.1.1)) ((C₁ + C₂) * R) ?_
  intro p _hp
  change (∑ q ∈ collisionWordConfigurationEndpointSet (s + r) xC,
    (∏ j, srwKernel (s + r) (q j - xC j)) *
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
    exact (hone (s + r) n xC jC (p jS)).trans hbound₁
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
      exact (hone (s + r) n xC jC (p jS)).trans hbound₁
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
      exact (htwo γ (s + r) n xC).trans hbound₂

end Critical2DKPZ.SHF.Moments
