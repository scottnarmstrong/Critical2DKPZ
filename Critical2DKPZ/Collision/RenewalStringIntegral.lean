/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.RenewalStringAbsoluteTerm
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Finite renewal-string sum to continuum integral

Disjoint half-shifted pair boxes convert the discrete renewal-string sum into a
lower integral over the occupied-block domain.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Collision

/-- Taking the nonnegative part is subadditive for a finite sum. -/
theorem ennreal_ofReal_sum_le_sum_ofReal {α : Type*} (s : Finset α)
    (f : α → ℝ) :
    ENNReal.ofReal (∑ x ∈ s, f x) ≤ ∑ x ∈ s, ENNReal.ofReal (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        ENNReal.ofReal (f a + ∑ x ∈ s, f x) ≤
            ENNReal.ofReal (f a) + ENNReal.ofReal (∑ x ∈ s, f x) :=
          ENNReal.ofReal_add_le
        _ ≤ ENNReal.ofReal (f a) + ∑ x ∈ s, ENNReal.ofReal (f x) :=
          by simpa [add_comm] using add_le_add_left ih (ENNReal.ofReal (f a))

/-- The renewal sum-to-integral bound: the finite renewal-string sum over occupied blocks is
bounded by the time integral over the half-shifted cells. -/
theorem renewalString_sum_le_integral (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ (m : ℕ) (lo hi : Fin (m + 1) → ℕ),
        (∀ j, lo j < hi j) → (∀ j : Fin m, hi j.castSucc ≤ lo j.succ) →
        hi (Fin.last m) ≤ N →
        ENNReal.ofReal (∑ a ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
          ∑ b ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
            if ∀ j, a j ≤ b j then
              (a 0 : ℝ)⁻¹ * (∏ j, criticalSigmaSq ϑ N *
                Renewal.criticalRenewalMass ϑ N (b j - a j)) *
                ∏ j : Fin m, (b j.castSucc : ℝ) /
                  (a j.succ * ((a j.succ : ℝ) - b j.castSucc))
            else 0) ≤
          ENNReal.ofReal (C ^ (m + 1)) *
            ∫⁻ p : Fin (m + 1) → ℝ × ℝ in {p | ∀ j,
              ((lo j : ℝ) + 1 / 2) / N < (p j).1 ∧
              (p j).1 < (p j).2 ∧ (p j).2 ≤ ((hi j : ℝ) + 1 / 2) / N},
              ENNReal.ofReal ((p 0).1⁻¹ *
                (∏ j, DeltaBose.scalarDensity
                  (ϑ - Real.eulerMascheroniConstant) ((p j).2 - (p j).1)) *
                ∏ j : Fin m, (p j.castSucc).2 /
                  ((p j.succ).1 * ((p j.succ).1 - (p j.castSucc).2))) := by
  classical
  by_cases hA : 0 ≤ A
  · obtain ⟨cCell, hcCell, hCell⟩ := exists_renewalStringPairCell_lower_all A hA
    let C : ℝ := 4 * (1 + cCell⁻¹)
    have hC : 0 < C := by
      dsimp [C]
      have hcinv : 0 < cCell⁻¹ := inv_pos.mpr hcCell
      positivity
    refine ⟨C, hC, ?_⟩
    intro N hN ϑ hϑ m lo hi hlo hsep hlast
    let S : Finset (Fin (m + 1) → ℕ) :=
      Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j))
    let valid : (Fin (m + 1) → ℕ) × (Fin (m + 1) → ℕ) → Prop :=
      fun z => ∀ j, z.1 j ≤ z.2 j
    let terms : (Fin (m + 1) → ℕ) × (Fin (m + 1) → ℕ) → ℝ := fun z =>
      (z.1 0 : ℝ)⁻¹ *
        (∏ j, criticalSigmaSq ϑ N *
          Renewal.criticalRenewalMass ϑ N (z.2 j - z.1 j)) *
        ∏ j : Fin m, (z.2 j.castSucc : ℝ) /
          (z.1 j.succ * ((z.1 j.succ : ℝ) - z.2 j.castSucc))
    let boxes : (Fin (m + 1) → ℕ) × (Fin (m + 1) → ℕ) →
        Set (Fin (m + 1) → ℝ × ℝ) := fun z =>
      renewalStringPairBox N m z.1 z.2
    let target : Set (Fin (m + 1) → ℝ × ℝ) :=
      {p | ∀ j, ((lo j : ℝ) + 1 / 2) / N < (p j).1 ∧
        (p j).1 < (p j).2 ∧ (p j).2 ≤ ((hi j : ℝ) + 1 / 2) / N}
    let density : (Fin (m + 1) → ℝ × ℝ) → ℝ≥0∞ := fun p =>
      ENNReal.ofReal (renewalStringPairBoxRational m p *
        renewalStringPairBoxDensity (ϑ - Real.eulerMascheroniConstant) m p)
    let T : Finset ((Fin (m + 1) → ℕ) × (Fin (m + 1) → ℕ)) :=
      (S.product S).filter valid
    have hNpos : 0 < N := by omega
    have hhiMono : Monotone hi := Fin.monotone_iff_le_succ.mpr fun j => by
      have hnext : lo j.succ < hi j.succ := hlo j.succ
      exact (lt_of_le_of_lt (hsep j) hnext).le
    have hTmem (z : (Fin (m + 1) → ℕ) × (Fin (m + 1) → ℕ)) (hz : z ∈ T) :
        z.1 ∈ S ∧ z.2 ∈ S ∧ valid z := by
      exact (Finset.mem_filter.mp hz).1 |> fun hp =>
        ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2,
          (Finset.mem_filter.mp hz).2⟩
    have hindexBounds (z : (Fin (m + 1) → ℕ) × (Fin (m + 1) → ℕ))
        (hz : z ∈ T) :
        (∀ j, lo j < z.1 j) ∧ (∀ j, z.2 j ≤ hi j) := by
      obtain ⟨hz₁, hz₂, _⟩ := hTmem z hz
      constructor
      · intro j
        exact (Finset.mem_Ioc.mp (Fintype.mem_piFinset.mp hz₁ j)).1
      · intro j
        exact (Finset.mem_Ioc.mp (Fintype.mem_piFinset.mp hz₂ j)).2
    have hvalid (z : (Fin (m + 1) → ℕ) × (Fin (m + 1) → ℕ)) (hz : z ∈ T) :
        ∀ j, z.1 j ≤ z.2 j := (hTmem z hz).2.2
    have hboxSubset (z : (Fin (m + 1) → ℕ) × (Fin (m + 1) → ℕ))
        (hz : z ∈ T) : boxes z ⊆ target := by
      obtain ⟨hloZ, hhiZB⟩ := hindexBounds z hz
      have hAlo : ∀ j, lo j < z.1 j := hloZ
      have hBhi : ∀ j, z.2 j ≤ hi j := hhiZB
      exact renewalStringPairBox_subset_target N m lo hi z.1 z.2 hNpos hAlo hBhi
        (hvalid z hz)
    have hdisj : Set.PairwiseDisjoint (↑T) boxes := by
      intro z hz w hw hzw
      have hzv := hvalid z hz
      have hwv := hvalid w hw
      have hneq : z.1 ≠ w.1 ∨ z.2 ≠ w.2 := by
        by_cases h₁ : z.1 = w.1
        · right
          intro h₂
          exact hzw (Prod.ext h₁ h₂)
        · exact Or.inl h₁
      exact renewalStringPairBox_disjoint N m hNpos z.1 z.2 w.1 w.2 hzv hwv hneq
    have hmeas : ∀ z ∈ T, MeasurableSet (boxes z) := by
      intro z hz
      exact measurableSet_renewalStringPairBox N m z.1 z.2
    have hsumReindex :
        (∑ a ∈ S, ∑ b ∈ S, ENNReal.ofReal
          (if valid (a, b) then terms (a, b) else 0)) =
          ∑ z ∈ T, ENNReal.ofReal (terms z) := by
      dsimp [T]
      rw [Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hab : valid (a, b)
      · change (∀ j, a j ≤ b j) at hab
        simp [valid, hab]
      · change ¬(∀ j, a j ≤ b j) at hab
        simp [valid, hab]
    have hsumOfReal :
        ENNReal.ofReal (∑ a ∈ S, ∑ b ∈ S,
          if valid (a, b) then terms (a, b) else 0) ≤
          ∑ z ∈ T, ENNReal.ofReal (terms z) := by
      calc
        _ ≤ ∑ a ∈ S, ENNReal.ofReal
            (∑ b ∈ S, if valid (a, b) then terms (a, b) else 0) :=
          ennreal_ofReal_sum_le_sum_ofReal S (fun a =>
            ∑ b ∈ S, if valid (a, b) then terms (a, b) else 0)
        _ ≤ ∑ a ∈ S, ∑ b ∈ S,
            ENNReal.ofReal (if valid (a, b) then terms (a, b) else 0) := by
          apply Finset.sum_le_sum
          intro a ha
          exact ennreal_ofReal_sum_le_sum_ofReal S (fun b =>
            if valid (a, b) then terms (a, b) else 0)
        _ = ∑ z ∈ T, ENNReal.ofReal (terms z) := hsumReindex
    have hcell (z : (Fin (m + 1) → ℕ) × (Fin (m + 1) → ℕ)) (hz : z ∈ T)
        (j : Fin (m + 1)) :
        ENNReal.ofReal (cCell / (N : ℝ) *
          |criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N
            (z.2 j - z.1 j)|) ≤
          ∫⁻ p in renewalStringPairCell N (z.1 j) (z.2 j),
            ENNReal.ofReal (DeltaBose.scalarDensity
              (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1)) := by
      have hbounds := hindexBounds z hz
      have haZ : 1 ≤ z.1 j := by
        have := hbounds.1 j
        omega
      have hbZN : z.2 j ≤ N :=
        (hbounds.2 j).trans ((hhiMono j.le_last).trans hlast)
      exact hCell N hN ϑ hϑ (z.1 j) (z.2 j)
        haZ (hvalid z hz j) hbZN
    have hterm (z : (Fin (m + 1) → ℕ) × (Fin (m + 1) → ℕ)) (hz : z ∈ T) :
        ENNReal.ofReal (terms z) ≤
          ENNReal.ofReal (C ^ (m + 1)) * ∫⁻ p in boxes z, density p := by
      obtain ⟨hz₁, hz₂, _⟩ := hTmem z hz
      obtain ⟨hloZ, hhiZ⟩ := hindexBounds z hz
      have hbN : ∀ j, z.2 j ≤ N := fun j =>
        (hhiZ j).trans ((hhiMono j.le_last).trans hlast)
      have hcellZ : ∀ j : Fin (m + 1),
          ENNReal.ofReal (cCell / (N : ℝ) *
            |criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N
              (z.2 j - z.1 j)|) ≤
            ∫⁻ p in renewalStringPairCell N (z.1 j) (z.2 j),
              ENNReal.ofReal (DeltaBose.scalarDensity
                (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1)) :=
        fun j => hcell z hz j
      have hterm' := renewalStringPairBox_absTerm_le N m lo hi z.1 z.2 ϑ cCell
        hNpos hcCell hloZ hhiZ hsep (hvalid z hz) hbN hcellZ
      simpa [C, boxes, density, terms, renewalStringPairBoxRational,
        renewalStringPairBoxDensity, mul_assoc, mul_left_comm, mul_comm] using hterm'
    have hsumTerm :
        (∑ z ∈ T, ENNReal.ofReal (terms z)) ≤
          ENNReal.ofReal (C ^ (m + 1)) * ∑ z ∈ T, ∫⁻ p in boxes z, density p := by
      calc
        _ ≤ ∑ z ∈ T,
            ENNReal.ofReal (C ^ (m + 1)) * ∫⁻ p in boxes z, density p :=
          Finset.sum_le_sum fun z hz => hterm z hz
        _ = _ := by rw [Finset.mul_sum]
    have hunion :
        ∫⁻ p in ⋃ z ∈ T, boxes z, density p =
          ∑ z ∈ T, ∫⁻ p in boxes z, density p :=
      lintegral_biUnion_finset hdisj hmeas density
    have hsub : (⋃ z ∈ T, boxes z) ⊆ target := by
      intro p hp
      rcases Set.mem_iUnion.mp hp with ⟨z, hpz⟩
      rcases Set.mem_iUnion.mp hpz with ⟨hz, hpz⟩
      exact hboxSubset z hz hpz
    have htarget :
        ∫⁻ p in target, density p ≤
          ∫⁻ p in target, ENNReal.ofReal
            ((p 0).1⁻¹ *
              (∏ j, DeltaBose.scalarDensity
                (ϑ - Real.eulerMascheroniConstant) ((p j).2 - (p j).1)) *
              ∏ j : Fin m, (p j.castSucc).2 /
                ((p j.succ).1 * ((p j.succ).1 - (p j.castSucc).2))) := by
      apply lintegral_mono
      intro p
      unfold density renewalStringPairBoxRational renewalStringPairBoxDensity
      apply ENNReal.ofReal_le_ofReal
      ring_nf
      exact le_rfl
    calc
      ENNReal.ofReal (∑ a ∈ S, ∑ b ∈ S,
          if valid (a, b) then terms (a, b) else 0) ≤
        ∑ z ∈ T, ENNReal.ofReal (terms z) := hsumOfReal
      _ ≤ ENNReal.ofReal (C ^ (m + 1)) *
          ∑ z ∈ T, ∫⁻ p in boxes z, density p := hsumTerm
      _ = ENNReal.ofReal (C ^ (m + 1)) *
          ∫⁻ p in ⋃ z ∈ T, boxes z, density p := by rw [hunion]
      _ ≤ ENNReal.ofReal (C ^ (m + 1)) * ∫⁻ p in target, density p :=
        mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) zero_le
      _ ≤ ENNReal.ofReal (C ^ (m + 1)) *
          ∫⁻ p in target, ENNReal.ofReal
            ((p 0).1⁻¹ *
              (∏ j, DeltaBose.scalarDensity
                (ϑ - Real.eulerMascheroniConstant) ((p j).2 - (p j).1)) *
              ∏ j : Fin m, (p j.castSucc).2 /
                ((p j.succ).1 * ((p j.succ).1 - (p j.castSucc).2))) :=
        mul_le_mul_of_nonneg_left htarget zero_le
      _ = _ := rfl
  · refine ⟨1, by norm_num, ?_⟩
    intro N hN ϑ hϑ m lo hi hlo hsep hlast
    exfalso
    have : -A ≤ A := le_trans hϑ.1 hϑ.2
    linarith

end Critical2DKPZ.Collision

end
