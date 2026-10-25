/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationFlatPairMoment
public import Critical2DKPZ.SHF.Moments.WordDominationLowOrder
public import Critical2DKPZ.SHF.Moments.WordDominationPositivity
public import Critical2DKPZ.SHF.Moments.CollisionWordMomentExpansion
import Mathlib.Tactic

/-! # Uniform geometric domination for two replicas -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose

/-- Two-replica word coefficients have a uniform geometric majorant. Only the
empty and one-letter words occur; their positive sum is bounded by sixth-moment bounds. -/
theorem testedBlockWord_geometric_le_two_replicas (ϑ : ℝ) {τ T : ℝ}
    (hτ : 0 < τ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
        ∀ m : ℕ, ∑ w : CollisionWord 2 m,
          |testedBlockWord ϑ N s t φ (List.ofFn w.1)| ≤ C * ρ ^ m := by
  obtain ⟨B, hB, hN⟩ := eventually_integral_compactAbs_pairing_product_le
    ϑ (φ 0) (φ 1) hτ
  let ψ : Fin 2 → C_c(Plane × Plane, ℝ) := fun i => compactAbs (φ i)
  refine ⟨2 * B, (1 / 2 : ℝ), mul_nonneg (by norm_num) hB,
    by norm_num, by norm_num, ?_⟩
  filter_upwards [hN] with N hN
  intro s t hs hτst ht m
  let F : ℕ → ℝ := fun m =>
    ∑ w : CollisionWord 2 m,
      testedBlockWord ϑ N s t ψ (List.ofFn w.1)
  let X : Fin 2 → Disorder → ℝ := fun i ω =>
    ∫ p : Plane × Plane, ψ i p * rescaledP2P ϑ N s t p ω ∂volume
  have hPairBound : ∫ ω, X 0 ω * X 1 ω ∂disorderLaw ≤ B := by
    have h := (hN s t hs hτst ht).2
    simpa [X, ψ] using h
  have hst : s ≤ t := by linarith
  have hid := integral_prod_pairing_eq_wordSum ϑ N hs hst ψ
  have hprodEq :
      (∫ ω, ∏ i : Fin 2, X i ω ∂disorderLaw) =
        ∫ ω, X 0 ω * X 1 ω ∂disorderLaw := by
    congr 1
    funext ω
    simp [X]
  rw [hprodEq] at hid
  rw [testedNonpairRemainder_eq_zero_of_h_le_two ϑ N (by omega) ψ] at hid
  have hFsum : (∑' m : ℕ, F m) = F 0 + F 1 := by
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [F, Finset.sum_range_succ]
    · intro m hm
      have hm2 : 2 ≤ m := by
        simp only [Finset.mem_range] at hm
        omega
      exact collisionWord_sum_eq_zero_of_h_le_two_of_two_le_length
        (h := 2) (m := m) (by omega) hm2 _
  have hid0 : (∫ ω, X 0 ω * X 1 ω ∂disorderLaw) = (∑' m : ℕ, F m) + 0 := by
    simpa [F] using hid
  have hid' : (∫ ω, X 0 ω * X 1 ω ∂disorderLaw) = F 0 + F 1 := by
    simpa only [hFsum, add_zero] using hid0
  have hFnonneg (m : ℕ) : 0 ≤ F m := by
    dsimp [F]
    apply Finset.sum_nonneg
    intro w hw
    exact testedBlockWord_nonneg ϑ N s t ψ
      (fun i p => by change 0 ≤ |φ i p|; positivity) (List.ofFn w.1)
  have htotal : F 0 + F 1 ≤ B := by
    rw [← hid']
    exact hPairBound
  have hF0 : F 0 ≤ B := by linarith [hFnonneg 1]
  have hF1 : F 1 ≤ B := by linarith [hFnonneg 0]
  have htest (m : ℕ) :
      (∑ w : CollisionWord 2 m,
        |testedBlockWord ϑ N s t φ (List.ofFn w.1)|) ≤ F m := by
    dsimp [F]
    apply Finset.sum_le_sum
    intro w hw
    exact abs_testedBlockWord_le_abs_testedBlockWord ϑ N s t φ (List.ofFn w.1)
  by_cases hm0 : m = 0
  · subst m
    calc
      _ ≤ F 0 := htest 0
      _ ≤ B := hF0
      _ ≤ 2 * B := by nlinarith
      _ = (2 * B) * (1 / 2 : ℝ) ^ 0 := by norm_num
  · by_cases hm1 : m = 1
    · subst m
      calc
        _ ≤ F 1 := htest 1
        _ ≤ B := hF1
        _ = (2 * B) * (1 / 2 : ℝ) ^ 1 := by norm_num; ring
    · have hm2 : 2 ≤ m := by omega
      have hzero :
          (∑ w : CollisionWord 2 m,
            |testedBlockWord ϑ N s t φ (List.ofFn w.1)|) = 0 := by
        exact collisionWord_sum_eq_zero_of_h_le_two_of_two_le_length
          (h := 2) (m := m) (by omega) hm2 _
      rw [hzero]
      positivity

/-- The geometric word estimate holds at replica orders at most two. -/
theorem testedBlockWord_geometric_le_of_h_le_two (ϑ : ℝ) {h : ℕ} (hh : h ≤ 2)
    {τ T : ℝ} (hτ : 0 < τ) (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
        ∀ m : ℕ, ∑ w : CollisionWord h m,
          |testedBlockWord ϑ N s t φ (List.ofFn w.1)| ≤ C * ρ ^ m := by
  have hcases : h = 0 ∨ h = 1 ∨ h = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact testedBlockWord_geometric_le_zero_replicas ϑ hτ φ
  · exact testedBlockWord_geometric_le_of_h_le_one ϑ (by omega) hτ φ
  · exact testedBlockWord_geometric_le_two_replicas ϑ hτ φ

end Critical2DKPZ.SHF.Moments

end
