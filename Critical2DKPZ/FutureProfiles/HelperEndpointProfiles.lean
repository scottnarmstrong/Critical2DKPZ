/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Expansion
public import Critical2DKPZ.FutureProfiles.Basic
import Mathlib.Tactic

/-! # Profiles of open block correctors -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks

/-- The profile pairing of an open corrector is its open discrepancy mass divided by the block
normalizer. -/
theorem profileP2Fun_openCorrector_eq (β : ℝ) {t : ℕ → ℕ} (_ht : Monotone t) (T : ℕ)
    {u s : ℕ} (_hu : 1 ≤ u) (_hus : u ≤ s) (_hsT : t s ≤ T) (ω : Disorder) :
    profileP2Fun β (t s) T (openCorrector β t u s ω) (fun _ => 1) ω =
      openDiscrepancyMass β t T u (s + 1) ω /
        ∏ i ∈ Finset.Icc u s, blockMass β t i ω := by
  let X : Finset Site := Polymer.endpoints 0 (t (u - 1))
  let Y (x : Site) : Finset Site := discrepancyStringSupport t u (s + 1 - u) x
  let S : Finset Site := X.biUnion Y
  let P : ℝ := ∏ i ∈ Finset.Icc u s, blockMass β t i ω
  have hP : P ≠ 0 := by
    dsimp [P]
    exact ne_of_gt (Finset.prod_pos fun i _ => blockMass_pos β t i ω)
  have hnum (y : Site) :
      openCorrectorNumerator β t u s ω y =
        ∑ x ∈ X, srwKernel (t (u - 1)) x * discrepancyString β t u (s + 1 - u) x y ω := by
    unfold openCorrectorNumerator
    apply tsum_eq_sum
    intro x hx
    have hkernel : srwKernel (t (u - 1)) x = 0 := by
      simpa only [sub_zero] using
        Polymer.srwKernel_eq_zero_of_not_mem (t (u - 1)) 0 x (by simpa [X] using hx)
    rw [hkernel]
    ring
  have hnumZero (y : Site) (hy : y ∉ S) : openCorrectorNumerator β t u s ω y = 0 := by
    exact openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y
      (by simpa [S, X, Y, openCorrectorNumeratorSupport] using hy)
  have hsupport : ∀ y ∉ S, openCorrector β t u s ω y = 0 := by
    intro y hy
    rw [openCorrector, hnumZero y hy, zero_div]
  have hfinite :
      (∑ y ∈ S,
        openCorrectorNumerator β t u s ω y *
          pointToPlane β (t s) (T - t s) y ω) =
        openDiscrepancyMass β t T u (s + 1) ω := by
    have hOuter :
        (∑' x, ∑' y,
          srwKernel (t (u - 1)) x * discrepancyString β t u (s + 1 - u) x y ω *
            pointToPlane β (t (s + 1 - 1)) (T - t (s + 1 - 1)) y ω) =
        ∑ x ∈ X, ∑' y,
          srwKernel (t (u - 1)) x * discrepancyString β t u (s + 1 - u) x y ω *
            pointToPlane β (t (s + 1 - 1)) (T - t (s + 1 - 1)) y ω := by
      apply tsum_eq_sum
      intro x hx
      have hkernel : srwKernel (t (u - 1)) x = 0 := by
        simpa only [sub_zero] using
          Polymer.srwKernel_eq_zero_of_not_mem (t (u - 1)) 0 x (by simpa [X] using hx)
      rw [hkernel]
      simp
    have hInner (x : Site) :
        (∑' y,
          srwKernel (t (u - 1)) x * discrepancyString β t u (s + 1 - u) x y ω *
            pointToPlane β (t (s + 1 - 1)) (T - t (s + 1 - 1)) y ω) =
        ∑ y ∈ Y x,
          srwKernel (t (u - 1)) x * discrepancyString β t u (s + 1 - u) x y ω *
            pointToPlane β (t (s + 1 - 1)) (T - t (s + 1 - 1)) y ω := by
      apply tsum_eq_sum
      intro y hy
      rw [discrepancyString_eq_zero_of_not_mem_support β t u (s + 1 - u)
        x y ω (by simpa [Y] using hy)]
      simp
    have hdouble : openDiscrepancyMass β t T u (s + 1) ω =
        ∑ x ∈ X, ∑ y ∈ Y x,
          srwKernel (t (u - 1)) x * discrepancyString β t u (s + 1 - u) x y ω *
            pointToPlane β (t s) (T - t s) y ω := by
      unfold openDiscrepancyMass
      rw [hOuter]
      have hsum := congrArg (fun f : Site → ℝ => ∑ x ∈ X, f x) (funext hInner)
      simpa only [Nat.add_sub_cancel] using hsum
    rw [hdouble]
    calc
      _ = ∑ y ∈ S, ∑ x ∈ X,
          srwKernel (t (u - 1)) x * discrepancyString β t u (s + 1 - u) x y ω *
            pointToPlane β (t s) (T - t s) y ω := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hnum y]
          rw [Finset.sum_mul]
      _ = ∑ x ∈ X, ∑ y ∈ S,
          srwKernel (t (u - 1)) x * discrepancyString β t u (s + 1 - u) x y ω *
            pointToPlane β (t s) (T - t s) y ω := by
          rw [Finset.sum_comm]
      _ = ∑ x ∈ X, ∑ y ∈ Y x,
          srwKernel (t (u - 1)) x * discrepancyString β t u (s + 1 - u) x y ω *
            pointToPlane β (t s) (T - t s) y ω := by
          apply Finset.sum_congr rfl
          intro x hx
          have hYsub : Y x ⊆ S := by
            intro y hy
            exact Finset.mem_biUnion.mpr ⟨x, by simpa [X] using hx, by simpa [Y] using hy⟩
          symm
          apply Finset.sum_subset hYsub
          intro y hyS hyY
          rw [discrepancyString_eq_zero_of_not_mem_support β t u (s + 1 - u)
            x y ω (by simpa [Y] using hyY)]
          simp
  have hprofile :
      profileP2Fun β (t s) T (openCorrector β t u s ω) (fun _ => 1) ω =
        (∑ y ∈ S,
          openCorrectorNumerator β t u s ω y *
            pointToPlane β (t s) (T - t s) y ω) / P := by
    rw [Polymer.profileP2Fun_eq_sum β (t s) T (openCorrector β t u s ω)
      (fun _ => 1) S hsupport ω]
    simp only [mul_one, Polymer.tsum_pointToPoint, openCorrector]
    calc
      _ = ∑ y ∈ S,
          (openCorrectorNumerator β t u s ω y *
            pointToPlane β (t s) (T - t s) y ω) / P := by
          apply Finset.sum_congr rfl
          intro y hy
          dsimp [P]
          field_simp [hP]
      _ = _ := by rw [Finset.sum_div]
  rw [hprofile, hfinite]

end Critical2DKPZ.FutureProfiles

end
