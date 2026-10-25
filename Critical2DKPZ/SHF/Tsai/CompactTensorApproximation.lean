/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CompactTensorTests
public import Critical2DKPZ.SHF.Tsai.ContinuousTensorPresentation
import Mathlib.Topology.UrysohnsLemma

/-! # Uniform compact tensor approximation

Fixed endpoint cutoffs equal one on the projections of the original support.
Multiplying the continuous tensor approximations by these cutoffs preserves
the uniform error and bounds all term supports by one compact rectangle.
-/

@[expose] public noncomputable section

open Set
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Every compact plane-pair test is uniformly approximable by compact endpoint tensor sums in one compact rectangle. -/
theorem exists_compactTensorSum_uniform_approx (f : C_c(Plane × Plane, ℝ)) :
    ∃ K : Set (Plane × Plane), IsCompact K ∧ ∀ ε : ℝ, 0 < ε →
      ∃ r : ℕ, ∃ g g' : Fin r → C_c(Plane, ℝ),
        (∀ b, tsupport (compactTensorTest (g b) (g' b) : Plane × Plane → ℝ) ⊆ K) ∧
        ∀ p, |(∑ b, g b p.1 * g' b p.2) - f p| < ε := by
  classical
  obtain ⟨χ, hχone, hχc, _hχU, hχ01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (f.hasCompactSupport.image continuous_fst) isOpen_univ (subset_univ _)
  obtain ⟨χ', hχ'one, hχ'c, _hχ'U, hχ'01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (f.hasCompactSupport.image continuous_snd) isOpen_univ (subset_univ _)
  let K := tsupport (χ : Plane → ℝ) ×ˢ tsupport (χ' : Plane → ℝ)
  have hK : IsCompact K := hχc.prod hχ'c
  have hcut (p : Plane × Plane) : χ p.1 * χ' p.2 * f p = f p := by
    by_cases hp : p ∈ tsupport (f : Plane × Plane → ℝ)
    · rw [hχone ⟨p, hp, rfl⟩, hχ'one ⟨p, hp, rfl⟩]
      simp
    · rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]
  refine ⟨K, hK, fun ε hε => ?_⟩
  obtain ⟨r, a, a', ha⟩ := exists_continuousTensorSum_approx f.toContinuousMap hK hε
  let g (b : Fin r) : C_c(Plane, ℝ) :=
    ⟨⟨fun x => χ x * a b x, χ.continuous.mul (a b).continuous⟩, (show HasCompactSupport (χ : Plane → ℝ) from hχc).mul_right⟩
  let g' (b : Fin r) : C_c(Plane, ℝ) :=
    ⟨⟨fun x => χ' x * a' b x, χ'.continuous.mul (a' b).continuous⟩, (show HasCompactSupport (χ' : Plane → ℝ) from hχ'c).mul_right⟩
  have hsupport (b) : tsupport (compactTensorTest (g b) (g' b) : Plane × Plane → ℝ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro p hp
    have hp' : g b p.1 * g' b p.2 ≠ 0 := hp
    have hχ : χ p.1 ≠ 0 := fun hzero => hp' (by
      change (χ p.1 * a b p.1) * g' b p.2 = 0
      rw [hzero, zero_mul, zero_mul])
    have hχ' : χ' p.2 ≠ 0 := fun hzero => hp' (by
      change g b p.1 * (χ' p.2 * a' b p.2) = 0
      rw [hzero, zero_mul, mul_zero])
    exact ⟨subset_tsupport _ hχ, subset_tsupport _ hχ'⟩
  refine ⟨r, g, g', hsupport, fun p => ?_⟩
  have hsum : (∑ b, g b p.1 * g' b p.2) = χ p.1 * χ' p.2 * ∑ b, a b p.1 * a' b p.2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    change (χ p.1 * a b p.1) * (χ' p.2 * a' b p.2) = _
    ring
  have hident : (∑ b, g b p.1 * g' b p.2) - f p =
      χ p.1 * χ' p.2 * ((∑ b, a b p.1 * a' b p.2) - f p) := by
    rw [hsum, mul_sub, hcut]
  rw [hident, abs_mul]
  by_cases hp : p ∈ K
  · have hnonneg : 0 ≤ χ p.1 * χ' p.2 := mul_nonneg (hχ01 _).1 (hχ'01 _).1
    have hle : |χ p.1 * χ' p.2| ≤ 1 := by
      rw [abs_of_nonneg hnonneg]
      exact (mul_le_mul (hχ01 _).2 (hχ'01 _).2 (hχ'01 _).1 zero_le_one).trans (by norm_num)
    exact (mul_le_of_le_one_left (abs_nonneg _) hle).trans_lt (ha p hp)
  · have hzero : χ p.1 * χ' p.2 = 0 := by
      by_cases hx : p.1 ∈ tsupport (χ : Plane → ℝ)
      · have hy : p.2 ∉ tsupport (χ' : Plane → ℝ) := fun hy => hp ⟨hx, hy⟩
        rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    simpa only [hzero, abs_zero, zero_mul] using hε

/-- A sequence of compact tensor sums approximates a compact test uniformly inside one fixed support window. -/
theorem exists_compactTensorSum_sequence (f : C_c(Plane × Plane, ℝ)) :
    ∃ K : Set (Plane × Plane), IsCompact K ∧
      ∃ r : ℕ → ℕ, ∃ g g' : (n : ℕ) → Fin (r n) → C_c(Plane, ℝ),
        (∀ n, tsupport (((∑ b, compactTensorTest (g n b) (g' n b)) : C_c(Plane × Plane, ℝ)) : Plane × Plane → ℝ) ⊆ K) ∧
        ∀ n p, |((∑ b, compactTensorTest (g n b) (g' n b)) : C_c(Plane × Plane, ℝ)) p - f p| ≤
          1 / ((n : ℝ) + 1) := by
  classical
  obtain ⟨K, hK, hApprox⟩ := exists_compactTensorSum_uniform_approx f
  have hChoice (n : ℕ) := hApprox (1 / ((n : ℝ) + 1)) (by positivity)
  choose r g g' hsupport herr using hChoice
  refine ⟨K, hK, r, g, g', ?_, ?_⟩
  · intro n
    apply closure_minimal _ hK.isClosed
    intro p hp
    by_contra hout
    have hzero (b : Fin (r n)) : compactTensorTest (g n b) (g' n b) p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hmem => hout (hsupport n b hmem))
    exact hp (by simp only [CompactlySupportedContinuousMap.sum_apply, hzero, Finset.sum_const_zero])
  · intro n p
    simpa only [CompactlySupportedContinuousMap.sum_apply, compactTensorTest_apply] using (herr n p).le

end Critical2DKPZ.SHF.Tsai

end
