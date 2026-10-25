/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionEntrance
public import Critical2DKPZ.Polymer.Profiles
import Mathlib.Tactic

/-! # Initial-location averages of collision entrances -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open Polymer

private theorem sum_srwKernel_subset_le_one (n : ℕ) (a : Site) (B : Finset Site) :
    ∑ b ∈ B, srwKernel n (b - a) ≤ 1 := by
  classical
  let E := endpoints a n
  have heq : ∑ b ∈ B.filter (fun b => b ∈ E), srwKernel n (b - a) =
      ∑ b ∈ B, srwKernel n (b - a) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hnot
    apply srwKernel_eq_zero_of_not_mem n a b
    intro he
    exact hnot (Finset.mem_filter.mpr ⟨hb, he⟩)
  rw [← heq, ← sum_srwKernel_endpoints n a]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun b hb => (Finset.mem_filter.mp hb).2) (fun b _hb _hnot => kernel_nonneg n (b - a))

/-- Averaging over a finite set of second starting sites removes the singular
collision-return mass. No separation of the initial sites is required. -/
theorem sum_collisionEntrance_abs_le_card
    (N lo hi : ℕ) (a : Site) (B : Finset Site) (M : ℝ) (hM : 0 ≤ M)
    (F : Site → ℝ × Plane → ℝ) (hF : ∀ b ∈ B, ∀ p, |F b p| ≤ M) :
    ∑ b ∈ B, |collisionEntrance N lo hi a b (F b)| ≤
      M * (Finset.Icc lo hi).card := by
  calc
    _ ≤ ∑ b ∈ B, M * ∑ r ∈ Finset.Icc lo hi, srwKernel (2 * r) (b - a) :=
      Finset.sum_le_sum fun b hb => collisionEntrance_abs_le N lo hi a b (hF b hb)
    _ = M * ∑ r ∈ Finset.Icc lo hi, ∑ b ∈ B, srwKernel (2 * r) (b - a) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ M * ∑ _r ∈ Finset.Icc lo hi, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun r _hr => sum_srwKernel_subset_le_one (2 * r) a B) hM
    _ = M * (Finset.Icc lo hi).card := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The two-start average is bounded by one support cardinality times the
clock cardinality. In diffusive normalization this gives a small initial-time
strip uniformly, including the near-diagonal starting configurations. -/
theorem sum_sum_collisionEntrance_abs_le_cards
    (N lo hi : ℕ) (A B : Finset Site) (M : ℝ) (hM : 0 ≤ M)
    (F : Site → Site → ℝ × Plane → ℝ)
    (hF : ∀ a ∈ A, ∀ b ∈ B, ∀ p, |F a b p| ≤ M) :
    ∑ a ∈ A, ∑ b ∈ B, |collisionEntrance N lo hi a b (F a b)| ≤
      (A.card : ℝ) * M * (Finset.Icc lo hi).card := by
  calc
    _ ≤ ∑ _a ∈ A, M * (Finset.Icc lo hi).card :=
      Finset.sum_le_sum fun a ha => sum_collisionEntrance_abs_le_card N lo hi a B M hM
        (F a) (hF a ha)
    _ = (A.card : ℝ) * M * (Finset.Icc lo hi).card := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Finite two-site configuration sums as rectangular sums. -/
theorem sum_initialConfigurations_eq_double (S : Fin 2 → Finset Site)
    (f : (Fin 2 → Site) → ℝ) :
    (∑ x ∈ Fintype.piFinset S, f x) = ∑ a ∈ S 0, ∑ b ∈ S 1, f ![a, b] := by
  classical
  rw [← Finset.sum_product (S 0) (S 1) (fun p : Site × Site => f ![p.1, p.2])]
  apply Finset.sum_bij (fun x _hx => (x 0, x 1))
  · intro x hx
    exact Finset.mem_product.mpr ⟨(Fintype.mem_piFinset.mp hx) 0,
      (Fintype.mem_piFinset.mp hx) 1⟩
  · intro x _hx y _hy hxy
    funext i
    fin_cases i
    · exact congrArg Prod.fst hxy
    · exact congrArg Prod.snd hxy
  · intro p hp
    refine ⟨![p.1, p.2], ?_, rfl⟩
    rw [Fintype.mem_piFinset]
    intro i
    fin_cases i
    · exact (Finset.mem_product.mp hp).1
    · exact (Finset.mem_product.mp hp).2
  · intro x _hx
    congr 1
    funext i
    fin_cases i <;> rfl

/-- The initial-average bound in the configuration carrier used by the exact
word expansion. It includes coincident starting sites. -/
theorem sum_piFinset_collisionEntrance_abs_le
    (N lo hi : ℕ) (S : Fin 2 → Finset Site) (M : ℝ) (hM : 0 ≤ M)
    (F : (Fin 2 → Site) → ℝ × Plane → ℝ)
    (hF : ∀ x ∈ Fintype.piFinset S, ∀ p, |F x p| ≤ M) :
    ∑ x ∈ Fintype.piFinset S, |collisionEntrance N lo hi (x 0) (x 1) (F x)| ≤
      ((S 0).card : ℝ) * M * (Finset.Icc lo hi).card := by
  classical
  rw [sum_initialConfigurations_eq_double]
  apply sum_sum_collisionEntrance_abs_le_cards N lo hi (S 0) (S 1) M hM
    (fun a b => F ![a, b])
  intro a ha b hb p
  apply hF ![a, b] _ p
  rw [Fintype.mem_piFinset]
  intro i
  fin_cases i
  · exact ha
  · exact hb

/-- Diffusive normalization of the configuration-average estimate. A support
of size at most `C N` leaves only the clock-window ratio `card/N`. -/
theorem scaled_sum_piFinset_collisionEntrance_abs_le
    {N : ℕ} (hN : 0 < N) (lo hi : ℕ) (S : Fin 2 → Finset Site)
    (C M : ℝ) (hM : 0 ≤ M) (hS : ((S 0).card : ℝ) ≤ C * N)
    (F : (Fin 2 → Site) → ℝ × Plane → ℝ)
    (hF : ∀ x ∈ Fintype.piFinset S, ∀ p, |F x p| ≤ M) :
    ((N : ℝ)^2)⁻¹ * ∑ x ∈ Fintype.piFinset S,
      |collisionEntrance N lo hi (x 0) (x 1) (F x)| ≤
        C * M * (((Finset.Icc lo hi).card : ℝ) / N) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hb := sum_piFinset_collisionEntrance_abs_le N lo hi S M hM F hF
  calc
    _ ≤ ((N : ℝ)^2)⁻¹ * (((S 0).card : ℝ) * M * (Finset.Icc lo hi).card) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ ((N : ℝ)^2)⁻¹ * ((C * N) * M * (Finset.Icc lo hi).card) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS hM) (Nat.cast_nonneg _)
    _ = C * M * (((Finset.Icc lo hi).card : ℝ) / N) := by field_simp

end Critical2DKPZ.SHF.Moments
