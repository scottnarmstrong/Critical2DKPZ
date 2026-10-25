/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceWalkMoments
public import Critical2DKPZ.SHF.Moments.GapOverlap
import Mathlib.Tactic

/-! # Logarithmic short-strip control for coincident moving starts -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

/-- The return mass through time `K` is the zero-gap overlap plus its time-zero atom. -/
theorem sum_returnWeight_Icc_eq_one_add_gapOverlap (K : ℕ) :
    ∑ r ∈ Finset.Icc 0 K, Renewal.returnWeight r =
      1 + gapOverlap (0 : Site) K := by
  have hset : Finset.Icc 0 K = insert 0 (Finset.Icc 1 K) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hzero : (0 : ℕ) ∉ Finset.Icc 1 K := by simp
  rw [hset, Finset.sum_insert hzero]
  simp [gapOverlap, Renewal.returnWeight, srwKernel_zero]

private theorem log_nat_le_log_nat_add_two (K : ℕ) :
    Real.log (K : ℝ) ≤ Real.log ((K : ℝ) + 2) := by
  by_cases hK : K = 0
  · subst K
    simp only [Nat.cast_zero, zero_add, Real.log_zero]
    exact Real.log_nonneg (by norm_num)
  · have hKpos : 0 < (K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hK
    apply Real.log_le_log hKpos
    linarith

/-- The cumulative central return mass grows at most logarithmically, including the
time-zero atom. -/
theorem exists_returnWeight_Icc_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ,
      ∑ r ∈ Finset.Icc 0 K, Renewal.returnWeight r ≤
        C * Real.log ((K : ℝ) + 2) := by
  obtain ⟨Cerr, hErr⟩ := gapOverlap_log_bound (0 : Site) (by simp)
  let Cerr' := max Cerr 0
  let C : ℝ := 1 / Real.pi + (Cerr' + 1) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCerr : 0 ≤ Cerr' := le_max_right _ _
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, fun K => ?_⟩
  rw [sum_returnWeight_Icc_eq_one_add_gapOverlap]
  have hgap : gapOverlap (0 : Site) K ≤
      (1 / Real.pi) * Real.log K + Cerr' := by
    have h := hErr K
    have h' : gapOverlap (0 : Site) K -
        (1 / Real.pi) * Real.log K ≤ Cerr' := by
      exact (le_abs_self _).trans (h.trans (le_max_left _ _))
    linarith
  have hlogK : Real.log (K : ℝ) ≤ Real.log ((K : ℝ) + 2) :=
    log_nat_le_log_nat_add_two K
  have hloglower : Real.log 2 ≤ Real.log ((K : ℝ) + 2) := by
    apply Real.log_le_log (by norm_num)
    have hKnonneg : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
    linarith
  have hconstant : Cerr' + 1 ≤
      ((Cerr' + 1) / Real.log 2) * Real.log ((K : ℝ) + 2) := by
    calc
      Cerr' + 1 = ((Cerr' + 1) / Real.log 2) * Real.log 2 := by
        field_simp [hlog2.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hloglower (by positivity)
  calc
    1 + gapOverlap (0 : Site) K ≤
        1 + (1 / Real.pi) * Real.log K + Cerr' := by linarith
    _ ≤ (1 / Real.pi) * Real.log ((K : ℝ) + 2) +
        ((Cerr' + 1) / Real.log 2) * Real.log ((K : ℝ) + 2) := by
      have hpi : 0 ≤ (1 / Real.pi : ℝ) := by positivity
      have hterm := mul_le_mul_of_nonneg_left hlogK hpi
      linarith [hterm, hconstant]
    _ = C * Real.log ((K : ℝ) + 2) := by
      dsimp [C]
      ring

/-- The centered short-strip estimate with its moving-center contribution bounded
by `log (N + 2)`. -/
theorem exists_collisionEntrance_abs_le_linear_center_log :
    ∃ Creturn Ccenter Cmoment : ℝ,
      0 < Creturn ∧ 0 < Ccenter ∧ 0 < Cmoment ∧
      ∀ (N K : ℕ), 0 < N → K ≤ N →
      ∀ (a : Site) (c : Plane) (L : ℝ), 0 ≤ L →
      ∀ (F : ℝ × Plane → ℝ),
      (∀ u x, 0 ≤ u → |F (u, x)| ≤ L * (u + ‖x - c‖)) →
      |collisionEntrance N 0 K a a F| ≤
        L * (Creturn * (((K : ℝ) + 1) / N) +
          Ccenter * ‖latticeRepresentative N a - c‖ *
            Real.log ((N : ℝ) + 2) +
          2 * Cmoment * (Real.sqrt ((N : ℝ) / 2))⁻¹ *
            Real.sqrt ((K : ℝ) + 1)) := by
  obtain ⟨Creturn, Cmoment, hCreturn, hCmoment, hstrip⟩ :=
    exists_collisionEntrance_abs_le_linear_center
  obtain ⟨Ccenter, hCcenter, hreturnSum⟩ := exists_returnWeight_Icc_le_log
  refine ⟨Creturn, Ccenter, Cmoment, hCreturn, hCcenter, hCmoment, ?_⟩
  intro N K hN hKN a c L hL F hF
  have hKlog : Real.log ((K : ℝ) + 2) ≤ Real.log ((N : ℝ) + 2) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hKN 2
  have hsum := hstrip N K hN a c L hL F hF
  have hreturn := hreturnSum K
  have hcenter :
      ‖latticeRepresentative N a - c‖ *
          ∑ r ∈ Finset.Icc 0 K, Renewal.returnWeight r ≤
        Ccenter * ‖latticeRepresentative N a - c‖ *
          Real.log ((N : ℝ) + 2) := by
    calc
      _ ≤ ‖latticeRepresentative N a - c‖ *
          (Ccenter * Real.log ((K : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hreturn (norm_nonneg _)
      _ ≤ _ := by
        calc
          ‖latticeRepresentative N a - c‖ *
              (Ccenter * Real.log ((K : ℝ) + 2)) =
            (‖latticeRepresentative N a - c‖ * Ccenter) *
              Real.log ((K : ℝ) + 2) := by ring
          _ ≤ (‖latticeRepresentative N a - c‖ * Ccenter) *
              Real.log ((N : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left hKlog (by positivity)
          _ = Ccenter * ‖latticeRepresentative N a - c‖ *
              Real.log ((N : ℝ) + 2) := by ring
  calc
    _ ≤ L * (Creturn * (((K : ℝ) + 1) / N) +
        ‖latticeRepresentative N a - c‖ *
          ∑ r ∈ Finset.Icc 0 K, Renewal.returnWeight r +
        2 * Cmoment * (Real.sqrt ((N : ℝ) / 2))⁻¹ *
          Real.sqrt ((K : ℝ) + 1)) := hsum
    _ ≤ L * (Creturn * (((K : ℝ) + 1) / N) +
        Ccenter * ‖latticeRepresentative N a - c‖ *
          Real.log ((N : ℝ) + 2) +
        2 * Cmoment * (Real.sqrt ((N : ℝ) / 2))⁻¹ *
          Real.sqrt ((K : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hL
      nlinarith [hcenter]

end Critical2DKPZ.SHF.Moments

end
