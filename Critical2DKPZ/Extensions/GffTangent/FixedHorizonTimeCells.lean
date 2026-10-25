/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Critical2DKPZ.SHF.Moments.TerminalWordLimitClocks
import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Exact one-clock integration of the CCR window variance sum -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- The first-collision clock samples the right endpoint of its time cell. -/
def fixedHorizonClock (N : ℕ) (t : ℝ) : ℕ := ⌊(N : ℝ) * t⌋₊ + 1

/-- The right endpoint of the cell has the prescribed positive scaled time. -/
theorem tendsto_fixedHorizonClock_div {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => (fixedHorizonClock N t : ℝ) / N) atTop (𝓝 t) := by
  simpa only [fixedHorizonClock, SHF.Moments.wordEntranceClock] using
    SHF.Moments.tendsto_wordEntranceClock_scaled ht

private theorem fixedHorizonTimeCell_mem {N : ℕ} (hN : 0 < N) (a : ℕ) (t : ℝ) :
    t ∈ Ico ((a : ℝ) / N) (((a : ℝ) + 1) / N) ↔
      0 ≤ t ∧ ⌊(N : ℝ) * t⌋₊ = a := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro ht
    have ht0 : 0 ≤ t := (div_nonneg (Nat.cast_nonneg _) hNr.le).trans ht.1
    refine ⟨ht0, (Nat.floor_eq_iff (mul_nonneg hNr.le ht0)).mpr ?_⟩
    exact ⟨by nlinarith [(div_le_iff₀ hNr).mp ht.1],
      by nlinarith [(lt_div_iff₀ hNr).mp ht.2]⟩
  · rintro ⟨ht0, hf⟩
    have hh := (Nat.floor_eq_iff (mul_nonneg hNr.le ht0)).mp hf
    exact ⟨(div_le_iff₀ hNr).mpr (by nlinarith [hh.1]),
      (lt_div_iff₀ hNr).mpr (by nlinarith [hh.2])⟩

/-- An exact finite-cell representation, including arbitrary lower cutoff. -/
theorem fixedHorizonTimeStep_eq_sum {N : ℕ} (hN : 0 < N) (a b : ℕ)
    (F : ℕ → ℝ) (t : ℝ) :
    (if 0 ≤ t ∧ a < fixedHorizonClock N t ∧ fixedHorizonClock N t ≤ b
      then F (fixedHorizonClock N t) else 0) =
      ∑ r ∈ Finset.Icc (a + 1) b,
        (Ico (((r : ℝ) - 1) / N) ((r : ℝ) / N)).indicator (fun _ => F r) t := by
  classical
  have hcell (r : ℕ) (hr : 1 ≤ r) :
      t ∈ Ico (((r : ℝ) - 1) / N) ((r : ℝ) / N) ↔
        0 ≤ t ∧ fixedHorizonClock N t = r := by
    have hc := fixedHorizonTimeCell_mem hN (r - 1) t
    have hc1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub hr, Nat.cast_one]
    rw [hc1] at hc
    simp only [sub_add_cancel] at hc
    simp only [fixedHorizonClock]
    constructor
    · intro hm
      obtain ⟨h0, heq⟩ := hc.mp hm
      exact ⟨h0, by omega⟩
    · rintro ⟨h0, heq⟩
      exact hc.mpr ⟨h0, by omega⟩
  by_cases ht : 0 ≤ t ∧ a < fixedHorizonClock N t ∧ fixedHorizonClock N t ≤ b
  · rw [ite_eq_left ht]
    have hr : fixedHorizonClock N t ∈ Finset.Icc (a + 1) b := by
      simp only [Finset.mem_Icc]; omega
    rw [Finset.sum_eq_single_of_mem _ hr]
    · rw [indicator_of_mem ((hcell _ (by omega)).mpr ⟨ht.1, rfl⟩)]
    · intro r hr hne
      apply indicator_of_notMem
      intro hm
      have hh := (hcell r (by have := (Finset.mem_Icc.mp hr).1; omega)).mp hm
      exact hne hh.2.symm
  · rw [ite_eq_right ht]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    apply indicator_of_notMem
    intro hm
    obtain ⟨ht0, heq⟩ := (hcell r (by have := (Finset.mem_Icc.mp hr).1; omega)).mp hm
    apply ht
    have hr' := Finset.mem_Icc.mp hr
    exact ⟨ht0, by omega, by omega⟩

/-- Integrating the collision-clock staircase is exactly the normalized finite
first-collision sum. No limiting assertion is used here. -/
theorem integrable_integral_fixedHorizonTimeStep {N : ℕ} (hN : 0 < N)
    (a b : ℕ) (F : ℕ → ℝ) :
    Integrable (fun t : ℝ =>
      if 0 ≤ t ∧ a < fixedHorizonClock N t ∧ fixedHorizonClock N t ≤ b
      then F (fixedHorizonClock N t) else 0) ∧
    (∫ t : ℝ, if 0 ≤ t ∧ a < fixedHorizonClock N t ∧ fixedHorizonClock N t ≤ b
      then F (fixedHorizonClock N t) else 0) =
      (∑ r ∈ Finset.Icc (a + 1) b, F r) / (N : ℝ) := by
  have hcell (r : ℕ) :
      Integrable ((Ico (((r : ℝ) - 1) / N) ((r : ℝ) / N)).indicator (fun _ => F r)) ∧
      (∫ t : ℝ, (Ico (((r : ℝ) - 1) / N) ((r : ℝ) / N)).indicator (fun _ => F r) t) =
        F r / N := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hv : (r : ℝ) / N - ((r : ℝ) - 1) / N = (N : ℝ)⁻¹ := by ring
    refine ⟨(integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_const ?_), ?_⟩
    · rw [Real.volume_Ico, hv]; finiteness
    · rw [integral_indicator_const _ measurableSet_Ico, measureReal_def, Real.volume_Ico, hv,
        ENNReal.toReal_ofReal (by positivity)]
      simp only [smul_eq_mul]
      ring
  simp_rw [fixedHorizonTimeStep_eq_sum hN]
  refine ⟨integrable_finsetSum _ (fun r _ => (hcell r).1), ?_⟩
  rw [integral_finsetSum _ (fun r _ => (hcell r).1)]
  simp_rw [(hcell _).2]
  rw [Finset.sum_div]

end Critical2DKPZ.Extensions.GffTangent
