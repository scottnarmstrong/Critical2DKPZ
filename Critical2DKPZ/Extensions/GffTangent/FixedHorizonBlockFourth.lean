/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonSignedFourth
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonBlockClocks
import Mathlib.Tactic

/-! # Vanishing total fourth moments as the time partition is refined -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- Every block length has the same macroscopic limit T/M, with no
rounding convention imposed on the full moving horizon. -/
theorem tendsto_quasiCriticalBlockLength_div (n : ℕ → ℕ) {T : ℝ}
    (hn : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 T))
    {M : ℕ} (hM : 0 < M) (i : ℕ) :
    Tendsto (fun N : ℕ =>
      ((quasiCriticalBlockClock (n N) M (i + 1) - quasiCriticalBlockClock (n N) M i : ℕ) : ℝ) / N)
      atTop (𝓝 (T / M)) := by
  have h := (tendsto_quasiCriticalBlockClock_div n hn hM (i + 1)).sub
    (tendsto_quasiCriticalBlockClock_div n hn hM i)
  have he : T * ((i + 1 : ℕ) : ℝ) / M - T * (i : ℝ) / M = T / M := by push_cast; ring
  simp only [← mul_div_assoc, he] at h
  apply h.congr'
  filter_upwards [] with N
  rw [Nat.cast_sub (monotone_quasiCriticalBlockClock (n N) M (Nat.le_succ i)), sub_div]

/-- Actual cell-weighted fluctuations on the ith time block. -/
def cellBlockFluctuation (β l : ℝ) (N n M i : ℕ) (f : TestFn) : Disorder → ℝ :=
  latticeWindowFluctuation β (Real.sqrt l)
    (quasiCriticalBlockClock n M i) (quasiCriticalBlockClock n M (i + 1))
    (fixedHorizonCellSites N f) (signedCellProfile N f)

/-- For every fixed partition, the total actual fourth moment is bounded
by a constant times T²/M plus an arbitrary vanishing-regime error. -/
theorem eventually_sum_fourth_cellBlockFluctuation_le (f : TestFn)
    {Cf : ℝ} (hCf : 0 ≤ Cf) (hfC : ∀ x : Plane, |f x| ≤ Cf)
    (l β : ℕ → ℝ) (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    (n : ℕ → ℕ) {T : ℝ} (hT : 0 < T)
    (hn : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 T))
    {M : ℕ} (hM : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ i : Fin M, ∫ ω, cellBlockFluctuation (β N) (l N) N (n N) M i f ω ^ 4 ∂disorderLaw) ≤
      (16 * ((2 : ℝ) ^ 32 * Real.pi ^ 2 * (4 * Cf * ∫ x : Plane, |f x|) ^ 2)) * T ^ 2 / M + ε := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let C := 16 * ((2 : ℝ) ^ 32 * Real.pi ^ 2 * (4 * Cf * ∫ x : Plane, |f x|) ^ 2)
  have heach : ∀ i : Fin M, ∀ᶠ N : ℕ in atTop,
      (∫ ω, cellBlockFluctuation (β N) (l N) N (n N) M i f ω ^ 4 ∂disorderLaw) ≤
        C * (T / M) ^ 2 + ε / M := by
    intro i
    have h := eventually_fourth_signed_cell_profile_le f hCf hfC l β hl hratio hβ hσ
      (div_pos hT hMr) (tendsto_quasiCriticalBlockLength_div n hn hM i)
      (ε := ε / M) (div_pos hε hMr)
    filter_upwards [h] with N hN
    exact (integral_fourth_latticeWindowFluctuation_le (β N) (Real.sqrt (l N))
      (quasiCriticalBlockClock (n N) M i) (quasiCriticalBlockClock (n N) M (i + 1))
      (fixedHorizonCellSites N f) (signedCellProfile N f)).trans hN
  filter_upwards [Filter.eventually_all.mpr heach] with N hN
  apply (Finset.sum_le_sum (fun i _ => hN i)).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (M : ℝ) * (C * (T / M) ^ 2 + ε / M) = C * T ^ 2 / M + ε
  field_simp

end Critical2DKPZ.Extensions.GffTangent
