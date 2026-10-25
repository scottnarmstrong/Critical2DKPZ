/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonBlocks
public import Critical2DKPZ.SHF.Moments.TimeRounding
import Mathlib.Tactic

/-! # Scaled linear-time partition clocks -/

@[expose] public section

open Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- Integer division of a moving horizon has the expected fixed partition
fraction, including the zero entrance fraction. -/
theorem tendsto_quasiCriticalBlockClock_div (n : ℕ → ℕ) {T : ℝ}
    (hn : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 T))
    {M : ℕ} (hM : 0 < M) (i : ℕ) :
    Tendsto (fun N : ℕ => (quasiCriticalBlockClock (n N) M i : ℝ) / N)
      atTop (𝓝 (T * ((i : ℝ) / M))) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hrem : Tendsto (fun N : ℕ => ((n N * i % M : ℕ) : ℝ) / N)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N))
      (fun N => div_le_div_of_nonneg_right
        (by exact_mod_cast (Nat.mod_lt (n N * i) hM).le) (Nat.cast_nonneg N))
      (SHF.Moments.tendsto_const_div_nat (M : ℝ))
  have hlim := (hn.mul_const ((i : ℝ) / M)).sub (hrem.div_const (M : ℝ))
  simp only [zero_div, sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have heq : ((n N * i % M : ℕ) : ℝ) + (M : ℝ) * (n N * i / M : ℕ) = (n N : ℝ) * i := by
    exact_mod_cast Nat.mod_add_div (n N * i) M
  dsimp only [quasiCriticalBlockClock]
  field_simp
  nlinarith [heq]

/-- Every block indexed below M ends before the full horizon. -/
theorem quasiCriticalBlockClock_succ_le (n M : ℕ) {i : ℕ} (hi : i < M) :
    quasiCriticalBlockClock n M (i + 1) ≤ n := by
  calc
    _ ≤ quasiCriticalBlockClock n M M := monotone_quasiCriticalBlockClock n M (by omega)
    _ = n := by simp [quasiCriticalBlockClock, Nat.ne_of_gt (Nat.zero_lt_of_lt hi)]

end Critical2DKPZ.Extensions.GffTangent
