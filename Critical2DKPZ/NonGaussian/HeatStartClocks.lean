/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TimeRounding
import Mathlib.Tactic

/-! # Clock limits for simple random walk initial profiles -/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.NonGaussian

/-- The smoothed-mass horizon corresponding to the heat-start lattice profile
has macroscopic length `δ + T - s`. -/
theorem tendsto_heatStartWalkHorizon_div {s T δ : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (hδ : 0 ≤ δ) :
    Tendsto (fun N : ℕ =>
      ((evenCeil (N * δ) + (evenCeil (N * T) - evenCeil (N * s)) : ℕ) : ℝ) / N)
      atTop (𝓝 (δ + (T - s))) := by
  simp_rw [Nat.cast_add, add_div]
  exact (SHF.Moments.tendsto_evenCeil_div δ hδ).add
    (SHF.Moments.tendsto_evenCeil_gap_div hs hsT)

/-- The discrete horizon-to-smoothing ratio tends to its continuum ratio;
the `max m 1` cutoff is eventually inactive at every fixed positive width. -/
theorem tendsto_heatStartWalkHorizon_ratio {s T δ : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ =>
      ((evenCeil (N * δ) + (evenCeil (N * T) - evenCeil (N * s)) : ℕ) : ℝ) /
        (max (evenCeil (N * δ)) 1 : ℕ)) atTop (𝓝 ((δ + (T - s)) / δ)) := by
  have h := (tendsto_heatStartWalkHorizon_div hs hsT hδ.le).div
    (SHF.Moments.tendsto_evenCeil_div δ hδ.le) hδ.ne'
  apply h.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1 / δ),
    eventually_ge_atTop 1] with N hNδ hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hm : 1 ≤ evenCeil (N * δ) := by
    have hlow := le_evenCeil (N * δ)
    have hone : (1 : ℝ) ≤ (evenCeil (N * δ) : ℝ) := by
      have hprod := (div_le_iff₀ hδ).mp hNδ
      linarith only [hlow, hprod]
    exact_mod_cast hone
  rw [max_eq_left hm]
  dsimp only [Pi.div_apply]
  field_simp [hNr.ne']

end Critical2DKPZ.NonGaussian

end
