/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.ScalarNormalization
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! # The exponentially growing geometric block clock

The floor error is negligible relative to the unfloored exponential argument.
Consequently the geometric widths have the same normalized logarithmic clock
as the original double-exponential widths.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The unfloored geometric block index grows to infinity. -/
theorem gridArgument_tendsto_atTop (ρ s : ℝ) (hρ : 1 < ρ) (hs : 0 < s) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => 2 * Real.exp ((L : ℝ) * s) / Real.log ρ)
      atTop atTop := by
  have hL : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hLs : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ) * s) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hL.eventually_ge_atTop (b / s)] with L hLb
    exact (div_le_iff₀ hs).mp hLb
  have hE : Tendsto (fun L : Set.Ioi (0 : ℝ) => Real.exp ((L : ℝ) * s))
      atTop atTop := by
    convert! Real.tendsto_exp_atTop.comp hLs using 1
  have hc : 0 < 2 / Real.log ρ := div_pos (by norm_num) (Real.log_pos hρ)
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hE.eventually_ge_atTop (b / (2 / Real.log ρ))] with L hLb
  calc
    b ≤ Real.exp ((L : ℝ) * s) * (2 / Real.log ρ) := (div_le_iff₀ hc).mp hLb
    _ = 2 * Real.exp ((L : ℝ) * s) / Real.log ρ := by ring

/-- The natural-valued geometric block index grows to infinity. -/
theorem nL_tendsto_atTop (ρ s : ℝ) (hρ : 1 < ρ) (hs : 0 < s) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => nL ρ L s) atTop atTop := by
  have hx := gridArgument_tendsto_atTop ρ s hρ hs
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hx.eventually_ge_atTop ((b : ℝ) + 1)] with L hLb
  have hf : 2 * Real.exp ((L : ℝ) * s) / Real.log ρ < (nL ρ L s : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hb : (b : ℝ) ≤ (nL ρ L s : ℝ) := by linarith
  exact_mod_cast hb

/-- Positive block indices are eventually available at every positive scale time. -/
theorem eventually_one_le_nL (ρ s : ℝ) (hρ : 1 < ρ) (hs : 0 < s) :
    ∀ᶠ L : Set.Ioi (0 : ℝ) in atTop, 1 ≤ nL ρ L s :=
  (nL_tendsto_atTop ρ s hρ hs).eventually_ge_atTop 1

/-- The floor error is negligible relative to the exponential grid argument. -/
theorem floor_grid_ratio_tendsto_one (ρ s : ℝ) (hρ : 1 < ρ) (hs : 0 < s) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      (nL ρ L s : ℝ) / (2 * Real.exp ((L : ℝ) * s) / Real.log ρ)) atTop (𝓝 1) := by
  let x : Set.Ioi (0 : ℝ) → ℝ := fun L => 2 * Real.exp ((L : ℝ) * s) / Real.log ρ
  have hx : Tendsto x atTop atTop := gridArgument_tendsto_atTop ρ s hρ hs
  have hxpos (L : Set.Ioi (0 : ℝ)) : 0 < x L :=
    div_pos (mul_pos (by norm_num) (Real.exp_pos _)) (Real.log_pos hρ)
  have hlo (L : Set.Ioi (0 : ℝ)) : 1 - 1 / x L ≤ (nL ρ L s : ℝ) / x L := by
    apply (le_div_iff₀ (hxpos L)).mpr
    have hf : x L < (nL ρ L s : ℝ) + 1 := Nat.lt_floor_add_one _
    have heq : (1 - 1 / x L) * x L = x L - 1 := by field_simp [(hxpos L).ne']
    rw [heq]
    linarith
  have hhi (L : Set.Ioi (0 : ℝ)) : (nL ρ L s : ℝ) / x L ≤ 1 :=
    (div_le_one₀ (hxpos L)).mpr (Nat.floor_le (hxpos L).le)
  have hinv : Tendsto (fun L => 1 / x L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hx
  have hlow : Tendsto (fun L => 1 - 1 / x L) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hinv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hlo hhi

/-- The geometric clock differs from `L*s` by a quantity tending to zero. -/
theorem loglog_grid (ρ s : ℝ) (hρ : 1 < ρ) (hs : 0 < s) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      Real.log ((nL ρ L s : ℝ) / 2 * Real.log ρ) - (L : ℝ) * s) atTop (𝓝 0) := by
  let x : Set.Ioi (0 : ℝ) → ℝ := fun L => 2 * Real.exp ((L : ℝ) * s) / Real.log ρ
  have hr := floor_grid_ratio_tendsto_one ρ s hρ hs
  have hl : Tendsto (fun L : Set.Ioi (0 : ℝ) => Real.log ((nL ρ L s : ℝ) / x L))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  apply hl.congr'
  filter_upwards [eventually_one_le_nL ρ s hρ hs] with L hN
  have hNne : (nL ρ L s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
  have hρne : Real.log ρ ≠ 0 := (Real.log_pos hρ).ne'
  have he : Real.exp ((L : ℝ) * s) ≠ 0 := (Real.exp_pos _).ne'
  have heq : (nL ρ L s : ℝ) / x L =
      ((nL ρ L s : ℝ) / 2 * Real.log ρ) / Real.exp ((L : ℝ) * s) := by
    dsimp [x]
    field_simp [hρne, he]
  rw [heq, Real.log_div (mul_ne_zero (div_ne_zero hNne (by norm_num)) hρne) he,
    Real.log_exp]

/-- The logarithm of the geometric block index has limiting linear clock `s`. -/
theorem log_nL_div_L_tendsto (ρ s : ℝ) (hρ : 1 < ρ) (hs : 0 < s) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => Real.log (nL ρ L s : ℝ) / (L : ℝ))
      atTop (𝓝 s) := by
  let D : Set.Ioi (0 : ℝ) → ℝ := fun L =>
    Real.log ((nL ρ L s : ℝ) / 2 * Real.log ρ) - (L : ℝ) * s
  let c : ℝ := Real.log (Real.log ρ / 2)
  have hD : Tendsto D atTop (𝓝 0) := loglog_grid ρ s hρ hs
  have hL : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hDC : Tendsto (fun L => D L - c) atTop (𝓝 (-c)) := by
    simpa only [zero_sub] using hD.sub tendsto_const_nhds
  have he : Tendsto (fun L => (D L - c) / (L : ℝ)) atTop (𝓝 0) := hDC.div_atTop hL
  have hh : Tendsto (fun L => s + (D L - c) / (L : ℝ)) atTop (𝓝 s) := by
    simpa only [add_zero] using tendsto_const_nhds.add he
  apply hh.congr'
  filter_upwards [eventually_one_le_nL ρ s hρ hs] with L hN
  have hNne : (nL ρ L s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
  have harg : Real.log ((nL ρ L s : ℝ) / 2 * Real.log ρ) = Real.log (nL ρ L s : ℝ) + c := by
    rw [show (nL ρ L s : ℝ) / 2 * Real.log ρ = (nL ρ L s : ℝ) * (Real.log ρ / 2) by ring,
      Real.log_mul hNne (div_ne_zero (Real.log_pos hρ).ne' (by norm_num))]
  change s + (Real.log ((nL ρ L s : ℝ) / 2 * Real.log ρ) - (L : ℝ) * s - c) / (L : ℝ) = _
  rw [harg]
  field_simp [L.property.ne']; ring

/-- The normalized logarithmic clock of the actual geometric widths is `s`. -/
theorem normalized_loglog_geometric_clock (ρ s : ℝ) (hρ : 1 < ρ) (hs : 0 < s) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)⁻¹ *
      Real.log (Real.log (Real.sqrt (tau ρ (nL ρ L s)))⁻¹)) atTop (𝓝 s) := by
  have hL : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hc : Tendsto (fun L : Set.Ioi (0 : ℝ) => Real.log (Real.log ρ / 2) / (L : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hL
  have hh : Tendsto (fun L : Set.Ioi (0 : ℝ) => Real.log (nL ρ L s : ℝ) / (L : ℝ) +
      Real.log (Real.log ρ / 2) / (L : ℝ)) atTop (𝓝 s) := by
    simpa only [add_zero] using (log_nL_div_L_tendsto ρ s hρ hs).add hc
  apply hh.congr'
  filter_upwards [eventually_one_le_nL ρ s hρ hs] with L hN
  rw [loglog_inv_sqrt_tau hρ (lt_of_lt_of_le Nat.zero_lt_one hN)]
  ring

/-- The geometric widths shrink to zero at every positive scale time. -/
theorem geometric_width_tendsto_zero (ρ s : ℝ) (hρ : 1 < ρ) (hs : 0 < s) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => Real.sqrt (tau ρ (nL ρ L s))) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp
      ((tendsto_tau_zero hρ).comp (nL_tendsto_atTop ρ s hρ hs))

/-- The geometric widths are eventually in the classical logarithmic-clock domain. -/
theorem eventually_geometric_width_lt_one (ρ s : ℝ) (hρ : 1 < ρ) (hs : 0 < s) :
    ∀ᶠ L : Set.Ioi (0 : ℝ) in atTop, Real.sqrt (tau ρ (nL ρ L s)) < 1 := by
  filter_upwards [eventually_one_le_nL ρ s hρ hs] with L hN
  have hsq := Real.sq_sqrt (tau_pos hρ (nL ρ L s)).le
  have hnonneg := Real.sqrt_nonneg (tau ρ (nL ρ L s))
  have hlt := tau_lt_one hρ (lt_of_lt_of_le Nat.zero_lt_one hN)
  nlinarith

/-- At a fixed positive `L`, the grid index is monotone in the scale time. -/
theorem monotone_nL_time (ρ L : ℝ) (hρ : 1 < ρ) (hL : 0 < L) : Monotone (nL ρ L) := by
  intro s s' hss
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ (Real.log_pos hρ).le
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hss hL.le)

end Critical2DKPZ.Extensions.ScaleLimit
