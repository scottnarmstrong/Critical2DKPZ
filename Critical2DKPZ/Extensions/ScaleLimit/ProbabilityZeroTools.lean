/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! # Domination and deterministic multipliers for convergence to zero in probability -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- An eventual pointwise absolute bound transfers convergence to zero in probability. -/
theorem tendstoInMeasure_zero_of_eventually_abs_le_mul {κ Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {l : Filter κ} {X Y : κ → Ω → ℝ}
    (hX : TendstoInMeasure P X l (fun _ => 0)) {M : ℝ} (hM : 0 < M)
    (hb : ∀ᶠ i in l, ∀ᵐ ω ∂P, |Y i ω| ≤ M * |X i ω|) :
    TendstoInMeasure P Y l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm] at hX ⊢
  intro ε hε
  have hlim := hX (ε / M) (div_pos hε hM)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hb] with i hi
  apply ENNReal.toReal_mono (measure_ne_top P _)
  apply measure_mono_ae
  filter_upwards [hi] with ω hω
  intro hY
  change ε ≤ ‖Y i ω - 0‖ at hY
  change ε / M ≤ ‖X i ω - 0‖
  simp only [sub_zero, Real.norm_eq_abs] at hY ⊢
  apply (div_le_iff₀ hM).mpr
  nlinarith

/-- A converging deterministic multiplier preserves convergence to zero in probability. -/
theorem tendstoInMeasure_mul_constSeq_zero {κ Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {l : Filter κ} {X : κ → Ω → ℝ}
    (hX : TendstoInMeasure P X l (fun _ => 0)) {c : κ → ℝ} {c₀ : ℝ}
    (hc : Tendsto c l (𝓝 c₀)) :
    TendstoInMeasure P (fun i ω => c i * X i ω) l (fun _ => 0) := by
  have hb : ∀ᶠ i in l, |c i| < |c₀| + 1 :=
    hc.abs.eventually (gt_mem_nhds (by linarith : |c₀| < |c₀| + 1))
  apply tendstoInMeasure_zero_of_eventually_abs_le_mul P hX (by positivity : 0 < |c₀| + 1)
  filter_upwards [hb] with i hi
  exact Filter.Eventually.of_forall fun ω => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hi.le (abs_nonneg _)

end Critical2DKPZ.Extensions.ScaleLimit
