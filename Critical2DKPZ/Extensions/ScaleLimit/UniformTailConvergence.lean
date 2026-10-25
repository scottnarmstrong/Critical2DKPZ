/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! # Uniform exponential tails imply vanishing normalized errors

The lower cutoff and the tail level can be fixed successively before the
normalization tends to infinity. Thus no quantitative choice of a growing
cutoff is needed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A uniform block-type tail estimate gives convergence in probability after
any diverging normalization and along any diverging block index. -/
theorem tendstoInMeasure_div_of_uniform_tail {Ω κ : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (ℓ₀ : ℕ)
    (htail : ∀ n ℓ : ℕ, ℓ₀ ≤ ℓ → ℓ < n → ∀ u : ℝ, 0 ≤ u →
      P {ω | (ℓ : ℝ) * Real.log 2 + Real.log 2 + u < |X n ω|} ≤
        ENNReal.ofReal (C / ℓ + (1 + C * ℓ) * Real.exp (-u)))
    (l : Filter κ) (n : κ → ℕ) (a : κ → ℝ)
    (hn : Tendsto n l atTop) (ha : Tendsto a l atTop) :
    TendstoInMeasure P (fun i ω => X (n i) ω / a i) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  rw [Metric.tendsto_nhds]
  intro η hη
  have hcut : Tendsto (fun ℓ : ℕ => C / (ℓ : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨ℓ, hℓ₀, hℓ1, hcutℓ⟩ :=
    ((eventually_ge_atTop ℓ₀).and ((eventually_ge_atTop 1).and
      (hcut.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < η / 2))))).exists
  have hexp : Tendsto (fun u : ℝ => (1 + C * ℓ) * Real.exp (-u)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero
  obtain ⟨u, hu, hsmall⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hexp.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < η / 2)))).exists
  let K : ℝ := (ℓ : ℝ) * Real.log 2 + Real.log 2 + u
  filter_upwards [hn.eventually_gt_atTop ℓ, ha.eventually_gt_atTop (max 0 (K / ε))] with i hni hai
  have hapos : 0 < a i := (le_max_left _ _).trans_lt hai
  have hKa : K < ε * a i := by
    have h := (le_max_right _ _).trans_lt hai
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp h
  have hsubset : {ω | ε ≤ ‖X (n i) ω / a i - 0‖} ⊆ {ω | K < |X (n i) ω|} := by
    intro ω hω
    change ε ≤ ‖X (n i) ω / a i - 0‖ at hω
    have hprod : ε * a i ≤ |X (n i) ω| := by
      apply (le_div_iff₀ hapos).mp
      simpa only [sub_zero, Real.norm_eq_abs, abs_div, abs_of_pos hapos] using hω
    exact hKa.trans_le hprod
  have hbound : P.real {ω | K < |X (n i) ω|} ≤ C / ℓ + (1 + C * ℓ) * Real.exp (-u) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (htail (n i) ℓ hℓ₀ hni u hu)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  exact ((measureReal_mono hsubset).trans hbound).trans_lt (by linarith)

end Critical2DKPZ.Extensions.ScaleLimit
