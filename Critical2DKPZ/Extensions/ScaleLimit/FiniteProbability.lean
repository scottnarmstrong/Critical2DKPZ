/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! # Finite-vector and first-moment probability convergence tools -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Coordinatewise convergence in probability gives finite-vector convergence
for an arbitrary index filter. -/
theorem tendstoInMeasure_finite_pi {κ Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) (l : Filter κ) (f : κ → Ω → I → ℝ) (g : Ω → I → ℝ)
    (hconv : ∀ i, TendstoInMeasure P (fun n ω => f n ω i) l (fun ω => g ω i)) :
    TendstoInMeasure P f l g := by
  classical
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hsum : Tendsto (fun n => ∑ i, P {ω | ε ≤ dist (f n ω i) (g ω i)}) l (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => (tendstoInMeasure_iff_dist.1 (hconv i)) ε hε)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
  intro n
  have hset : {ω | ε ≤ dist (f n ω) (g ω)} ⊆ ⋃ i, {ω | ε ≤ dist (f n ω i) (g ω i)} := by
    intro ω hω
    change ε ≤ dist (f n ω) (g ω) at hω
    by_contra hout
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hout
    exact (not_lt_of_ge hω) ((dist_pi_lt_iff hε).2 hout)
  exact (measure_mono hset).trans (measure_iUnion_fintype_le P _)

/-- A uniform eventual first absolute moment makes any diverging normalization
negligible in probability. Initial values need no regularity. -/
theorem tendstoInMeasure_div_of_integral_abs_bound {κ Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (l : Filter κ) (X : κ → Ω → ℝ)
    (a : κ → ℝ) (ha : Tendsto a l atTop) (C : ℝ)
    (hb : ∀ᶠ i in l, Integrable (X i) P ∧ (∫ ω, |X i ω| ∂P) ≤ C) :
    TendstoInMeasure P (fun i ω => X i ω / a i) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hlim : Tendsto (fun i => C / a i / ε) l (𝓝 0) := by
    simpa only [zero_div] using (tendsto_const_nhds.div_atTop ha).div_const ε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hb, ha.eventually_gt_atTop 0] with i hi hai
  have hs : {ω | ε ≤ ‖X i ω / a i - 0‖} ⊆ {ω | ε * a i ≤ |X i ω|} := by
    intro ω hω
    change ε ≤ ‖X i ω / a i - 0‖ at hω
    apply (le_div_iff₀ hai).mp
    simpa only [sub_zero, Real.norm_eq_abs, abs_div, abs_of_pos hai] using hω
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => abs_nonneg (X i ω))) hi.1.abs (ε * a i)
  apply (measureReal_mono hs).trans
  have hpos : 0 < ε * a i := mul_pos hε hai
  have hdiv : P.real {ω | ε * a i ≤ |X i ω|} ≤ C / (ε * a i) := by
    apply (le_div_iff₀ hpos).mpr
    nlinarith [hi.2]
  have heq : C / (ε * a i) = C / a i / ε := by ring
  exact hdiv.trans_eq heq

end Critical2DKPZ.Extensions.ScaleLimit
