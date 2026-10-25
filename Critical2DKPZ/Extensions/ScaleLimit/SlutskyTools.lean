/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

/-! # Deterministic perturbations of distributional limits

The constant-in-the-randomness convergence proof follows the private helper in
`Critical2DKPZ.LogNormality.SHFLogNormality`, with an arbitrary index filter.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Convergent deterministic real quantities converge in probability as constant variables. -/
theorem tendstoInMeasure_const_of_tendsto {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {l : Filter ι} {c : ι → ℝ} {c₀ : ℝ}
    (hc : Tendsto c l (𝓝 c₀)) :
    TendstoInMeasure P (fun i _ => c i) l (fun _ => c₀) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hclose := (Metric.tendsto_nhds.mp hc) ε hε
  have hzero : ∀ᶠ i in l, P {ω | ε ≤ ‖c i - c₀‖} = 0 := by
    filter_upwards [hclose] with i hi
    have hnorm : ‖c i - c₀‖ < ε := by simpa only [Real.dist_eq, Real.norm_eq_abs] using hi
    have hset : {ω : Ω | ε ≤ ‖c i - c₀‖} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro ω hω
      exact (not_le_of_gt hnorm) hω
    rw [hset, measure_empty]
  have heq : (fun i => P {ω | ε ≤ ‖c i - c₀‖}) =ᶠ[l] fun _ => 0 := hzero
  exact tendsto_const_nhds.congr' heq.symm

/-- Multiplication by a deterministic scalar converging to one preserves a real limit law. -/
theorem tendstoInDistribution_smul_of_tendsto {ι Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Ω') [IsProbabilityMeasure Q] {l : Filter ι} [l.IsCountablyGenerated]
    {X : ι → Ω → ℝ} {Z : Ω' → ℝ} {c : ι → ℝ}
    (hX : TendstoInDistribution X l Z (fun _ => P) Q) (hc : Tendsto c l (𝓝 1)) :
    TendstoInDistribution (fun i ω => c i * X i ω) l Z (fun _ => P) Q := by
  have h := hX.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop)
    (tendstoInMeasure_const_of_tendsto P hc) (fun _ => measurable_const.aemeasurable)
  simpa only [one_mul] using h

end Critical2DKPZ.Extensions.ScaleLimit
