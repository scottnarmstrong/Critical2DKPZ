/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! # Finite coordinate convergence in probability

The large-distance event of a finite vector lies in the union of the
coordinate large-distance events. The finite union estimate gives vector
convergence, hence convergence of expectations of bounded continuous tests.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.SHF.Tsai

/-- Coordinatewise convergence in measure gives convergence of a finite real vector. -/
theorem tendstoInMeasure_fintype_pi {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) (f : ℕ → Ω → I → ℝ) (g : Ω → I → ℝ)
    (hconv : ∀ i, TendstoInMeasure P (fun n ω => f n ω i) atTop (fun ω => g ω i)) :
    TendstoInMeasure P f atTop g := by
  classical
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hsum : Tendsto (fun n => ∑ i, P {ω | ε ≤ dist (f n ω i) (g ω i)}) atTop (𝓝 0) := by
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

/-- Bounded continuous expectations converge under finite coordinate convergence in measure. -/
theorem tendsto_integral_boundedContinuous_of_coordinatewise_tendstoInMeasure
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : ℕ → Ω → I → ℝ) (g : Ω → I → ℝ)
    (hfm : ∀ n i, AEMeasurable (fun ω => f n ω i) P)
    (hconv : ∀ i, TendstoInMeasure P (fun n ω => f n ω i) atTop (fun ω => g ω i))
    (H : (I → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, H (f n ω) ∂P) atTop (𝓝 (∫ ω, H (g ω) ∂P)) := by
  have hf (n) : AEMeasurable (f n) P := AEMeasurable.of_eval (hfm n)
  have hprob := tendstoInMeasure_fintype_pi P f g hconv
  have hdist := hprob.tendstoInDistribution hf
  exact (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hf
    hdist.aemeasurable_limit).1 hdist H

end Critical2DKPZ.SHF.Tsai

end
