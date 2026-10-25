/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConvergenceApproximation

/-! # Second-moment approximation of limits in probability

Uniformly vanishing integrable second-moment errors imply the uniform
probability approximation required by the three-term convergence argument.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Convergence in measure passes through approximations with uniformly vanishing second moments. -/
theorem tendstoInMeasure_of_uniform_sq_approximation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (fa : ℕ → ℕ → Ω → ℝ) (ga : ℕ → Ω → ℝ)
    (hconv : ∀ i, TendstoInMeasure P (fa i) atTop (ga i))
    (A B : ℕ → ℝ) (hA : Tendsto A atTop (𝓝 0)) (hB : Tendsto B atTop (𝓝 0))
    (hleft : ∀ i n, Integrable (fun ω => (f n ω - fa i n ω) ^ 2) P ∧
      (∫ ω, (f n ω - fa i n ω) ^ 2 ∂P) ≤ A i)
    (hright : ∀ i, Integrable (fun ω => (g ω - ga i ω) ^ 2) P ∧
      (∫ ω, (g ω - ga i ω) ^ 2 ∂P) ≤ B i) :
    TendstoInMeasure P f atTop g := by
  apply tendstoInMeasure_of_uniform_approximation P f g fa ga hconv
  intro ε hε δ hδ
  have hsmall : (0 : ℝ) < δ * ε ^ 2 := mul_pos hδ (sq_pos_of_pos hε)
  obtain ⟨i, hiA, hiB⟩ := ((hA.eventually (gt_mem_nhds hsmall)).and
    (hB.eventually (gt_mem_nhds hsmall))).exists
  refine ⟨i, fun n => ?_, ?_⟩
  · apply (measureReal_dist_ge_le_integral_sq P (f n) (fa i n) (hleft i n).1 hε).trans
    apply (div_le_iff₀ (sq_pos_of_pos hε)).2
    exact (hleft i n).2.trans hiA.le
  · apply (measureReal_dist_ge_le_integral_sq P g (ga i) (hright i).1 hε).trans
    apply (div_le_iff₀ (sq_pos_of_pos hε)).2
    exact (hright i).2.trans hiB.le

end Critical2DKPZ.SHF.Tsai

end
