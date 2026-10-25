/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Uniform approximation for convergence in measure

A three-term metric estimate transfers convergence from approximating random
variables when both approximation errors are small in measure, uniformly in
the convergence index. A second-moment Markov bound supplies the error control.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Uniform approximation of a convergent family and its limit preserves convergence in measure. -/
theorem tendstoInMeasure_of_uniform_approximation
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (f : ℕ → Ω → E) (g : Ω → E)
    (fa : ℕ → ℕ → Ω → E) (ga : ℕ → Ω → E)
    (hconv : ∀ i, TendstoInMeasure P (fa i) atTop (ga i))
    (happrox : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ i,
      (∀ n, P.real {ω | ε ≤ dist (f n ω) (fa i n ω)} ≤ δ) ∧
        P.real {ω | ε ≤ dist (g ω) (ga i ω)} ≤ δ) :
    TendstoInMeasure P f atTop g := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro δ hδ
    obtain ⟨i, hleft, hright⟩ := happrox (ε / 3) (by positivity) (δ / 4) (by positivity)
    have hevent := ((tendstoInMeasure_iff_measureReal_dist.1 (hconv i)) (ε / 3)
      (by positivity)).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ / 4))
    filter_upwards [hevent] with n hn
    have hset : {ω | ε ≤ dist (f n ω) (g ω)} ⊆
        ({ω | ε / 3 ≤ dist (f n ω) (fa i n ω)} ∪
          {ω | ε / 3 ≤ dist (fa i n ω) (ga i ω)}) ∪
            {ω | ε / 3 ≤ dist (g ω) (ga i ω)} := by
      intro ω hω
      change ε ≤ dist (f n ω) (g ω) at hω
      by_contra hout
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hout
      have htri := dist_triangle4 (f n ω) (fa i n ω) (ga i ω) (g ω)
      rw [dist_comm (ga i ω) (g ω)] at htri
      linarith only [hω, hout.1.1, hout.1.2, hout.2, htri]
    have hbound : P.real {ω | ε ≤ dist (f n ω) (g ω)} ≤
        P.real {ω | ε / 3 ≤ dist (f n ω) (fa i n ω)} +
          P.real {ω | ε / 3 ≤ dist (fa i n ω) (ga i ω)} +
            P.real {ω | ε / 3 ≤ dist (g ω) (ga i ω)} := by
      exact (measureReal_mono hset).trans
        ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) (le_refl _)))
    linarith only [hbound, hleft n, hright, hn, hδ]

/-- The second-moment Markov bound for the real probability of a distance error. -/
theorem measureReal_dist_ge_le_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f g : Ω → ℝ)
    (hI : Integrable (fun ω => (f ω - g ω) ^ 2) P) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ dist (f ω) (g ω)} ≤ (∫ ω, (f ω - g ω) ^ 2 ∂P) / ε ^ 2 := by
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun ω => sq_nonneg (f ω - g ω))) hI (ε ^ 2)
  have hset : {ω | ε ≤ dist (f ω) (g ω)} ⊆ {ω | ε ^ 2 ≤ (f ω - g ω) ^ 2} := by
    intro ω hω
    change ε ≤ dist (f ω) (g ω) at hω
    change ε ^ 2 ≤ (f ω - g ω) ^ 2
    rw [Real.dist_eq] at hω
    exact (sq_le_sq₀ hε.le (abs_nonneg _) |>.2 hω).trans_eq (sq_abs _)
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  calc
    _ ≤ ε ^ 2 * P.real {ω | ε ^ 2 ≤ (f ω - g ω) ^ 2} := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (measureReal_mono hset) (sq_nonneg ε)
    _ ≤ _ := hMarkov

end Critical2DKPZ.SHF.Tsai

end
