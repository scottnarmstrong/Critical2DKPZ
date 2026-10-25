/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonLyapunov
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-! # Fourth-moment CLT for finite rows with positive limiting variance -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction NNReal

namespace Critical2DKPZ.Extensions.GffTangent

/-- Finite independent centered rows with a positive limiting variance and
vanishing total fourth moment converge to the corresponding Gaussian law. -/
theorem tendstoInDistribution_fin_sum_of_fourth_moments
    {κ Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filter κ) (n : κ → ℕ) (Y : (k : κ) → Fin (n k) → Ω → ℝ)
    (v : ℝ≥0) (s : ℝ) (hs : 0 < s) (hs2 : s ^ 2 = (v : ℝ))
    (hind : ∀ k, iIndepFun (Y k) P)
    (hm : ∀ k i, AEMeasurable (Y k i) P)
    (hmem : ∀ k i, MemLp (Y k i) 4 P)
    (hmean : ∀ k i, (∫ ω, Y k i ω ∂P) = 0)
    (hvar : Tendsto (fun k => ∑ i, ∫ ω, Y k i ω ^ 2 ∂P) F (𝓝 (s ^ 2)))
    (hfourth : Tendsto (fun k => ∑ i, ∫ ω, Y k i ω ^ 4 ∂P) F (𝓝 0)) :
    TendstoInDistribution (fun k ω => ∑ i, Y k i ω)
      F id (fun _ => P) (gaussianReal 0 v) := by
  have hthird : Tendsto (fun k => ∑ i, ∫ ω, |Y k i ω| ^ 3 ∂P) F (𝓝 0) := by
    have hlim := hvar.sqrt.mul hfourth.sqrt
    simp only [Real.sqrt_zero, mul_zero] at hlim
    apply squeeze_zero (fun k => Finset.sum_nonneg (fun i _ =>
      integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) 3))) ?_ hlim
    intro k
    exact (Finset.sum_le_sum (fun i _ => integral_abs_cube_le_second_fourth P (hmem k i))).trans
      (Real.sum_sqrt_mul_sqrt_le _ (fun i => integral_nonneg (fun ω => sq_nonneg _))
        (fun i => integral_nonneg (fun ω => by change 0 ≤ Y k i ω ^ 4; positivity)))
  have hsum (k : κ) : AEMeasurable (fun ω => ∑ i, Y k i ω) P :=
    Finset.aemeasurable_fun_sum _ (fun i _ => hm k i)
  apply (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hsum
    (measurable_id.aemeasurable : AEMeasurable id (gaussianReal 0 v))).mpr
  intro h
  let g : ℝ →ᵇ ℝ := h.compContinuous ⟨fun x => s * x, by fun_prop⟩
  have hmap : (gaussianReal 0 1).map (fun x => s * x) =
      gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.coe_injective
      simpa only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one] using hs2
  have hint : (∫ y, g y ∂gaussianReal 0 1) =
      ∫ y, h y ∂gaussianReal 0 v := by
    rw [← hmap, integral_map (by fun_prop) h.continuous.aestronglyMeasurable]
    rfl
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := ScaleLimit.exists_lyapunov_clt_bound_fin g (half_pos hε)
  have hv := (hvar.sub_const (s ^ 2)).abs
  simp only [sub_self, abs_zero] at hv
  filter_upwards [hv.eventually (gt_mem_nhds (mul_pos hδ (sq_pos_of_pos hs))),
    hthird.eventually (gt_mem_nhds (mul_pos hδ (pow_pos hs 3)))] with k hvk htk
  have hb := hbound P (n k) (Y k) s hs (hind k) (hm k)
    (fun i => (hmem k i).mono_exponent (by norm_num)) (hmean k) hvk.le htk.le
  have he (ω : Ω) : g ((∑ i, Y k i ω) / s) = h (∑ i, Y k i ω) := by
    change h (s * ((∑ i, Y k i ω) / s)) = _
    rw [mul_div_cancel₀ _ hs.ne']
  simp only [he, hint] at hb
  exact lt_of_le_of_lt (by simpa only [Real.dist_eq, id_eq] using hb) (half_lt_self hε)

end Critical2DKPZ.Extensions.GffTangent
