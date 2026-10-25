/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeatKernelPointwise
public import Critical2DKPZ.SHF.Tsai.HilbertContractionLimits
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Strong heat approximation of compact continuous spatial tests

Pointwise heat approximation and the uniform bound on the heat average give
convergence of its pairing with the compact test. The `L²` contraction and
the Hilbert-space distance identity upgrade this to strong `L²` convergence.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology CompactlySupported InnerProductSpace

namespace Critical2DKPZ.SHF.Tsai

/-- Positive heat times tending to zero approximate every compact continuous test in `L²`. -/
theorem tendsto_eLpNorm_heat_sub_compact (t : ℕ → ℝ) (ht : ∀ n, 0 < t n)
    (htlim : Tendsto t atTop (𝓝 0)) (g : C_c(Plane, ℝ)) :
    Tendsto (fun n => eLpNorm (mollifierAction (heatKernel (t n)) g - (g : Plane → ℝ)) 2) atTop (𝓝 0) := by
  have hgc : Continuous (g : Plane → ℝ) := map_continuous g
  have hg : MemLp (g : Plane → ℝ) 2 := hgc.memLp_of_hasCompactSupport g.hasCompactSupport
  have hIg : Integrable (g : Plane → ℝ) := hgc.integrable_of_hasCompactSupport g.hasCompactSupport
  have hheat (n) := mollifierAction_heat_memLp_and_eLpNorm_le (ht n) g hg
  let G := hg.toLp (g : Plane → ℝ)
  let T (n : ℕ) := (hheat n).1.toLp (mollifierAction (heatKernel (t n)) g)
  have hnorm (n) : ‖T n‖ ≤ ‖G‖ := by
    simpa only [T, G, Lp.norm_toLp] using ENNReal.toReal_mono hg.eLpNorm_ne_top (hheat n).2
  have hinner (n) : ⟪T n, G⟫_ℝ = ∫ x : Plane, g x * mollifierAction (heatKernel (t n)) g x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hheat n).1.coeFn_toLp, hg.coeFn_toLp] with x hx hxg
    simp only [T, G, hx, hxg, RCLike.inner_apply, conj_trivial]
  have hGsq : (∫ x : Plane, g x ^ 2) = ‖G‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    simp only [G, hx, RCLike.inner_apply, conj_trivial, pow_two]
  let C := ‖g.toBoundedContinuousFunction‖
  have hC (x : Plane) : ‖g x‖ ≤ C := g.toBoundedContinuousFunction.norm_coe_le_norm x
  have hfm (n) : AEStronglyMeasurable
      (fun x : Plane => g x * mollifierAction (heatKernel (t n)) g x) volume :=
    hg.aestronglyMeasurable.mul (hheat n).1.aestronglyMeasurable
  have hbound (n) (x : Plane) : ‖g x * mollifierAction (heatKernel (t n)) g x‖ ≤ ‖g x‖ * C := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (mollifierAction_heat_integrable_norm_le (ht n) g hg C hC x).2 (norm_nonneg _)
  have hlim (x : Plane) : Tendsto (fun n => g x * mollifierAction (heatKernel (t n)) g x)
      atTop (𝓝 (g x ^ 2)) := by
    simpa only [pow_two] using
      (tendsto_mollifierAction_heat_pointwise_of_bounded t ht htlim g hgc C hC x).const_mul (g x)
  have hDCT := tendsto_integral_filter_of_dominated_convergence (fun x : Plane => ‖g x‖ * C)
    (Eventually.of_forall hfm) (Eventually.of_forall (fun n => Eventually.of_forall (hbound n)))
    (hIg.norm.mul_const C) (Eventually.of_forall hlim)
  rw [hGsq] at hDCT
  have hpair : Tendsto (fun n => ⟪T n, G⟫_ℝ) atTop (𝓝 (‖G‖ ^ 2)) := by
    simpa only [hinner] using hDCT
  have hstrong := tendsto_of_norm_le_of_inner_tendsto T G hnorm hpair
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => mollifierAction (heatKernel (t n)) g) (fun n => (hheat n).1) g hg).1 hstrong

end Critical2DKPZ.SHF.Tsai

end
