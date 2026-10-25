/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralContraction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Dominated convergence in L2 for explicitly represented curves -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Pointwise convergence and an integrable square bound imply convergence
of the corresponding L2 classes. Representatives are specified explicitly. -/
theorem tendsto_L2_of_dominated_sq {ι α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure α) {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → Lp E 2 μ) (G : Lp E 2 μ) (f : ι → α → E) (g : α → E)
    (hF : ∀ᶠ i in l, (F i : α → E) =ᵐ[μ] f i) (hG : (G : α → E) =ᵐ[μ] g)
    {B : α → ℝ} (hB : Integrable B μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖f i x - g x‖ ^ 2 ≤ B x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    Tendsto F l (𝓝 G) := by
  let V : ι → α → ℝ := fun i x => ‖f i x - g x‖ ^ 2
  have hm : ∀ᶠ i in l, AEStronglyMeasurable (V i) μ := by
    filter_upwards [hF] with i hFi
    have hfi : AEStronglyMeasurable (f i) μ := (Lp.memLp (F i)).aestronglyMeasurable.congr hFi
    have hgi : AEStronglyMeasurable g μ := (Lp.memLp G).aestronglyMeasurable.congr hG
    exact (hfi.sub hgi).norm.pow 2
  have hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖V i x‖ ≤ B x := by
    filter_upwards [hbound] with i hi
    filter_upwards [hi] with x hx
    change |‖f i x - g x‖ ^ 2| ≤ B x
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hx
  have hp : ∀ᵐ x ∂μ, Tendsto (fun i => V i x) l (𝓝 0) := by
    filter_upwards [hlim] with x hx
    simpa only [V, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      ((hx.sub_const (g x)).norm.pow 2)
  have hi := tendsto_integral_filter_of_dominated_convergence B
    hm hb hB hp
  have hsq : Tendsto (fun i => ‖F i - G‖ ^ 2) l (𝓝 0) := by
    have heq : ∀ᶠ i in l, ‖F i - G‖ ^ 2 = ∫ x, V i x ∂μ := by
      filter_upwards [hF] with i hFi
      rw [norm_Lp_two_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (F i) G, hFi, hG] with x hsub hf hg
      change (F i - G) x = F i x - G x at hsub
      change ‖(F i - G) x‖ ^ 2 = ‖f i x - g x‖ ^ 2
      rw [hsub, hf, hg]
    have hi' : Tendsto (fun i => ∫ x, V i x ∂μ) l (𝓝 0) := by
      simpa only [integral_zero] using hi
    exact hi'.congr' (heq.mono fun _ h => h.symm)
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun i => Real.sqrt (‖F i - G‖ ^ 2)) l (𝓝 (Real.sqrt 0)) at hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

end Critical2DKPZ.Extensions.ScaleLimit
