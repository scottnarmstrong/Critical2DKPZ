/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.CausalComposition
import Mathlib.Tactic

/-! # Three causal kernels as an ordered pair of collision times -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The spatial middle integral can be moved past the second elapsed-time integral. -/
theorem lintegral_kernel_middle_swap {X Y Z W : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]
    (ν : Measure Y) (η : Measure Z) [SFinite ν] [SFinite η]
    {K : TimeKernel X Y} {L : TimeKernel Y Z} {M : TimeKernel Z W}
    (hK : Measurable K) (hL : Measurable L) (hM : Measurable M)
    (r b : ℝ) (x : X) (w : W) :
    (∫⁻ y, K (r, x, y) *
      (∫⁻ s in Ioo 0 b, ∫⁻ z, L (s, y, z) * M (b - s, z, w) ∂η) ∂ν) =
      ∫⁻ s in Ioo 0 b, ∫⁻ y, ∫⁻ z,
        K (r, x, y) * L (s, y, z) * M (b - s, z, w) ∂η ∂ν := by
  have hG (y : Y) : Measurable (fun p : ℝ × Z => L (p.1, y, p.2) * M (b - p.1, p.2, w)) :=
    (hL.comp (by fun_prop)).mul (hM.comp (by fun_prop))
  have hF : Measurable (fun p : (Y × ℝ) × Z =>
      K (r, x, p.1.1) * (L (p.1.2, p.1.1, p.2) * M (b - p.1.2, p.2, w))) := by
    have h1 : Measurable (fun p : (Y × ℝ) × Z => K (r, x, p.1.1)) := hK.comp (by fun_prop)
    have h2 : Measurable (fun p : (Y × ℝ) × Z => L (p.1.2, p.1.1, p.2)) := hL.comp (by fun_prop)
    have h3 : Measurable (fun p : (Y × ℝ) × Z => M (b - p.1.2, p.2, w)) := hM.comp (by fun_prop)
    exact h1.mul (h2.mul h3)
  calc
    (∫⁻ y, K (r, x, y) *
        (∫⁻ s in Ioo 0 b, ∫⁻ z, L (s, y, z) * M (b - s, z, w) ∂η) ∂ν)
        = ∫⁻ y, (∫⁻ s in Ioo 0 b,
          K (r, x, y) * (∫⁻ z, L (s, y, z) * M (b - s, z, w) ∂η)) ∂ν := by
          apply lintegral_congr
          intro y
          exact (lintegral_const_mul _ (hG y).lintegral_prod_right').symm
    _ = ∫⁻ s in Ioo 0 b, ∫⁻ y,
          K (r, x, y) * (∫⁻ z, L (s, y, z) * M (b - s, z, w) ∂η) ∂ν := by
      have hm : Measurable (fun p : Y × ℝ => K (r, x, p.1) *
          (∫⁻ z, L (p.2, p.1, z) * M (b - p.2, z, w) ∂η)) := by
        have h1 : Measurable (fun p : Y × ℝ => K (r, x, p.1)) := hK.comp (by fun_prop)
        have h2 : Measurable (fun p : (Y × ℝ) × Z =>
            L (p.1.2, p.1.1, p.2) * M (b - p.1.2, p.2, w)) :=
          (hL.comp (by fun_prop)).mul (hM.comp (by fun_prop))
        exact h1.mul h2.lintegral_prod_right'
      exact lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro s
      apply lintegral_congr
      intro y
      have hz : Measurable (fun z : Z => L (s, y, z) * M (b - s, z, w)) :=
        (hG y).comp (measurable_const.prodMk measurable_id)
      rw [← lintegral_const_mul _ hz]
      apply lintegral_congr
      intro z
      exact (mul_assoc _ _ _).symm

/-- Composing three causal factors gives the ordered collision-time integral with `r < u`. -/
theorem timeKernelComp_three_causal_eq {X Y Z W : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]
    (ν : Measure Y) (η : Measure Z) [SFinite ν] [SFinite η]
    {K : TimeKernel X Y} {L : TimeKernel Y Z} {M : TimeKernel Z W}
    (hK : Measurable K) (hL : Measurable L) (hM : Measurable M)
    (t : ℝ) (x : X) (w : W) :
    timeKernelComp ν (causalKernel K) (timeKernelComp η (causalKernel L) (causalKernel M)) (t, x, w) =
      ∫⁻ r in Ioo 0 t, ∫⁻ u in Ioo r t, ∫⁻ y, ∫⁻ z,
        K (r, x, y) * L (u - r, y, z) * M (t - u, z, w) ∂η ∂ν := by
  have hm := measurable_timeKernelComp η (measurable_causalKernel hL) (measurable_causalKernel hM)
  conv_lhs => rw [← timeKernelComp_causal η L M]
  rw [timeKernelComp_causal_eq ν hK hm]
  apply lintegral_congr
  intro r
  simp only [timeKernelComp_causal_eq η hL hM]
  rw [lintegral_kernel_middle_swap ν η hK hL hM,
    lintegral_Ioo_sub_right r t]
  apply lintegral_congr
  intro u
  have he : t - r - (u - r) = t - u := by ring
  simp only [he]

end Critical2DKPZ.DeltaBose
