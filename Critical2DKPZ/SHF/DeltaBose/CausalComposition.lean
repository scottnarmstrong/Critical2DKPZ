/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.TimeKernelComposition
import Mathlib.Tactic

/-! # Causal kernels and ordered elapsed-time integrals -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Zero extension from strictly positive elapsed times. -/
noncomputable def causalKernel {X Y : Type*} (K : TimeKernel X Y) : TimeKernel X Y :=
  fun p => if 0 < p.1 then K p else 0

/-- The causal extension of a measurable time kernel is measurable. -/
theorem measurable_causalKernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {K : TimeKernel X Y} (hK : Measurable K) : Measurable (causalKernel K) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_fst) hK measurable_const

/-- A causal kernel agrees with its original kernel at positive times. -/
@[simp] theorem causalKernel_of_pos {X Y : Type*} (K : TimeKernel X Y) {t : ℝ}
    (ht : 0 < t) (x : X) (y : Y) : causalKernel K (t, x, y) = K (t, x, y) := ite_eq_left ht

/-- A causal kernel vanishes at nonpositive times. -/
@[simp] theorem causalKernel_of_nonpos {X Y : Type*} (K : TimeKernel X Y) {t : ℝ}
    (ht : t ≤ 0) (x : X) (y : Y) : causalKernel K (t, x, y) = 0 := ite_eq_right (not_lt.mpr ht)

/-- A composition of causal kernels is causal, without a convergence assumption. -/
theorem timeKernelComp_causal {X Y Z : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (K : TimeKernel X Y) (L : TimeKernel Y Z) :
    causalKernel (timeKernelComp ν (causalKernel K) (causalKernel L)) =
      timeKernelComp ν (causalKernel K) (causalKernel L) := by
  funext ⟨t, x, z⟩
  by_cases ht : 0 < t
  · exact ite_eq_left ht
  · rw [causalKernel, ite_eq_right ht]
    symm
    change (∫⁻ q : ℝ × Y, causalKernel K (q.1, x, q.2) *
      causalKernel L (t - q.1, q.2, z) ∂volume.prod ν) = 0
    have he : (fun q : ℝ × Y => causalKernel K (q.1, x, q.2) *
        causalKernel L (t - q.1, q.2, z)) = fun _ => 0 := by
      funext q
      by_cases hq : 0 < q.1
      · rw [causalKernel_of_nonpos L (by linarith only [ht, hq]), mul_zero]
      · rw [causalKernel_of_nonpos K (not_lt.mp hq), zero_mul]
    rw [he, lintegral_zero]

/-- Full-line causal composition is exactly the positive elapsed-time integral. -/
theorem timeKernelComp_causal_eq {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) [SFinite ν] {K : TimeKernel X Y} {L : TimeKernel Y Z}
    (hK : Measurable K) (hL : Measurable L) (t : ℝ) (x : X) (z : Z) :
    timeKernelComp ν (causalKernel K) (causalKernel L) (t, x, z) =
      ∫⁻ r in Ioo 0 t, ∫⁻ y, K (r, x, y) * L (t - r, y, z) ∂ν := by
  have hm : Measurable (fun q : ℝ × Y =>
      causalKernel K (q.1, x, q.2) * causalKernel L (t - q.1, q.2, z)) :=
    ((measurable_causalKernel hK).comp (by fun_prop)).mul
      ((measurable_causalKernel hL).comp (by fun_prop))
  rw [timeKernelComp, lintegral_prod _ hm.aemeasurable, ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ Ioo 0 t
  · rw [indicator_of_mem hr]
    apply lintegral_congr
    intro y
    rw [causalKernel_of_pos K hr.1, causalKernel_of_pos L (sub_pos.mpr hr.2)]
  · rw [indicator_of_notMem hr]
    have he : (fun y : Y => causalKernel K (r, x, y) * causalKernel L (t - r, y, z)) =
        fun _ => 0 := by
      funext y
      by_cases h0 : 0 < r
      · have h1 : t ≤ r := le_of_not_gt (fun h => hr ⟨h0, h⟩)
        rw [causalKernel_of_nonpos L (sub_nonpos.mpr h1), mul_zero]
      · rw [causalKernel_of_nonpos K (not_lt.mp h0), zero_mul]
    rw [he, lintegral_zero]

/-- Translating elapsed time into the next absolute collision time. -/
theorem lintegral_Ioo_sub_right (r t : ℝ) (F : ℝ → ℝ≥0∞) :
    (∫⁻ s in Ioo 0 (t - r), F s) = ∫⁻ u in Ioo r t, F (u - r) := by
  have hm : MeasurePreserving (fun u : ℝ => u - r) := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-r)
  have he := hm.lintegral_comp_emb (MeasurableEquiv.subRight r).measurableEmbedding
    ((Ioo 0 (t - r)).indicator F)
  have hi : (fun u : ℝ => (Ioo 0 (t - r)).indicator F (u - r)) =
      (Ioo r t).indicator (fun u => F (u - r)) := by
    funext u
    have hmem : u - r ∈ Ioo 0 (t - r) ↔ u ∈ Ioo r t := by
      simp only [mem_Ioo]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith only [h1], by linarith only [h2]⟩
    simp only [indicator, hmem]
  rw [hi, lintegral_indicator measurableSet_Ioo, lintegral_indicator measurableSet_Ioo] at he
  exact he.symm

end Critical2DKPZ.DeltaBose
