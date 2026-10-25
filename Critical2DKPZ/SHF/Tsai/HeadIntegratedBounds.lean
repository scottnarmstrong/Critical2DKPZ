/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeadSpatialBound
public import Critical2DKPZ.SHF.Tsai.WeightedFormBoundIntegral
public import Critical2DKPZ.SHF.Tsai.HeadTimeConvolution
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.Tactic

/-! # Time integration for the four-particle head -/

@[expose] public section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

private def headTimeTriangle (s : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < s}

private noncomputable def headTriangleIntegrand (s : ℝ)
    (F : ℝ × ℝ → ℝ≥0∞) (p : ℝ × ℝ) : ℝ≥0∞ := by
  classical
  exact if p ∈ headTimeTriangle s then F p else 0

private theorem measurableSet_headTimeTriangle (s : ℝ) :
    MeasurableSet (headTimeTriangle s) := by
  change MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < s}
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt (measurable_fst.add measurable_snd) measurable_const))

private theorem lintegral_headTimeTriangle {s : ℝ} {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ r in Ioo 0 s, ∫⁻ v in Ioo 0 (s - r), F (r, v)) =
      ∫⁻ p : ℝ × ℝ, headTriangleIntegrand s F p ∂(volume.prod volume) := by
  classical
  have hD := measurableSet_headTimeTriangle s
  have hI : Measurable (fun p : ℝ × ℝ => headTriangleIntegrand s F p) := by
    change Measurable (fun p : ℝ × ℝ =>
      if p ∈ headTimeTriangle s then F p else 0)
    exact Measurable.ite hD hF measurable_const
  calc
    _ = ∫⁻ r, if r ∈ Ioo 0 s then
          ∫⁻ v in Ioo 0 (s - r), F (r, v) else 0 := by
            rw [← lintegral_indicator measurableSet_Ioo]
            apply lintegral_congr_ae
            filter_upwards [] with r
            by_cases hr : r ∈ Ioo 0 s
            · simp [hr]
            · simp [hr]
    _ = ∫⁻ r, ∫⁻ v, headTriangleIntegrand s F (r, v) := by
            apply lintegral_congr_ae
            filter_upwards [] with r
            by_cases hr : r ∈ Ioo 0 s
            · have hmem (v : ℝ) :
                  (r, v) ∈ headTimeTriangle s ↔ v ∈ Ioo 0 (s - r) := by
                simp only [headTimeTriangle, Set.mem_ofPred_eq, mem_Ioo]
                constructor
                · rintro ⟨_, hv, hsum⟩
                  exact ⟨hv, by linarith⟩
                · rintro ⟨hv, hvlt⟩
                  exact ⟨hr.1, hv, by linarith⟩
              rw [ite_eq_left hr]
              rw [← lintegral_indicator measurableSet_Ioo]
              apply lintegral_congr_ae
              filter_upwards [] with v
              rw [Set.indicator_apply, headTriangleIntegrand, hmem v]
              simp
            · rw [ite_eq_right hr]
              symm
              apply lintegral_eq_zero_of_ae_eq_zero
              filter_upwards [] with v
              have hnot (v : ℝ) : (r, v) ∉ headTimeTriangle s := by
                intro h
                apply hr
                simp only [mem_Ioo]
                exact ⟨h.1, by linarith [h.2.1, h.2.2]⟩
              simp [headTriangleIntegrand, hnot v]
    _ = ∫⁻ p : ℝ × ℝ,
          headTriangleIntegrand s F p ∂(volume.prod volume) := by
            exact (lintegral_prod _ hI.aemeasurable).symm

private theorem lintegral_translate_Ioo (r s : ℝ) (F : ℝ → ℝ≥0∞) :
    (∫⁻ u in Ioo r s, F (u - r)) = ∫⁻ v in Ioo 0 (s - r), F v := by
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.addLeft r
  have hAdd : MeasurePreserving (fun v : ℝ => r + v) volume volume :=
    measurePreserving_add_left volume r
  have hPre : e ⁻¹' Ioo r s = Ioo 0 (s - r) := by
    ext v
    simp [e, MeasurableEquiv.addLeft, mem_Ioo]
  have hMP := hAdd.restrict_preimage_emb e.measurableEmbedding (Ioo r s)
  have hMap := hMP.lintegral_comp_emb e.measurableEmbedding
    (fun u : ℝ => F (u - r))
  simpa [e, hPre, MeasurableEquiv.addLeft, sub_add_cancel] using hMap.symm

/-- The deleted-coordinate representation in the relative beta merge time. -/
theorem headKernel_eq_lintegral_deleted_relative {α β : CollisionPair 4}
    (i : Fin 4) (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i)
    (hβ : i = β.1.1 ∨ i = β.1.2) (θ s : ℝ)
    (x : Configuration 4) (w : FusedConfiguration β) :
    headKernel θ α β s x w =
      ∫⁻ r in Ioo 0 s, ∫⁻ v in Ioo 0 (s - r),
        ENNReal.ofReal (heatKernel s (w.1 - x i)) *
          deletedHeadSpatialSlice i hi₁ hi₂ θ r v (s - r - v) x w := by
  rw [headKernel_eq_lintegral_deletedSpatial i hi₁ hi₂ hβ θ s x w]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r _hr
  have hshift := lintegral_translate_Ioo r s
    (fun v => ENNReal.ofReal (heatKernel s (w.1 - x i)) *
      deletedHeadSpatialSlice i hi₁ hi₂ θ r v (s - r - v) x w)
  have hInner :
      (∫⁻ u in Ioo r s,
        ENNReal.ofReal (heatKernel s (w.1 - x i)) *
          deletedHeadSpatialSlice i hi₁ hi₂ θ r (u - r) (s - u) x w) =
        ∫⁻ v in Ioo 0 (s - r),
          ENNReal.ofReal (heatKernel s (w.1 - x i)) *
            deletedHeadSpatialSlice i hi₁ hi₂ θ r v (s - r - v) x w := by
    calc
      _ = ∫⁻ u in Ioo r s,
          (fun v => ENNReal.ofReal (heatKernel s (w.1 - x i)) *
            deletedHeadSpatialSlice i hi₁ hi₂ θ r v (s - r - v) x w) (u - r) := by
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
              congr 1
              rw [show s - r - (u - r) = s - u by ring]
      _ = _ := hshift
  exact hInner

private theorem measurable_headSpatialSlice_joint {α β : CollisionPair 4}
    (θ : ℝ) :
    Measurable (fun p : ((ℝ × ℝ) × (ℝ × (Configuration 4 × FusedConfiguration β))) =>
      @headSpatialSlice α β θ p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  classical
  have hInArg : Measurable (fun q : ((((ℝ × ℝ) × (ℝ × (Configuration 4 × FusedConfiguration β))) ×
      FusedConfiguration α) × FusedConfiguration α) =>
      (q.1.1.1.1, q.1.2, q.1.1.2.2.1)) := by
    fun_prop
  have hIn : Measurable (fun q : ((((ℝ × ℝ) × (ℝ × (Configuration 4 × FusedConfiguration β))) ×
      FusedConfiguration α) × FusedConfiguration α) =>
      ENNReal.ofReal (incomingKernel α q.1.1.1.1 q.1.2 q.1.1.2.2.1)) :=
    ((measurable_incomingKernel α).comp hInArg).ennreal_ofReal
  have hColArg : Measurable
      (fun q : ((((ℝ × ℝ) × (ℝ × (Configuration 4 × FusedConfiguration β))) ×
        FusedConfiguration α) × FusedConfiguration α) =>
        ((θ, q.1.1.1.2), (q.1.2, q.2))) := by
    fun_prop
  have hCol : Measurable (fun q : ((((ℝ × ℝ) × (ℝ × (Configuration 4 × FusedConfiguration β))) ×
      FusedConfiguration α) × FusedConfiguration α) =>
      ENNReal.ofReal (collisionKernel α θ q.1.1.1.2 q.1.2 q.2)) :=
    ((measurable_collisionKernel α).comp hColArg).ennreal_ofReal
  have hSwapArg : Measurable
      (fun q : ((((ℝ × ℝ) × (ℝ × (Configuration 4 × FusedConfiguration β))) ×
        FusedConfiguration α) × FusedConfiguration α) =>
        (q.1.1.2.1, q.2, q.1.1.2.2.2)) := by
    fun_prop
  have hSwap : Measurable (fun q : ((((ℝ × ℝ) × (ℝ × (Configuration 4 × FusedConfiguration β))) ×
      FusedConfiguration α) × FusedConfiguration α) =>
      ENNReal.ofReal (swappingKernel α β q.1.1.2.1 q.2 q.1.1.2.2.2)) :=
    ((measurable_swappingKernel α β).comp hSwapArg).ennreal_ofReal
  have hIntegrand : Measurable
      (fun q : ((((ℝ × ℝ) × (ℝ × (Configuration 4 × FusedConfiguration β))) ×
        FusedConfiguration α) × FusedConfiguration α) =>
        ENNReal.ofReal (incomingKernel α q.1.1.1.1 q.1.2 q.1.1.2.2.1) *
          ENNReal.ofReal (collisionKernel α θ q.1.1.1.2 q.1.2 q.2) *
            ENNReal.ofReal (swappingKernel α β q.1.1.2.1 q.2 q.1.1.2.2.2)) := by
    exact (hIn.mul hCol).mul hSwap
  have hInner : Measurable (fun q : ((ℝ × ℝ) × (ℝ × (Configuration 4 × FusedConfiguration β))) ×
      FusedConfiguration α =>
      ∫⁻ z' : FusedConfiguration α,
        ENNReal.ofReal (incomingKernel α q.1.1.1 q.2 q.1.2.2.1) *
          ENNReal.ofReal (collisionKernel α θ q.1.1.2 q.2 z') *
            ENNReal.ofReal (swappingKernel α β q.1.2.1 z' q.1.2.2.2) ∂volume) := by
    exact hIntegrand.lintegral_prod_right'
  have hOuter : Measurable (fun p : (ℝ × ℝ) × (ℝ × (Configuration 4 × FusedConfiguration β)) =>
      ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
        ENNReal.ofReal (incomingKernel α p.1.1 z p.2.2.1) *
          ENNReal.ofReal (collisionKernel α θ p.1.2 z z') *
            ENNReal.ofReal (swappingKernel α β p.2.1 z' p.2.2.2) ∂volume ∂volume) := by
    exact hInner.lintegral_prod_right'
  change Measurable (fun p : (ℝ × ℝ) × (ℝ × (Configuration 4 × FusedConfiguration β)) =>
    @headSpatialSlice α β θ p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)
  exact hOuter

private theorem measurable_headSpatialSlice_relative_joint {α β : CollisionPair 4}
    (θ s : ℝ) :
    Measurable (fun q : (ℝ × ℝ) × (Configuration 4 × FusedConfiguration β) =>
      @headSpatialSlice α β θ q.1.1 q.1.2 (s - q.1.1 - q.1.2) q.2.1 q.2.2) := by
  have hMap : Measurable
      (fun q : (ℝ × ℝ) × (Configuration 4 × FusedConfiguration β) =>
        (q.1, (s - q.1.1 - q.1.2, q.2))) := by
    fun_prop
  have hJoint : Measurable
      (fun p : (ℝ × ℝ) × (ℝ × (Configuration 4 × FusedConfiguration β)) =>
        @headSpatialSlice α β θ p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2) :=
    measurable_headSpatialSlice_joint (α := α) (β := β) θ
  change Measurable (fun q : (ℝ × ℝ) × (Configuration 4 × FusedConfiguration β) =>
    (fun p : (ℝ × ℝ) × (ℝ × (Configuration 4 × FusedConfiguration β)) =>
      @headSpatialSlice α β θ p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)
      (q.1, (s - q.1.1 - q.1.2, q.2)))
  exact hJoint.comp hMap

private theorem deletedHeadCoefficient_mono (θ p c r v q : ℝ)
    (hp : 2 < p) (hc : 0 < c) (hr : 0 < r) (hv : 0 < v) (hq : 0 < q) :
    ENNReal.ofReal (c * r ^ (-1 / p) * scalarDensity θ v *
      q ^ (-(1 : ℝ) / 2) * (r + v + q) ^ (-1 / p)) ≤
      ENNReal.ofReal (c * r ^ (-1 / p) * scalarDensity θ v *
        q ^ (-(1 / 2 + 1 / p : ℝ))) := by
  have hp0 : 0 < p := by linarith
  have hexp : -1 / p ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) hp0.le
  have htime : q ≤ r + v + q := by linarith
  have hpow : (r + v + q) ^ (-1 / p) ≤ q ^ (-1 / p) :=
    Real.rpow_le_rpow_of_nonpos hq htime hexp
  have hqhalf : 0 < q ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hq _
  have hqsum : q ^ (-(1 : ℝ) / 2) * q ^ (-1 / p) =
      q ^ (-(1 / 2 + 1 / p : ℝ)) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  have hpowProduct : q ^ (-(1 : ℝ) / 2) * (r + v + q) ^ (-1 / p) ≤
      q ^ (-(1 / 2 + 1 / p : ℝ)) := by
    calc
      _ ≤ q ^ (-(1 : ℝ) / 2) * q ^ (-1 / p) :=
        mul_le_mul_of_nonneg_left hpow hqhalf.le
      _ = _ := hqsum
  have hA : 0 ≤ c * r ^ (-1 / p) * scalarDensity θ v := by
    exact mul_nonneg (mul_nonneg hc.le (Real.rpow_pos_of_pos hr _).le)
      (scalarDensity_pos θ hv).le
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = (c * r ^ (-1 / p) * scalarDensity θ v) *
          (q ^ (-(1 : ℝ) / 2) * (r + v + q) ^ (-1 / p)) := by ring
    _ ≤ (c * r ^ (-1 / p) * scalarDensity θ v) * q ^ (-(1 / 2 + 1 / p : ℝ)) :=
      mul_le_mul_of_nonneg_left hpowProduct hA
    _ = _ := by ring

private theorem weightedFormBound_headSpatialSlice_from_deleted {α β : CollisionPair 4}
    (i : Fin 4) (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i)
    (hβ : i = β.1.1 ∨ i = β.1.2) (θ : ℝ) {p a : ℝ}
    (hp : 2 < p) (c : ℝ) (hc : 0 < c)
    (hDel : ∀ r v q : ℝ, 0 < r → 0 < v → 0 < q →
      WeightedFormBound volume volume
        (fun x : Configuration 4 => a * configurationOneNorm x)
        (fun _ : FusedConfiguration β => 0) 2 p
        (fun x w => ENNReal.ofReal (heatKernel (r + v + q) (w.1 - x i)) *
          deletedHeadSpatialSlice i hi₁ hi₂ θ r v q x w)
        (ENNReal.ofReal (c * r ^ (-1 / p) * scalarDensity θ v *
          q ^ (-(1 : ℝ) / 2) * (r + v + q) ^ (-1 / p)))) :
    ∀ r v q : ℝ, 0 < r → 0 < v → 0 < q →
      WeightedFormBound volume volume
        (fun x : Configuration 4 => a * configurationOneNorm x)
        (fun _ : FusedConfiguration β => 0) 2 p
        (@headSpatialSlice α β θ r v q)
        (ENNReal.ofReal (c * r ^ (-1 / p) * scalarDensity θ v *
          q ^ (-(1 / 2 + 1 / p : ℝ)))) := by
  intro r v q hr hv hq
  apply WeightedFormBound.mono (hDel r v q hr hv hq)
  · intro x w
    exact (lintegral_headSpatial_deleted_eq i hi₁ hi₂ hβ θ r v q hr hv hq x w).le
  · exact deletedHeadCoefficient_mono θ p c r v q hp hc hr hv hq

private theorem lintegral_headSpatialSlice_time_eq_headKernel {α β : CollisionPair 4}
    (i : Fin 4) (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i)
    (hβ : i = β.1.1 ∨ i = β.1.2) (θ s : ℝ)
    (x : Configuration 4) (w : FusedConfiguration β) :
    (∫⁻ t : ℝ × ℝ,
      headTriangleIntegrand s
        (fun u => @headSpatialSlice α β θ u.1 u.2 (s - u.1 - u.2) x w) t
      ∂(volume.prod volume)) = headKernel θ α β s x w := by
  have hSliceJoint := measurable_headSpatialSlice_relative_joint
    (α := α) (β := β) θ s
  have hSliceTime : Measurable (fun u : ℝ × ℝ =>
      @headSpatialSlice α β θ u.1 u.2 (s - u.1 - u.2) x w) := by
    have hMap : Measurable (fun u : ℝ × ℝ => (u, (x, w))) := by fun_prop
    change Measurable (fun u : ℝ × ℝ =>
      (fun q : (ℝ × ℝ) × (Configuration 4 × FusedConfiguration β) =>
        @headSpatialSlice α β θ q.1.1 q.1.2 (s - q.1.1 - q.1.2) q.2.1 q.2.2)
        (u, (x, w)))
    exact hSliceJoint.comp hMap
  have hParam :
      (∫⁻ t : ℝ × ℝ,
        headTriangleIntegrand s
          (fun u => @headSpatialSlice α β θ u.1 u.2 (s - u.1 - u.2) x w) t
        ∂(volume.prod volume)) =
        ∫⁻ r in Ioo 0 s, ∫⁻ v in Ioo 0 (s - r),
          @headSpatialSlice α β θ r v (s - r - v) x w := by
    exact (lintegral_headTimeTriangle (s := s) hSliceTime).symm
  have hHeadRel := headKernel_eq_lintegral_deleted_relative i hi₁ hi₂ hβ θ s x w
  have hNested :
      (∫⁻ r in Ioo 0 s, ∫⁻ v in Ioo 0 (s - r),
        @headSpatialSlice α β θ r v (s - r - v) x w) = headKernel θ α β s x w := by
    calc
      _ = ∫⁻ r in Ioo 0 s, ∫⁻ v in Ioo 0 (s - r),
            ENNReal.ofReal (heatKernel s (w.1 - x i)) *
              deletedHeadSpatialSlice i hi₁ hi₂ θ r v (s - r - v) x w := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
          have hq : 0 < s - r - v := by linarith [hr.2, hv.2]
          have hSliceEq := lintegral_headSpatial_deleted_eq i hi₁ hi₂ hβ θ
            r v (s - r - v) hr.1 hv.1 hq x w
          have hsum : r + v + (s - r - v) = s := by ring
          simpa [hsum] using hSliceEq
      _ = headKernel θ α β s x w := hHeadRel.symm
  exact hParam.trans hNested

/-- The scalar head coefficient after attaching the deleted planar coordinate
has the required time power, uniformly on compact time intervals. -/
theorem exists_headTimeCoefficient_bound (θ T p c : ℝ) (hp : 2 < p) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s → s ≤ T →
      (∫⁻ r in Ioo 0 s, ∫⁻ v in Ioo 0 (s - r),
        ENNReal.ofReal (c * r ^ (-1 / p) * scalarDensity θ v *
          (s - r - v) ^ (-(1 / 2 + 1 / p : ℝ)))) ≤
        ENNReal.ofReal (C * s ^ (1 / 2 - 2 / p)) := by
  obtain ⟨C₀, rate, hC₀, hrate, hTime⟩ :=
    exists_scalarDensity_head_time_lintegral_bound θ T p hp
  let C : ℝ := c * C₀ * Real.exp (rate * T)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro s hs hsT
  have hTime' := hTime s hs hsT
  have hfactor (r v : ℝ) (hr : 0 < r) (hv : 0 < v)
      (hq : 0 < s - r - v) :
      ENNReal.ofReal (c * r ^ (-1 / p) * scalarDensity θ v *
        (s - r - v) ^ (-(1 / 2 + 1 / p : ℝ))) =
        ENNReal.ofReal c *
          (ENNReal.ofReal (r ^ (-1 / p)) *
            (ENNReal.ofReal (scalarDensity θ v) *
              ENNReal.ofReal ((s - r - v) ^ (-(1 / 2 + 1 / p : ℝ))))) := by
    have hrpow : 0 < r ^ (-1 / p) := Real.rpow_pos_of_pos hr _
    have hden : 0 < scalarDensity θ v := scalarDensity_pos θ hv
    have hqpow : 0 < (s - r - v) ^ (-(1 / 2 + 1 / p : ℝ)) :=
      Real.rpow_pos_of_pos hq _
    calc
      _ = ENNReal.ofReal c * ENNReal.ofReal
          (r ^ (-1 / p) * scalarDensity θ v *
            (s - r - v) ^ (-(1 / 2 + 1 / p : ℝ))) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              ring
      _ = ENNReal.ofReal c *
          (ENNReal.ofReal (r ^ (-1 / p)) *
            ENNReal.ofReal (scalarDensity θ v *
              (s - r - v) ^ (-(1 / 2 + 1 / p : ℝ)))) := by
              rw [← ENNReal.ofReal_mul hrpow.le]
              congr 1
              ring_nf
      _ = _ := by
              rw [← ENNReal.ofReal_mul hden.le]
  have hIntegrandEq :
      (∫⁻ r in Ioo 0 s, ∫⁻ v in Ioo 0 (s - r),
        ENNReal.ofReal (c * r ^ (-1 / p) * scalarDensity θ v *
          (s - r - v) ^ (-(1 / 2 + 1 / p : ℝ)))) =
        ENNReal.ofReal c *
          (∫⁻ r in Ioo 0 s, ENNReal.ofReal (r ^ (-1 / p)) *
            (∫⁻ v in Ioo 0 (s - r), ENNReal.ofReal (scalarDensity θ v) *
              ENNReal.ofReal ((s - r - v) ^ (-(1 / 2 + 1 / p : ℝ))))) := by
    calc
      _ = ∫⁻ r in Ioo 0 s, ∫⁻ v in Ioo 0 (s - r), ENNReal.ofReal c *
            (ENNReal.ofReal (r ^ (-1 / p)) *
              (ENNReal.ofReal (scalarDensity θ v) *
                ENNReal.ofReal ((s - r - v) ^ (-(1 / 2 + 1 / p : ℝ))))) := by
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
              exact hfactor r v hr.1 hv.1 (by linarith [hr.2, hv.2])
      _ = ∫⁻ r in Ioo 0 s, ENNReal.ofReal c *
            (ENNReal.ofReal (r ^ (-1 / p)) *
              (∫⁻ v in Ioo 0 (s - r), ENNReal.ofReal (scalarDensity θ v) *
                ENNReal.ofReal ((s - r - v) ^ (-(1 / 2 + 1 / p : ℝ))))) := by
              apply lintegral_congr_ae
              filter_upwards [] with r
              calc
                (∫⁻ v in Ioo 0 (s - r), ENNReal.ofReal c *
                    (ENNReal.ofReal (r ^ (-1 / p)) *
                      (ENNReal.ofReal (scalarDensity θ v) *
                        ENNReal.ofReal ((s - r - v) ^ (-(1 / 2 + 1 / p : ℝ)))))) =
                  ENNReal.ofReal c * ∫⁻ v in Ioo 0 (s - r),
                    ENNReal.ofReal (r ^ (-1 / p)) *
                      (ENNReal.ofReal (scalarDensity θ v) *
                        ENNReal.ofReal ((s - r - v) ^ (-(1 / 2 + 1 / p : ℝ)))) :=
                          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
                _ = ENNReal.ofReal c *
                    (ENNReal.ofReal (r ^ (-1 / p)) *
                      ∫⁻ v in Ioo 0 (s - r), ENNReal.ofReal (scalarDensity θ v) *
                        ENNReal.ofReal ((s - r - v) ^ (-(1 / 2 + 1 / p : ℝ)))) := by
                          congr 1
                          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc
    _ = ENNReal.ofReal c *
          (∫⁻ r in Ioo 0 s, ENNReal.ofReal (r ^ (-1 / p)) *
            (∫⁻ v in Ioo 0 (s - r), ENNReal.ofReal (scalarDensity θ v) *
              ENNReal.ofReal ((s - r - v) ^ (-(1 / 2 + 1 / p : ℝ))))) := hIntegrandEq
    _ ≤ ENNReal.ofReal c *
          ENNReal.ofReal (C₀ * Real.exp (rate * s) * s ^ (1 / 2 - 2 / p)) := by
            exact mul_le_mul' le_rfl hTime'
    _ ≤ ENNReal.ofReal (C * s ^ (1 / 2 - 2 / p)) := by
          have hexp : Real.exp (rate * s) ≤ Real.exp (rate * T) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT hrate.le)
          have hsPow : 0 ≤ s ^ (1 / 2 - 2 / p) :=
            Real.rpow_nonneg hs.le _
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          calc
            c * (C₀ * Real.exp (rate * s) * s ^ (1 / 2 - 2 / p)) ≤
                c * (C₀ * Real.exp (rate * T) * s ^ (1 / 2 - 2 / p)) := by
                  apply mul_le_mul_of_nonneg_left
                  · exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hexp hC₀.le) hsPow
                  · exact hc.le
            _ = C * s ^ (1 / 2 - 2 / p) := by
                  dsimp [C]
                  ring

/-- The four-particle head kernel has a weighted bilinear form bound of order `t^{1/2 - 2/p}` on each bounded positive-time interval. -/
theorem weightedFormBound_headKernel (θ T : ℝ) {p a : ℝ}
    (hp : 2 < p) (ha : 0 < a)
    (α β : CollisionPair 4) (hαβ : α ≠ β) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, 0 < s → s ≤ T →
      WeightedFormBound volume volume
        (fun x : Configuration 4 => a * configurationOneNorm x)
        (fun _ : FusedConfiguration β => 0) 2 p
        (headKernel θ α β s)
        (ENNReal.ofReal (c * s ^ (1 / 2 - 2 / p))) := by
  classical
  obtain ⟨i, hiβ, hiα₁, hiα₂⟩ :=
    exists_beta_endpoint_outside_alpha α β hαβ
  have hi₁ : α.1.1 ≠ i := hiα₁.symm
  have hi₂ : α.1.2 ≠ i := hiα₂.symm
  obtain ⟨cDel, hcDel, hDel⟩ :=
    exists_weightedFormBound_deletedHeadSpatialSlice i hi₁ hi₂ hiβ θ hp ha
  obtain ⟨C, hC, hTimeCoeff⟩ :=
    exists_headTimeCoefficient_bound θ T p cDel hp hcDel
  refine ⟨C, hC, ?_⟩
  intro s hs hsT
  let Slice : (ℝ × ℝ) → Configuration 4 → FusedConfiguration β → ℝ≥0∞ :=
    fun t x w => @headSpatialSlice α β θ t.1 t.2 (s - t.1 - t.2) x w
  let Coeff : (ℝ × ℝ) → ℝ≥0∞ := fun t => ENNReal.ofReal
    (cDel * t.1 ^ (-1 / p) * scalarDensity θ t.2 *
      (s - t.1 - t.2) ^ (-(1 / 2 + 1 / p : ℝ)))
  let K : (ℝ × ℝ) → Configuration 4 → FusedConfiguration β → ℝ≥0∞ :=
    fun t x w => headTriangleIntegrand s (fun u => Slice u x w) t
  let cK : (ℝ × ℝ) → ℝ≥0∞ := fun t => headTriangleIntegrand s Coeff t
  have hSlice : Measurable
      (fun q : (ℝ × ℝ) × (Configuration 4 × FusedConfiguration β) =>
        Slice q.1 q.2.1 q.2.2) := by
    change Measurable (fun q : (ℝ × ℝ) × (Configuration 4 × FusedConfiguration β) =>
      @headSpatialSlice α β θ q.1.1 q.1.2 (s - q.1.1 - q.1.2) q.2.1 q.2.2)
    exact measurable_headSpatialSlice_relative_joint (α := α) (β := β) θ s
  have hDmeas : MeasurableSet (headTimeTriangle s) :=
    measurableSet_headTimeTriangle s
  have hKMeas : Measurable
      (fun q : (ℝ × ℝ) × (Configuration 4 × FusedConfiguration β) =>
        K q.1 q.2.1 q.2.2) := by
    change Measurable (fun q : (ℝ × ℝ) × (Configuration 4 × FusedConfiguration β) =>
      if q.1 ∈ headTimeTriangle s then Slice q.1 q.2.1 q.2.2 else 0)
    exact Measurable.ite (hDmeas.preimage measurable_fst) hSlice measurable_const
  have hCoeffReal : Measurable (fun t : (ℝ × ℝ) =>
      cDel * t.1 ^ (-1 / p) * scalarDensity θ t.2 *
        (s - t.1 - t.2) ^ (-(1 / 2 + 1 / p : ℝ))) := by
    have hDensity : Measurable (fun t : (ℝ × ℝ) => scalarDensity θ t.2) :=
      (measurable_scalarDensity.comp (measurable_const.prodMk measurable_snd))
    fun_prop
  have hCoeffMeas : Measurable Coeff := by
    change Measurable (fun t : (ℝ × ℝ) => ENNReal.ofReal
      (cDel * t.1 ^ (-1 / p) * scalarDensity θ t.2 *
        (s - t.1 - t.2) ^ (-(1 / 2 + 1 / p : ℝ))))
    exact hCoeffReal.ennreal_ofReal
  have hcKMeas : Measurable cK := by
    change Measurable (fun t : (ℝ × ℝ) =>
      if t ∈ headTimeTriangle s then Coeff t else 0)
    exact Measurable.ite hDmeas hCoeffMeas measurable_const
  have hBound : ∀ t : (ℝ × ℝ),
      WeightedFormBound volume volume
        (fun x : Configuration 4 => a * configurationOneNorm x)
        (fun _ : FusedConfiguration β => 0) 2 p (K t) (cK t) := by
    intro t
    by_cases ht : t ∈ headTimeTriangle s
    · have hr : 0 < t.1 := ht.1
      have hv : 0 < t.2 := ht.2.1
      have hq : 0 < s - t.1 - t.2 := by linarith [ht.2.2]
      let r := t.1
      let v := t.2
      let q := s - t.1 - t.2
      have hPoint := weightedFormBound_headSpatialSlice_from_deleted i hi₁ hi₂ hiβ
        θ hp cDel hcDel hDel r v q hr hv hq
      simpa [K, cK, Coeff, headTriangleIntegrand, Slice, r, v, q, ht] using hPoint
    · have hZero : WeightedFormBound volume volume
          (fun x : Configuration 4 => a * configurationOneNorm x)
          (fun _ : FusedConfiguration β => 0) 2 p
          (fun _ _ => 0) 0 := by
        intro f g hf hg
        simp
      simpa [K, cK, headTriangleIntegrand, ht] using hZero
  have hCoeffEq :
      (∫⁻ t : (ℝ × ℝ), cK t ∂(volume.prod volume)) =
        ∫⁻ r in Ioo 0 s, ∫⁻ v in Ioo 0 (s - r),
          ENNReal.ofReal (cDel * r ^ (-1 / p) * scalarDensity θ v *
            (s - r - v) ^ (-(1 / 2 + 1 / p : ℝ))) := by
    change (∫⁻ t : (ℝ × ℝ), headTriangleIntegrand s Coeff t ∂(volume.prod volume)) = _
    exact (lintegral_headTimeTriangle (s := s) hCoeffMeas).symm
  have hCoeffBound :
      (∫⁻ t : (ℝ × ℝ), cK t ∂(volume.prod volume)) ≤
        ENNReal.ofReal (C * s ^ (1 / 2 - 2 / p)) := by
    rw [hCoeffEq]
    exact hTimeCoeff s hs hsT
  have hW : WeightedFormBound volume volume
      (fun x : Configuration 4 => a * configurationOneNorm x)
      (fun _ : FusedConfiguration β => 0) 2 p
      (fun x w => ∫⁻ t : (ℝ × ℝ), K t x w ∂(volume.prod volume))
      (∫⁻ t : (ℝ × ℝ), cK t ∂(volume.prod volume)) :=
    WeightedFormBound.lintegral_param hKMeas hcKMeas hBound
  have hKernelEq (x : Configuration 4) (w : FusedConfiguration β) :
      (∫⁻ t : (ℝ × ℝ), K t x w ∂(volume.prod volume)) = headKernel θ α β s x w := by
    change (∫⁻ t : ℝ × ℝ,
      headTriangleIntegrand s
        (fun u => @headSpatialSlice α β θ u.1 u.2 (s - u.1 - u.2) x w) t
      ∂(volume.prod volume)) = _
    exact lintegral_headSpatialSlice_time_eq_headKernel i hi₁ hi₂ hiβ θ s x w
  apply WeightedFormBound.mono hW
    (fun x w => (hKernelEq x w).symm.le)
    hCoeffBound

end Critical2DKPZ.SHF.Tsai

end
