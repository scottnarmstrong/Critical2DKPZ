/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeadCoordinateSplit
public import Critical2DKPZ.SHF.Tsai.HeadGaussian
public import Critical2DKPZ.SHF.Tsai.HeadTail
public import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.MeasureTheory.Measure.Prod

/-! # Integrating a deleted endpoint in the four-particle head -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

private theorem measurable_heatKernel_sub_left (t : ℝ) (a : Plane) :
    Measurable (fun x : Plane => heatKernel t (x - a)) := by
  have hm : Measurable (fun x : Plane => x - a) := measurable_id.sub measurable_const
  exact (measurable_heatKernel t).comp hm

private theorem measurable_heatKernel_sub_right (t : ℝ) (a : Plane) :
    Measurable (fun x : Plane => heatKernel t (a - x)) := by
  have hm : Measurable (fun x : Plane => a - x) := measurable_const.sub measurable_id
  exact (measurable_heatKernel t).comp hm

private theorem measurable_heatKernel_sub_diff (t : ℝ) :
    Measurable (fun p : Plane × Plane => heatKernel t (p.2 - p.1)) := by
  have hm : Measurable (fun p : Plane × Plane => p.2 - p.1) :=
    measurable_snd.sub measurable_fst
  exact (measurable_heatKernel t).comp hm

private theorem measurable_prodRect {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {R : X → X → ℝ≥0∞} {H : Y → Y → ℝ≥0∞}
    (hR : Measurable (Function.uncurry R)) (hH : Measurable (Function.uncurry H)) :
    Measurable (fun p : (X × Y) × (X × Y) => R p.1.1 p.2.1 * H p.1.2 p.2.2) := by
  have hRmap : Measurable (fun p : (X × Y) × (X × Y) => (p.1.1, p.2.1)) :=
    measurable_fst.fst.prodMk measurable_snd.fst
  have hHmap : Measurable (fun p : (X × Y) × (X × Y) => (p.1.2, p.2.2)) :=
    measurable_fst.snd.prodMk measurable_snd.snd
  exact (hR.comp hRmap).mul (hH.comp hHmap)

private theorem collisionKernel_nonneg_of_pos {n : ℕ} (α : CollisionPair n) (θ : ℝ)
    {t : ℝ} (ht : 0 < t) (z z' : FusedConfiguration α) :
    0 ≤ collisionKernel α θ t z z' :=
  (collisionKernel_pos α θ ht z z').le

private theorem headFactorReindex {α β : CollisionPair 4}
    (i : Fin 4) (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i)
    (hβ : i = β.1.1 ∨ i = β.1.2) (θ r v q : ℝ)
    (hr : 0 < r) (hv : 0 < v) (hq : 0 < q)
    (x : Configuration 4) (w : FusedConfiguration β)
    (z z' : FusedConfiguration α) :
    ENNReal.ofReal (incomingKernel α r z x) *
        ENNReal.ofReal (collisionKernel α θ v z z') *
          ENNReal.ofReal (swappingKernel α β q z' w) =
      (ENNReal.ofReal (incomingKernel (omittedCollisionPair i α hi₁ hi₂) r
        ((omittedAlphaFusedEquiv i α hi₁ hi₂ z).1) (omittedFullPart i x)) *
        ENNReal.ofReal (collisionKernel (omittedCollisionPair i α hi₁ hi₂) θ v
          ((omittedAlphaFusedEquiv i α hi₁ hi₂ z).1)
          ((omittedAlphaFusedEquiv i α hi₁ hi₂ z').1)) *
        ENNReal.ofReal (freeKernel 3 q
          (collisionEmbedding (omittedCollisionPair i α hi₁ hi₂)
            ((omittedAlphaFusedEquiv i α hi₁ hi₂ z').1))
          (omittedFullPart i (collisionEmbedding β w)))) *
      (ENNReal.ofReal (heatKernel r
          ((omittedAlphaFusedEquiv i α hi₁ hi₂ z).2 - x i)) *
        ENNReal.ofReal (heatKernel v
          ((omittedAlphaFusedEquiv i α hi₁ hi₂ z').2 -
            (omittedAlphaFusedEquiv i α hi₁ hi₂ z).2)) *
        ENNReal.ofReal (heatKernel q
          (w.1 - (omittedAlphaFusedEquiv i α hi₁ hi₂ z').2))) := by
  rw [incomingKernel_omitted_factor i α hi₁ hi₂ r z x,
    collisionKernel_omitted_factor i α hi₁ hi₂ θ v z z',
    swappingKernel_omitted_factor i α β hi₁ hi₂ hβ q z' w]
  have hcol : 0 ≤ collisionKernel (omittedCollisionPair i α hi₁ hi₂) θ v
      ((omittedAlphaFusedEquiv i α hi₁ hi₂ z).1)
      ((omittedAlphaFusedEquiv i α hi₁ hi₂ z').1) :=
    collisionKernel_nonneg_of_pos (n := 3) _ θ hv _ _
  rw [ENNReal.ofReal_mul (heatKernel_nonneg hr.le _),
    ENNReal.ofReal_mul hcol,
    ENNReal.ofReal_mul (heatKernel_nonneg hq.le _)]
  ac_rfl

private theorem lintegral_iterated_mul {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    (f : X → ℝ≥0∞) (g : Y → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, ∫⁻ y, f x * g y ∂ν ∂μ) = (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν := by
  have hm : Measurable (fun z : X × Y => f z.1 * g z.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  calc
    _ = ∫⁻ z : X × Y, f z.1 * g z.2 ∂μ.prod ν :=
      lintegral_lintegral hm.aemeasurable
    _ = _ := lintegral_prod_mul hf.aemeasurable hg.aemeasurable

private theorem lintegral_pair_comp {X Y : Type*} [MeasureSpace X] [MeasureSpace Y]
    [SFinite (volume : Measure X)] [SFinite (volume : Measure Y)]
    (e : X ≃ᵐ Y) (hMP : MeasurePreserving e (volume : Measure X) (volume : Measure Y))
    {f : Y → Y → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) :
    (∫⁻ x : X, ∫⁻ x' : X, f (e x) (e x')) =
      ∫⁻ y : Y, ∫⁻ y' : Y, f y y' := by
  have hInner (x : X) : Measurable (fun y : Y => f (e x) y) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have hOuter : Measurable (fun y : Y => ∫⁻ y' : Y, f y y' ∂(volume : Measure Y)) :=
    hf.lintegral_prod_right'
  calc
    _ = ∫⁻ x : X, ∫⁻ y : Y, f (e x) y := by
      apply lintegral_congr
      intro x
      exact hMP.lintegral_comp (hInner x)
    _ = _ := hMP.lintegral_comp hOuter

private theorem lintegral_rect_pair_assoc {X Y : Type*} [MeasureSpace X] [MeasureSpace Y]
    [SFinite (volume : Measure X)] [SFinite (volume : Measure Y)]
    {f : (X × Y) → (X × Y) → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) :
    (∫⁻ p : X × Y, ∫⁻ p' : X × Y, f p p') =
      ∫⁻ x : X, ∫⁻ y : Y, ∫⁻ x' : X, ∫⁻ y' : Y, f (x, y) (x', y') := by
  calc
    _ = ∫⁻ p : X × Y, ∫⁻ x' : X, ∫⁻ y' : Y, f p (x', y') := by
      apply lintegral_congr
      intro p
      rw [Measure.volume_eq_prod]
      exact lintegral_prod (fun p' : X × Y => f p p')
        ((hf.comp (measurable_const.prodMk measurable_id)).aemeasurable)
    _ = ∫⁻ x : X, ∫⁻ y : Y, ∫⁻ x' : X, ∫⁻ y' : Y, f (x, y) (x', y') := by
      have hOuter : Measurable (fun p : X × Y => ∫⁻ p' : X × Y, f p p') :=
        hf.lintegral_prod_right'
      calc
        _ = ∫⁻ p : X × Y, ∫⁻ p' : X × Y, f p p' := by
          apply lintegral_congr
          intro p
          symm
          rw [Measure.volume_eq_prod]
          exact lintegral_prod (fun p' : X × Y => f p p')
            ((hf.comp (measurable_const.prodMk measurable_id)).aemeasurable)
        _ = ∫⁻ x : X, ∫⁻ y : Y, ∫⁻ p' : X × Y, f (x, y) p' := by
          rw [Measure.volume_eq_prod]
          exact lintegral_prod _ hOuter.aemeasurable
        _ = _ := by
          apply lintegral_congr
          intro x
          apply lintegral_congr
          intro y
          rw [Measure.volume_eq_prod]
          exact lintegral_prod (fun p' : X × Y => f (x, y) p')
            ((hf.comp (measurable_const.prodMk measurable_id)).aemeasurable)

private theorem lintegral_rect_product {X : Type*} [MeasureSpace X]
    [SFinite (volume : Measure X)] [SFinite (volume : Measure Plane)]
    {R : X → X → ℝ≥0∞} {H : Plane → Plane → ℝ≥0∞}
    (hR : Measurable (Function.uncurry R)) (hH : Measurable (Function.uncurry H)) :
    (∫⁻ x : X, ∫⁻ ξ : Plane, ∫⁻ x' : X, ∫⁻ ξ' : Plane,
      R x x' * H ξ ξ') =
      (∫⁻ x : X, ∫⁻ x' : X, R x x') *
        ∫⁻ ξ : Plane, ∫⁻ ξ' : Plane, H ξ ξ' := by
  calc
    _ = ∫⁻ x : X, ∫⁻ ξ : Plane,
        (∫⁻ x' : X, R x x') * ∫⁻ ξ' : Plane, H ξ ξ' := by
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro ξ
      exact lintegral_iterated_mul (R x) (H ξ)
        (hR.comp (measurable_const.prodMk measurable_id))
        (hH.comp (measurable_const.prodMk measurable_id))
    _ = _ := lintegral_iterated_mul
      (fun x => ∫⁻ x' : X, R x x') (fun ξ => ∫⁻ ξ' : Plane, H ξ ξ')
      hR.lintegral_prod_right' hH.lintegral_prod_right'

private theorem lintegral_heat_three (r v q : ℝ) (hr : 0 < r) (hv : 0 < v)
    (hq : 0 < q) (a b : Plane) :
    (∫⁻ ξ : Plane, ∫⁻ ξ' : Plane,
      ENNReal.ofReal (heatKernel r (ξ - a)) *
        ENNReal.ofReal (heatKernel v (ξ' - ξ)) *
          ENNReal.ofReal (heatKernel q (b - ξ'))) =
      ENNReal.ofReal (heatKernel (r + v + q) (b - a)) := by
  have hInner (ξ : Plane) :
      (∫⁻ ξ' : Plane,
        ENNReal.ofReal (heatKernel r (ξ - a)) *
          ENNReal.ofReal (heatKernel v (ξ' - ξ)) *
            ENNReal.ofReal (heatKernel q (b - ξ'))) =
        ENNReal.ofReal (heatKernel r (ξ - a)) *
          ENNReal.ofReal (heatKernel (v + q) (b - ξ)) := by
    have hconst : ENNReal.ofReal (heatKernel r (ξ - a)) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc
      _ = ∫⁻ ξ' : Plane,
          ENNReal.ofReal (heatKernel r (ξ - a)) *
            (ENNReal.ofReal (heatKernel v (ξ' - ξ)) *
              ENNReal.ofReal (heatKernel q (b - ξ'))) := by
              apply lintegral_congr
              intro ξ'
              exact (mul_assoc _ _ _)
      _ = ENNReal.ofReal (heatKernel r (ξ - a)) *
          ∫⁻ ξ' : Plane,
            ENNReal.ofReal (heatKernel v (ξ' - ξ)) *
              ENNReal.ofReal (heatKernel q (b - ξ')) :=
                lintegral_const_mul' _ _ hconst
      _ = _ := by rw [lintegral_heatKernel_shifted_mul hv hq ξ b]
  calc
    _ = ∫⁻ ξ : Plane,
        ENNReal.ofReal (heatKernel r (ξ - a)) *
          ENNReal.ofReal (heatKernel (v + q) (b - ξ)) := by
      apply lintegral_congr
      exact hInner
    _ = _ := by
      simpa [add_assoc] using
        (lintegral_heatKernel_shifted_mul hr (add_pos hv hq) a b)

private noncomputable def deletedHeadR {γ : CollisionPair 3} (θ r v q : ℝ)
    (x' y' : Configuration 3) (z z' : FusedConfiguration γ) : ℝ≥0∞ :=
  ENNReal.ofReal (incomingKernel γ r z x') *
    ENNReal.ofReal (collisionKernel γ θ v z z') *
      ENNReal.ofReal (freeKernel 3 q (collisionEmbedding γ z') y')

private noncomputable def deletedHeadH (r v q : ℝ) (a b ξ ξ' : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (heatKernel r (ξ - a)) *
    ENNReal.ofReal (heatKernel v (ξ' - ξ)) *
      ENNReal.ofReal (heatKernel q (b - ξ'))

private theorem measurable_deletedHeadR {γ : CollisionPair 3} (θ r v q : ℝ)
    (x' y' : Configuration 3) :
    Measurable (Function.uncurry (deletedHeadR (γ := γ) θ r v q x' y')) := by
  change Measurable (fun p : FusedConfiguration γ × FusedConfiguration γ =>
    ENNReal.ofReal (incomingKernel γ r p.1 x') *
      ENNReal.ofReal (collisionKernel γ θ v p.1 p.2) *
        ENNReal.ofReal (freeKernel 3 q (collisionEmbedding γ p.2) y'))
  have hin : Measurable (fun p : FusedConfiguration γ × FusedConfiguration γ =>
      incomingKernel γ r p.1 x') := by
    exact (measurable_incomingKernel γ).comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_const))
  have hcol : Measurable (fun p : FusedConfiguration γ × FusedConfiguration γ =>
      collisionKernel γ θ v p.1 p.2) := by
    have hm : Measurable (fun p : FusedConfiguration γ × FusedConfiguration γ => ((θ, v), p)) :=
      measurable_const.prodMk measurable_id
    exact (measurable_collisionKernel γ).comp hm
  have hem : Measurable (fun p : FusedConfiguration γ × FusedConfiguration γ =>
      collisionEmbedding γ p.2) := measurable_collisionEmbedding γ |>.comp measurable_snd
  have hfree : Measurable (fun p : FusedConfiguration γ × FusedConfiguration γ =>
      freeKernel 3 q (collisionEmbedding γ p.2) y') := by
    exact (measurable_freeKernel 3).comp
      (measurable_const.prodMk (hem.prodMk measurable_const))
  exact ((hin.ennreal_ofReal).mul (hcol.ennreal_ofReal)).mul hfree.ennreal_ofReal

private theorem measurable_deletedHeadH (r v q : ℝ) (a b : Plane) :
    Measurable (Function.uncurry (deletedHeadH r v q a b)) := by
  change Measurable (fun p : Plane × Plane =>
    ENNReal.ofReal (heatKernel r (p.1 - a)) *
      ENNReal.ofReal (heatKernel v (p.2 - p.1)) *
        ENNReal.ofReal (heatKernel q (b - p.2)))
  have h1 := measurable_heatKernel_sub_left r a
  have h2 := measurable_heatKernel_sub_diff v
  have h3 := measurable_heatKernel_sub_right q b
  have hH₁ : Measurable (fun p : Plane × Plane =>
      ENNReal.ofReal (heatKernel r (p.1 - a))) := (h1.comp measurable_fst).ennreal_ofReal
  have hH₂ : Measurable (fun p : Plane × Plane =>
      ENNReal.ofReal (heatKernel v (p.2 - p.1))) := h2.ennreal_ofReal
  have hH₃ : Measurable (fun p : Plane × Plane =>
      ENNReal.ofReal (heatKernel q (b - p.2))) := (h3.comp measurable_snd).ennreal_ofReal
  exact (hH₁.mul hH₂).mul hH₃

/-- The fixed-time spatial part of the literal four-particle head. -/
noncomputable def headSpatialSlice {α β : CollisionPair 4}
    (θ r v q : ℝ) (x : Configuration 4) (w : FusedConfiguration β) : ℝ≥0∞ :=
    ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
      ENNReal.ofReal (incomingKernel α r z x) *
        ENNReal.ofReal (collisionKernel α θ v z z') *
          ENNReal.ofReal (swappingKernel α β q z' w)

/-- The literal head is the time-simplex integral of its fixed-time spatial
slice. -/
theorem headKernel_eq_lintegral_headSpatialSlice (θ s : ℝ) (α β : CollisionPair 4)
    (x : Configuration 4) (w : FusedConfiguration β) :
    headKernel θ α β s x w =
      ∫⁻ r in Set.Ioo 0 s, ∫⁻ u in Set.Ioo r s,
        @headSpatialSlice α β θ r (u - r) (s - u) x w := by
  unfold headKernel headSpatialSlice
  rfl

/-- The reduced three-particle block obtained after deleting one free label. -/
noncomputable def deletedHeadSpatialSlice {α β : CollisionPair 4}
    (i : Fin 4) (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i)
    (θ r v q : ℝ) (x : Configuration 4) (w : FusedConfiguration β) : ℝ≥0∞ :=
    let γ := omittedCollisionPair i α hi₁ hi₂
    let x' := omittedFullPart i x
    let y' := omittedFullPart i (collisionEmbedding β w)
    ∫⁻ z : FusedConfiguration γ, ∫⁻ z' : FusedConfiguration γ,
      ENNReal.ofReal (incomingKernel γ r z x') *
        ENNReal.ofReal (collisionKernel γ θ v z z') *
          ENNReal.ofReal (freeKernel 3 q (collisionEmbedding γ z') y')

/-- At fixed positive times, integrating the two four-particle collision
coordinates collapses the heat strands on a label outside `α` to the single
total-time heat kernel. The remaining integral is the literal three-particle
incoming/collision/free block. -/
theorem lintegral_headSpatial_deleted_eq {α β : CollisionPair 4}
    (i : Fin 4) (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i)
    (hβ : i = β.1.1 ∨ i = β.1.2) (θ r v q : ℝ)
    (hr : 0 < r) (hv : 0 < v) (hq : 0 < q)
    (x : Configuration 4) (w : FusedConfiguration β) :
    @headSpatialSlice α β θ r v q x w =
      ENNReal.ofReal (heatKernel (r + v + q) (w.1 - x i)) *
        @deletedHeadSpatialSlice α β i hi₁ hi₂ θ r v q x w := by
  classical
  rw [headSpatialSlice, deletedHeadSpatialSlice]
  let γ := omittedCollisionPair i α hi₁ hi₂
  let e := omittedAlphaFusedEquiv i α hi₁ hi₂
  let x' := omittedFullPart i x
  let y' := omittedFullPart i (collisionEmbedding β w)
  let R : FusedConfiguration γ → FusedConfiguration γ → ℝ≥0∞ :=
    deletedHeadR (γ := γ) θ r v q x' y'
  let H : Plane → Plane → ℝ≥0∞ := deletedHeadH r v q (x i) w.1
  let G : (FusedConfiguration γ × Plane) → (FusedConfiguration γ × Plane) → ℝ≥0∞ :=
    fun z z' => R z.1 z'.1 * H z.2 z'.2
  have hR : Measurable (fun p : FusedConfiguration γ × FusedConfiguration γ =>
      R p.1 p.2) := measurable_deletedHeadR (γ := γ) θ r v q x' y'
  have hH : Measurable (Function.uncurry H) :=
    measurable_deletedHeadH r v q (x i) w.1
  have hG' : Measurable (Function.uncurry G) := by
    exact measurable_prodRect hR hH
  have hFactor (z z' : FusedConfiguration α) :
      ENNReal.ofReal (incomingKernel α r z x) *
        ENNReal.ofReal (collisionKernel α θ v z z') *
          ENNReal.ofReal (swappingKernel α β q z' w) = G (e z) (e z') := by
    simpa only [G, R, H, e, deletedHeadR, deletedHeadH] using
      headFactorReindex i hi₁ hi₂ hβ θ r v q hr hv hq x w z z'
  have hMP := measurePreserving_omittedAlphaFusedEquiv i α hi₁ hi₂
  calc
    _ = ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
        G (e z) (e z') := by
          apply lintegral_congr
          intro z
          apply lintegral_congr
          intro z'
          exact hFactor z z'
    _ = ∫⁻ z : FusedConfiguration γ × Plane,
        ∫⁻ z' : FusedConfiguration γ × Plane, G z z' :=
          lintegral_pair_comp e hMP hG'
    _ = ∫⁻ z : FusedConfiguration γ, ∫⁻ ξ : Plane,
        ∫⁻ z' : FusedConfiguration γ, ∫⁻ ξ' : Plane,
          R z z' * H ξ ξ' := by
            rw [lintegral_rect_pair_assoc hG']
    _ = (∫⁻ z : FusedConfiguration γ, ∫⁻ z' : FusedConfiguration γ, R z z') *
        ENNReal.ofReal (heatKernel (r + v + q) (w.1 - x i)) := by
          calc
            _ = (∫⁻ z : FusedConfiguration γ, ∫⁻ z' : FusedConfiguration γ, R z z') *
                ∫⁻ ξ : Plane, ∫⁻ ξ' : Plane, H ξ ξ' := lintegral_rect_product hR hH
            _ = _ := by
              congr 1
              simpa only [H, deletedHeadH] using
                lintegral_heat_three r v q hr hv hq (x i) w.1
    _ = _ := by
      dsimp [R, x', y', γ, deletedHeadR]
      rw [mul_comm]

/-- The literal head is a time-simplex integral of the total-time deleted
coordinate heat strand times the reduced three-particle block. -/
theorem headKernel_eq_lintegral_deletedSpatial {α β : CollisionPair 4}
    (i : Fin 4) (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i)
    (hβ : i = β.1.1 ∨ i = β.1.2) (θ s : ℝ)
    (x : Configuration 4) (w : FusedConfiguration β) :
    headKernel θ α β s x w =
      ∫⁻ r in Set.Ioo 0 s, ∫⁻ u in Set.Ioo r s,
        ENNReal.ofReal (heatKernel s (w.1 - x i)) *
          @deletedHeadSpatialSlice α β i hi₁ hi₂ θ r (u - r) (s - u) x w := by
  rw [headKernel_eq_lintegral_headSpatialSlice]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hrpos : 0 < r := hr.1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hv : 0 < u - r := sub_pos.mpr hu.1
  have hq : 0 < s - u := sub_pos.mpr hu.2
  have hfactor := lintegral_headSpatial_deleted_eq i hi₁ hi₂ hβ θ r (u - r) (s - u)
    hrpos hv hq x w
  have htime : r + (u - r) + (s - u) = s := by ring
  rw [hfactor, htime]

end Critical2DKPZ.SHF.Tsai

end
