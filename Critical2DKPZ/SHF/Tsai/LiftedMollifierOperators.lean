/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.LiftedMollifiers
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Bounded mollifier operators on one planar coordinate

The fiberwise convolution descends to the product-space `L²` quotient. The
product norm estimate supplies continuity, and fiberwise dominated convergence
makes the resulting operators converge strongly to the identity.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Product-space a.e. equality suffices for a.e. equality of the lifted convolution. -/
theorem leftMollifierAction_congr_ae {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SigmaFinite μ] (w : Plane → ℝ) {F G : Plane × Y → ℝ}
    (h : F =ᵐ[(volume : Measure Plane).prod μ] G) :
    leftMollifierAction w F =ᵐ[(volume : Measure Plane).prod μ] leftMollifierAction w G := by
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := (volume : Measure Plane))).quasiMeasurePreserving.ae_eq_comp h
  have hsections := Measure.ae_ae_of_ae_prod hswap
  have hlift := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Plane)) (ν := μ)).ae hsections
  filter_upwards [hlift] with q hq
  apply integral_congr_ae
  filter_upwards [hq] with y hy
  change F (y, q.2) = G (y, q.2) at hy
  rw [hy]

/-- The lifted integral is additive on product-space `L²` data, almost everywhere. -/
theorem leftMollifierAction_add_ae {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SigmaFinite μ] {w : Plane → ℝ} (hw : MemLp w 2)
    {F G : Plane × Y → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hF : MemLp F 2 ((volume : Measure Plane).prod μ)) (hG : MemLp G 2 ((volume : Measure Plane).prod μ)) :
    leftMollifierAction w (F + G) =ᵐ[(volume : Measure Plane).prod μ]
      leftMollifierAction w F + leftMollifierAction w G := by
  have hFfiber := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Plane)) (ν := μ)).ae
    (ae_memLp_prod_left (volume : Measure Plane) μ hFm hF)
  have hGfiber := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Plane)) (ν := μ)).ae
    (ae_memLp_prod_left (volume : Measure Plane) μ hGm hG)
  filter_upwards [hFfiber, hGfiber] with q hq hq'
  simp only [leftMollifierAction, Pi.add_apply, mul_add]
  exact integral_add (integrable_mollifierAction_integrand hw hq q.1)
    (integrable_mollifierAction_integrand hw hq' q.1)

/-- Scalar multiplication commutes with each lifted integral. -/
theorem leftMollifierAction_smul {Y : Type*} (w : Plane → ℝ) (F : Plane × Y → ℝ) (a : ℝ) :
    leftMollifierAction w (a • F) = a • leftMollifierAction w F := by
  funext q
  simp only [leftMollifierAction, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

/-- The actual lifted convolution as a linear map on product-space `L²` classes. -/
def leftMollifierLinearMap {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SigmaFinite μ] {w : ℕ → Plane → ℝ} (hw : IsL2ApplicableMollifier w) (j : ℕ) :
    Lp ℝ 2 ((volume : Measure Plane).prod μ) →ₗ[ℝ] Lp ℝ 2 ((volume : Measure Plane).prod μ) where
  toFun F := ((leftMollifierAction_memLp_and_tendsto μ hw
    (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).1 j).toLp (leftMollifierAction (w j) F)
  map_add' F G := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact (leftMollifierAction_congr_ae μ (w j) (Lp.coeFn_add F G)).trans
      (leftMollifierAction_add_ae μ (hw.2.2.1 j) (Lp.stronglyMeasurable F).measurable
        (Lp.stronglyMeasurable G).measurable (Lp.memLp F) (Lp.memLp G))
  map_smul' a F := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    have h := leftMollifierAction_congr_ae μ (w j) (Lp.coeFn_smul a F)
    filter_upwards [h] with q hq
    simpa only [leftMollifierAction_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using hq

/-- One finite real constant controls all lifted operators and all product-space inputs. -/
theorem exists_leftMollifierLinearMap_uniform_bound {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SigmaFinite μ] {w : ℕ → Plane → ℝ} (hw : IsL2ApplicableMollifier w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j (F : Lp ℝ 2 ((volume : Measure Plane).prod μ)),
      ‖leftMollifierLinearMap μ hw j F‖ ≤ C * ‖F‖ := by
  obtain ⟨M, hMfin, hM⟩ := exists_mollifierAction_uniform_bound hw
  refine ⟨M.toReal, ENNReal.toReal_nonneg, fun j F => ?_⟩
  change ‖((leftMollifierAction_memLp_and_tendsto μ hw
    (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).1 j).toLp (leftMollifierAction (w j) F)‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hMfin (Lp.eLpNorm_ne_top F))
    (eLpNorm_leftMollifierAction_le μ (hw.2.1 j).measurable (hM j)
      (Lp.stronglyMeasurable F).measurable (Lp.memLp F))
  simpa only [ENNReal.toReal_mul] using h

/-- The bounded mollifier acting on the planar coordinate of the product. -/
def leftMollifierOperator {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SigmaFinite μ] {w : ℕ → Plane → ℝ} (hw : IsL2ApplicableMollifier w) (j : ℕ) :
    Lp ℝ 2 ((volume : Measure Plane).prod μ) →L[ℝ] Lp ℝ 2 ((volume : Measure Plane).prod μ) :=
  (leftMollifierLinearMap μ hw j).mkContinuousOfExistsBound (by
    obtain ⟨C, _, hC⟩ := exists_leftMollifierLinearMap_uniform_bound μ hw
    exact ⟨C, hC j⟩)

/-- The lifted mollifier operator agrees almost everywhere with convolution in the first coordinate. -/
theorem coe_leftMollifierOperator {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SigmaFinite μ] {w : ℕ → Plane → ℝ} (hw : IsL2ApplicableMollifier w) (j : ℕ)
    (F : Lp ℝ 2 ((volume : Measure Plane).prod μ)) :
    ⇑(leftMollifierOperator μ hw j F) =ᵐ[(volume : Measure Plane).prod μ] leftMollifierAction (w j) F :=
  ((leftMollifierAction_memLp_and_tendsto μ hw (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).1 j).coeFn_toLp

/-- The lifted bounded operators converge strongly to the identity. -/
theorem tendsto_leftMollifierOperator {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SigmaFinite μ] {w : ℕ → Plane → ℝ} (hw : IsL2ApplicableMollifier w)
    (F : Lp ℝ 2 ((volume : Measure Plane).prod μ)) : Tendsto (fun j => leftMollifierOperator μ hw j F) atTop (𝓝 F) := by
  have hlim := (leftMollifierAction_memLp_and_tendsto μ hw
    (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).2
  have heq : (fun j => eLpNorm (⇑(leftMollifierOperator μ hw j F) - ⇑F) 2 ((volume : Measure Plane).prod μ)) =
      fun j => eLpNorm (fun q => leftMollifierAction (w j) F q - F q) 2 ((volume : Measure Plane).prod μ) := by
    funext j
    apply eLpNorm_congr_ae
    filter_upwards [coe_leftMollifierOperator μ hw j F] with q hq
    change leftMollifierOperator μ hw j F q - F q = leftMollifierAction (w j) F q - F q
    rw [hq]
  rw [← heq] at hlim
  have h := Lp.tendsto_Lp_of_tendsto_eLpNorm (F : Plane × Y → ℝ) (Lp.memLp F) hlim
  simpa only [Lp.toLp_coeFn] using h

end Critical2DKPZ.SHF.Tsai

end
