/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.PotentialFusedRows
public import Critical2DKPZ.SHF.DeltaBose.WeightedSchur
import Mathlib.Tactic

/-! # Time-integrated swapping rows and their Schur bound -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Time integration of the distinct-pair Gaussian swapping block. -/
noncomputable def integratedSwappingKernel {n : ℕ} (α β : CollisionPair n)
    (z : FusedConfiguration α) (w : FusedConfiguration β) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (swappingKernel α β t z w)

/-- The finite constant left by time integration of the potential row bound. -/
noncomputable def integratedPotentialRowConstant : ℝ≥0∞ :=
  (ENNReal.ofReal ((2 * Real.pi)⁻¹) * halfTimeResolventConstant) *
    ENNReal.ofReal ((2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹)

/-- The integrated heat-potential row constant is finite. -/
theorem integratedPotentialRowConstant_ne_top :
    integratedPotentialRowConstant ≠ ⊤ := by
  unfold integratedPotentialRowConstant
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top halfTimeResolventConstant_ne_top)
    ENNReal.ofReal_ne_top

/-- Integrating the row bound against the doubled-time heat kernel gives a constant multiple of the heat potential. -/
theorem lintegral_heatPotentialRowBound_mul_heatKernel_eq_constant (x : Plane) :
    (∫⁻ t in Ioi (0 : ℝ), heatPotentialRowBound t *
      ENNReal.ofReal (heatKernel (2 * t) x)) =
      integratedPotentialRowConstant * heatPotential x := by
  rw [lintegral_heatPotentialRowBound_mul_heatKernel_double]
  unfold integratedPotentialRowConstant
  ac_rfl

private theorem measurable_joint_swappingKernel {n : ℕ} (α β : CollisionPair n) :
    Measurable (fun p : ℝ × (FusedConfiguration α × FusedConfiguration β) =>
      ENNReal.ofReal (swappingKernel α β p.1 p.2.1 p.2.2)) := by
  have hHeat : Measurable (fun p : ℝ × Plane => heatKernel p.1 p.2) := by
    unfold heatKernel
    fun_prop
  have hα : Measurable
      (fun p : ℝ × (FusedConfiguration α × FusedConfiguration β) =>
        collisionEmbedding α p.2.1) := (measurable_collisionEmbedding α).comp (by fun_prop)
  have hβ : Measurable
      (fun p : ℝ × (FusedConfiguration α × FusedConfiguration β) =>
        collisionEmbedding β p.2.2) := (measurable_collisionEmbedding β).comp (by fun_prop)
  change Measurable (fun p : ℝ × (FusedConfiguration α × FusedConfiguration β) =>
    ENNReal.ofReal (∏ i, heatKernel p.1
      ((collisionEmbedding β p.2.2) i - (collisionEmbedding α p.2.1) i)))
  have hprod : Measurable (fun p : ℝ × (FusedConfiguration α × FusedConfiguration β) =>
      ∏ i, heatKernel p.1 ((collisionEmbedding β p.2.2) i -
        (collisionEmbedding α p.2.1) i)) := by
    apply Finset.measurable_fun_prod
    intro i hi
    have hc : Measurable
        (fun p : ℝ × (FusedConfiguration α × FusedConfiguration β) =>
          (p.1, (collisionEmbedding β p.2.2) i - (collisionEmbedding α p.2.1) i)) := by
      exact measurable_fst.prodMk
        (((measurable_pi_apply i).comp hβ).sub ((measurable_pi_apply i).comp hα))
    exact hHeat.comp hc
  exact hprod.ennreal_ofReal

/-- The integrated swapping kernel is jointly measurable in its fused endpoints. -/
theorem measurable_integratedSwappingKernel {n : ℕ} (α β : CollisionPair n) :
    Measurable (Function.uncurry (integratedSwappingKernel α β)) := by
  have hK : Measurable (fun p : (FusedConfiguration α × FusedConfiguration β) × ℝ =>
      ENNReal.ofReal (swappingKernel α β p.2 p.1.1 p.1.2)) :=
    (measurable_joint_swappingKernel α β).comp measurable_swap
  have h := hK.lintegral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))
  change Measurable (fun p : FusedConfiguration α × FusedConfiguration β =>
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (swappingKernel α β t p.1 p.2))
  exact h

/-- Integrated potential-weighted row bound for every distinct pair. -/
theorem lintegral_integratedSwappingKernel_sourceWeight_le {n : ℕ}
    (α β : CollisionPair n) (hne : α ≠ β) (z : FusedConfiguration α) :
    (∫⁻ w : FusedConfiguration β,
      integratedSwappingKernel α β z w *
        heatPotential ((collisionEmbedding β w) α.1.1 -
          (collisionEmbedding β w) α.1.2)) ≤
      integratedPotentialRowConstant *
        heatPotential ((collisionEmbedding α z) β.1.2 -
          (collisionEmbedding α z) β.1.1) := by
  let W : FusedConfiguration β → ℝ≥0∞ := fun w =>
    heatPotential ((collisionEmbedding β w) α.1.1 -
      (collisionEmbedding β w) α.1.2)
  let T : ℝ → FusedConfiguration β → ℝ≥0∞ := fun t w =>
    ENNReal.ofReal (swappingKernel α β t z w)
  have hfinite := heatPotential_swappingWeight_ne_top_ae α β hne
  have hjoint : Measurable (fun p : FusedConfiguration β × ℝ => T p.2 p.1 * W p.1) := by
    have hK : Measurable (fun p : FusedConfiguration β × ℝ => T p.2 p.1) := by
      have hbase := measurable_joint_swappingKernel α β
      exact hbase.comp (measurable_snd.prodMk
        (measurable_const.prodMk measurable_fst))
    have hW : Measurable W := by
      dsimp [W]
      have he : Measurable (fun w : FusedConfiguration β => collisionEmbedding β w) :=
        measurable_collisionEmbedding β
      exact measurable_heatPotential.comp
        (((measurable_pi_apply α.1.1).comp he).sub
          ((measurable_pi_apply α.1.2).comp he))
    exact hK.mul (hW.comp measurable_fst)
  calc (∫⁻ w : FusedConfiguration β,
        integratedSwappingKernel α β z w *
          heatPotential ((collisionEmbedding β w) α.1.1 -
            (collisionEmbedding β w) α.1.2))
      = ∫⁻ w : FusedConfiguration β, ∫⁻ t in Ioi (0 : ℝ), T t w * W w := by
          apply lintegral_congr_ae
          filter_upwards [hfinite] with w hw
          rw [integratedSwappingKernel, lintegral_mul_const' _ _ hw]
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ w : FusedConfiguration β, T t w * W w :=
          lintegral_lintegral_swap hjoint.aemeasurable
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), heatPotentialRowBound t *
          ENNReal.ofReal (heatKernel (2 * t)
            ((collisionEmbedding α z) β.1.2 - (collisionEmbedding α z) β.1.1)) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact lintegral_swappingPotential_row_le α β hne ht z
    _ = integratedPotentialRowConstant *
          heatPotential ((collisionEmbedding α z) β.1.2 -
            (collisionEmbedding α z) β.1.1) :=
          lintegral_heatPotentialRowBound_mul_heatKernel_eq_constant _

/-- The time-integrated distinct-pair swapping operator is bounded on ordinary
`L²`, by a positive Schur weight built from the heat potential. -/
theorem integratedSwappingKernel_l2_sq_le {n : ℕ} (α β : CollisionPair n)
    (hne : α ≠ β) {f : FusedConfiguration β → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : FusedConfiguration α,
      (∫⁻ w : FusedConfiguration β,
        integratedSwappingKernel α β z w * f w) ^ 2) ≤
      integratedPotentialRowConstant ^ 2 *
        ∫⁻ w : FusedConfiguration β, f w ^ 2 := by
  let K : FusedConfiguration α → FusedConfiguration β → ℝ≥0∞ :=
    integratedSwappingKernel α β
  let v : FusedConfiguration α → ℝ≥0∞ := fun z =>
    heatPotential ((collisionEmbedding α z) β.1.2 - (collisionEmbedding α z) β.1.1)
  let w : FusedConfiguration β → ℝ≥0∞ := fun z =>
    heatPotential ((collisionEmbedding β z) α.1.1 - (collisionEmbedding β z) α.1.2)
  have hK : Measurable (Function.uncurry K) := measurable_integratedSwappingKernel α β
  have hv : Measurable v := by
    dsimp [v]
    have he := measurable_collisionEmbedding α
    exact measurable_heatPotential.comp
      (((measurable_pi_apply β.1.2).comp he).sub ((measurable_pi_apply β.1.1).comp he))
  have hw : Measurable w := by
    dsimp [w]
    have he := measurable_collisionEmbedding β
    exact measurable_heatPotential.comp
      (((measurable_pi_apply α.1.1).comp he).sub ((measurable_pi_apply α.1.2).comp he))
  have hwfinite : ∀ᵐ y : FusedConfiguration β, w y ≠ 0 ∧ w y ≠ ⊤ := by
    filter_upwards [heatPotential_swappingWeight_ne_top_ae α β hne] with y hy
    exact ⟨ne_of_gt (heatPotential_pos _), hy⟩
  have hrow (z : FusedConfiguration α) :
      (∫⁻ y : FusedConfiguration β, K z y * w y) ≤
        integratedPotentialRowConstant * v z :=
    lintegral_integratedSwappingKernel_sourceWeight_le α β hne z
  have hcol (y : FusedConfiguration β) :
      (∫⁻ z : FusedConfiguration α, K z y * v z) ≤
        integratedPotentialRowConstant * w y := by
    have hsymm : ∀ z : FusedConfiguration α,
        K z y = integratedSwappingKernel β α y z := by
      intro z
      change integratedSwappingKernel α β z y = integratedSwappingKernel β α y z
      unfold integratedSwappingKernel
      apply lintegral_congr
      intro t
      exact congrArg ENNReal.ofReal (swappingKernel_symm α β t z y)
    have hrow' := lintegral_integratedSwappingKernel_sourceWeight_le β α hne.symm y
    have hvEq (z : FusedConfiguration α) :
        v z = heatPotential ((collisionEmbedding α z) β.1.1 -
          (collisionEmbedding α z) β.1.2) := by
      exact heatPotential_sub_swap _ _
    have hwEq : w y = heatPotential ((collisionEmbedding β y) α.1.2 -
        (collisionEmbedding β y) α.1.1) := by
      exact heatPotential_sub_swap _ _
    calc (∫⁻ z : FusedConfiguration α, K z y * v z)
        = ∫⁻ z : FusedConfiguration α,
            integratedSwappingKernel β α y z *
              heatPotential ((collisionEmbedding α z) β.1.1 -
                (collisionEmbedding α z) β.1.2) := by
              apply lintegral_congr
              intro z
              rw [hsymm z]
              rw [hvEq]
      _ ≤ integratedPotentialRowConstant *
            heatPotential ((collisionEmbedding β y) α.1.2 -
              (collisionEmbedding β y) α.1.1) := hrow'
      _ = integratedPotentialRowConstant * w y := by rw [hwEq]
  have hschur := lintegral_kernel_sq_le_weighted_schur volume volume hK hv hw hwfinite
    integratedPotentialRowConstant_ne_top integratedPotentialRowConstant_ne_top hrow hcol hf
  simpa only [pow_two] using hschur

end Critical2DKPZ.DeltaBose
