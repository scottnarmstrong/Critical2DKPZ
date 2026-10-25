/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitRieszPotential
import Critical2DKPZ.SHF.DeltaBose.PotentialFusedRows
import Mathlib.Tactic

/-! # Integrable Gaussian inverse-gap envelopes on collision spaces -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose
namespace Critical2DKPZ.SHF.Moments

/-- An incoming Gaussian density times the inverse gap of a distinct pair is integrable. -/
theorem integrable_incomingKernel_mul_inverse_gap {h : ℕ}
    (α β : CollisionPair h) (hne : α ≠ β) {t : ℝ} (ht : 0 < t) :
    Integrable (fun v : FusedConfiguration α => incomingKernel α t v 0 *
      ‖collisionEmbedding α v β.1.2 - collisionEmbedding α v β.1.1‖⁻¹) := by
  classical
  let g : FusedConfiguration α → Plane := fun v =>
    collisionEmbedding α v β.1.2 - collisionEmbedding α v β.1.1
  have hmcoord (i : Fin h) : Measurable (fun v : FusedConfiguration α => collisionEmbedding α v i) := by
    unfold collisionEmbedding
    split_ifs <;> fun_prop
  have hg : Measurable g := (hmcoord β.1.2).sub (hmcoord β.1.1)
  have hk : Measurable (fun v : FusedConfiguration α => incomingKernel α t v 0) := by
    unfold incomingKernel freeKernel
    apply Finset.measurable_fun_prod
    intro i _hi
    unfold heatKernel
    have hi := hmcoord i
    fun_prop
  have hm := hk.mul hg.norm.inv
  have hnonneg (v : FusedConfiguration α) :
      0 ≤ incomingKernel α t v 0 * ‖g v‖⁻¹ :=
    mul_nonneg (incomingKernel_pos α ht _ _).le (inv_nonneg.mpr (norm_nonneg _))
  obtain ⟨C, hC, hbound⟩ := exists_ofReal_inv_norm_le_heatPotential
  have he (v : FusedConfiguration α) : swappingKernel β α t (0 : FusedConfiguration β) v =
      incomingKernel α t v 0 := by
    unfold swappingKernel incomingKernel
    congr 1
    funext i
    unfold collisionEmbedding
    split_ifs <;> rfl
  have hr := lintegral_swappingPotential_row_le β α hne.symm ht (0 : FusedConfiguration β)
  have hgap (v : FusedConfiguration α) :
      heatPotential (g v) = heatPotential (collisionEmbedding α v β.1.1 -
        collisionEmbedding α v β.1.2) := by
    rw [← heatPotential_neg]
    congr 1
    dsimp [g]
    abel
  have hfin : (∫⁻ v : FusedConfiguration α,
      ENNReal.ofReal (incomingKernel α t v 0 * ‖g v‖⁻¹)) < ⊤ := by
    calc
      _ ≤ ENNReal.ofReal C * (∫⁻ v : FusedConfiguration α,
          ENNReal.ofReal (swappingKernel β α t (0 : FusedConfiguration β) v) *
            heatPotential (collisionEmbedding α v β.1.1 - collisionEmbedding α v β.1.2)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_mono
        intro v
        dsimp only
        rw [ENNReal.ofReal_mul (incomingKernel_pos α ht _ _).le, he]
        have hb := mul_le_mul_left (hbound (g v)) (ENNReal.ofReal (incomingKernel α t v 0))
        rw [hgap] at hb
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
      _ ≤ ENNReal.ofReal C * (heatPotentialRowBound t * ENNReal.ofReal
          (heatKernel (2 * t) (collisionEmbedding β (0 : FusedConfiguration β) α.1.2 -
            collisionEmbedding β (0 : FusedConfiguration β) α.1.1))) := mul_le_mul_right hr _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (heatPotentialRowBound_ne_top t))
          ENNReal.ofReal_lt_top)
  exact ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall hnonneg)).mpr hfin⟩

/-- The product Gaussian envelope is integrable after multiplication by a next-pair inverse-gap factor. -/
theorem integrable_incomingKernel_pair_mul_one_add_inverse_gap {h : ℕ}
    (α β : CollisionPair h) (hne : α ≠ β) {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : FusedConfiguration α × FusedConfiguration α =>
      incomingKernel α t p.1 0 * incomingKernel α t p.2 0 *
        (1 + ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖⁻¹)) := by
  have hi := integrable_incomingKernel_fused α ht (0 : Configuration h)
  have hw := integrable_incomingKernel_mul_inverse_gap α β hne ht
  have hsum := hi.add hw
  have hp := hi.mul_prod hsum
  apply hp.congr
  exact Eventually.of_forall fun p => by
    simp only [Pi.add_apply]
    ring

end Critical2DKPZ.SHF.Moments
