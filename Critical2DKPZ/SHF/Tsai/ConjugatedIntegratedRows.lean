/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedFractionalRows
public import Critical2DKPZ.SHF.Tsai.ConjugatedPotentialTime
public import Critical2DKPZ.SHF.DeltaBose.PotentialIntegratedSchur
import Mathlib.Tactic

/-! # Time-integrated swapping rows with fractional power weights -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Time-integrated swapping rows obey Schur bounds for every fractional
power of the canonical potential. All singular points remain in the statement. -/
theorem lintegral_integratedSwapping_fractionalPotential_row_le {n : ℕ}
    (α β : CollisionPair n) (hne : α ≠ β) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (z : FusedConfiguration α) :
    (∫⁻ w : FusedConfiguration β, integratedSwappingKernel α β z w *
      heatPotential ((collisionEmbedding β w) α.1.1 - (collisionEmbedding β w) α.1.2) ^ b) ≤
      fractionalPotentialRowConstant b *
        heatPotential ((collisionEmbedding α z) β.1.2 - (collisionEmbedding α z) β.1.1) ^ b := by
  let k : ℝ → FusedConfiguration β → ℝ≥0∞ := fun t w =>
    ENNReal.ofReal (swappingKernel α β t z w)
  let W : FusedConfiguration β → ℝ≥0∞ := fun w =>
    heatPotential ((collisionEmbedding β w) α.1.1 - (collisionEmbedding β w) α.1.2)
  have hk : Measurable (Function.uncurry k) :=
    ((measurable_swappingKernel α β).comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).ennreal_ofReal
  have hW : Measurable W := measurable_heatPotential.comp
    (((measurable_pi_apply α.1.1).comp (measurable_collisionEmbedding β)).sub
      ((measurable_pi_apply α.1.2).comp (measurable_collisionEmbedding β)))
  have hprod : Measurable (fun q : FusedConfiguration β × ℝ => k q.2 q.1 * W q.1 ^ b) :=
    (hk.comp measurable_swap).mul ((hW.comp measurable_fst).pow_const b)
  calc
    _ = ∫⁻ w : FusedConfiguration β, ∫⁻ t in Ioi 0, k t w * W w ^ b := by
      apply lintegral_congr
      intro w
      exact (lintegral_mul_const _
        (hk.comp (measurable_id.prodMk measurable_const))).symm
    _ = ∫⁻ t in Ioi 0, ∫⁻ w : FusedConfiguration β, k t w * W w ^ b :=
      lintegral_lintegral_swap hprod.aemeasurable
    _ ≤ ∫⁻ t in Ioi 0, heatPotentialRowBound t ^ b * ENNReal.ofReal (heatKernel (2 * t)
        ((collisionEmbedding α z) β.1.2 - (collisionEmbedding α z) β.1.1)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact lintegral_swapping_fractionalPotential_row_le α β hne hb hb1 ht z
    _ ≤ _ := lintegral_fractionalPotentialRowBound_heatKernel_le hb _

end Critical2DKPZ.SHF.Tsai

end
