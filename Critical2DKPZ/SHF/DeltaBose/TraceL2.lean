/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.IncomingMass
public import Critical2DKPZ.SHF.DeltaBose.BlockL2
import Mathlib.Tactic

/-!
# Incoming, adjoint-incoming, and fixed-time swapping L² bounds

The squared incoming norm is bounded by `(4πt)⁻¹`; the squared swapping
norm is bounded by `(4πt)⁻²`. The latter is a fixed-time estimate only.
Its time integral diverges and does not supply the distinct-pair integrated
estimate needed for the diagram series.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Uniform fused mass of the incoming kernel. -/
theorem lintegral_incomingKernel_fused_le {n : ℕ} (α : CollisionPair n) {t : ℝ}
    (ht : 0 < t) (x : Configuration n) :
    (∫⁻ z : FusedConfiguration α, ENNReal.ofReal (incomingKernel α t z x)) ≤
      ENNReal.ofReal (4 * Real.pi * t)⁻¹ := by
  rw [lintegral_incomingKernel_fused α ht]
  apply ENNReal.ofReal_le_ofReal
  have he : 2 * Real.pi * (2 * t) = 4 * Real.pi * t := by ring
  simpa only [he] using heatKernel_le_at_zero (by positivity : 0 ≤ 2 * t)
    (x α.1.2 - x α.1.1)

/-- Incoming trace bound from the full configuration space to the fused space. -/
theorem incomingKernel_l2_sq_le {n : ℕ} (α : CollisionPair n) {t : ℝ}
    (ht : 0 < t) {f : Configuration n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : FusedConfiguration α,
      (∫⁻ x : Configuration n, ENNReal.ofReal (incomingKernel α t z x) * f x) ^ 2) ≤
      ENNReal.ofReal (4 * Real.pi * t)⁻¹ * ∫⁻ x : Configuration n, f x ^ 2 := by
  have hK : Measurable (fun p : FusedConfiguration α × Configuration n =>
      ENNReal.ofReal (incomingKernel α t p.1 p.2)) :=
    ((measurable_incomingKernel α).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hrow (z : FusedConfiguration α) :
      (∫⁻ x : Configuration n, ENNReal.ofReal (incomingKernel α t z x)) ≤ 1 := by
    rw [lintegral_incomingKernel_full α ht]
  simpa only [one_mul] using lintegral_kernel_sq_le volume volume hK hrow
    (lintegral_incomingKernel_fused_le α ht) hf

/-- The adjoint incoming kernel has the same squared L² bound. -/
theorem incomingKernel_adjoint_l2_sq_le {n : ℕ} (α : CollisionPair n) {t : ℝ}
    (ht : 0 < t) {f : FusedConfiguration α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : Configuration n,
      (∫⁻ z : FusedConfiguration α, ENNReal.ofReal (incomingKernel α t z x) * f z) ^ 2) ≤
      ENNReal.ofReal (4 * Real.pi * t)⁻¹ * ∫⁻ z : FusedConfiguration α, f z ^ 2 := by
  have hp : Measurable (fun p : Configuration n × FusedConfiguration α => (t, p.2, p.1)) :=
    measurable_const.prodMk (measurable_snd.prodMk measurable_fst)
  have hK := ((measurable_incomingKernel α).comp hp).ennreal_ofReal
  have hcol (z : FusedConfiguration α) :
      (∫⁻ x : Configuration n, ENNReal.ofReal (incomingKernel α t z x)) ≤ 1 := by
    rw [lintegral_incomingKernel_full α ht]
  simpa only [mul_one] using lintegral_kernel_sq_le volume volume hK
    (lintegral_incomingKernel_fused_le α ht) hcol hf

/-- Swapping at a fixed positive time has norm at most `(4πt)⁻¹`. -/
theorem swappingKernel_l2_sq_le {n : ℕ} (α β : CollisionPair n) {t : ℝ}
    (ht : 0 < t) {f : FusedConfiguration β → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : FusedConfiguration α,
      (∫⁻ w : FusedConfiguration β, ENNReal.ofReal (swappingKernel α β t z w) * f w) ^ 2) ≤
      ENNReal.ofReal (4 * Real.pi * t)⁻¹ ^ 2 * ∫⁻ w : FusedConfiguration β, f w ^ 2 := by
  have hK : Measurable (fun p : FusedConfiguration α × FusedConfiguration β =>
      ENNReal.ofReal (swappingKernel α β t p.1 p.2)) :=
    ((measurable_swappingKernel α β).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hrow (z : FusedConfiguration α) :
      (∫⁻ w : FusedConfiguration β, ENNReal.ofReal (swappingKernel α β t z w)) ≤
        ENNReal.ofReal (4 * Real.pi * t)⁻¹ := by
    change (∫⁻ w : FusedConfiguration β,
      ENNReal.ofReal (incomingKernel β t w (collisionEmbedding α z))) ≤ _
    exact lintegral_incomingKernel_fused_le β ht (collisionEmbedding α z)
  have hcol (w : FusedConfiguration β) :
      (∫⁻ z : FusedConfiguration α, ENNReal.ofReal (swappingKernel α β t z w)) ≤
        ENNReal.ofReal (4 * Real.pi * t)⁻¹ := by
    have he : (fun z : FusedConfiguration α => swappingKernel α β t z w) =
        (fun z : FusedConfiguration α => incomingKernel α t z (collisionEmbedding β w)) := by
      funext z
      exact freeKernel_symm n t _ _
    simp_rw [congrFun he]
    exact lintegral_incomingKernel_fused_le α ht (collisionEmbedding β w)
  simpa only [pow_two] using lintegral_kernel_sq_le volume volume hK hrow hcol hf

end Critical2DKPZ.DeltaBose
