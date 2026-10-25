/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.BlockL2
public import Critical2DKPZ.SHF.DeltaBose.ScalarLaplace
import Mathlib.Tactic

/-! # The damped collision resolvent

Above the critical Laplace rate, the repeated-collision kernel integrated against `exp(-rate*t)` has mass and an L² norm bound equal to `4π / (log rate - θ)`. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The time-integrated, exponentially damped repeated-collision kernel. -/
noncomputable def collisionResolvent {n : ℕ} (α : CollisionPair n) (θ rate : ℝ)
    (z w : FusedConfiguration α) : ℝ≥0∞ :=
  ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-(rate * t))) *
    ENNReal.ofReal (collisionKernel α θ t z w)

/-- Joint measurability of the collision resolvent. -/
theorem measurable_collisionResolvent {n : ℕ} (α : CollisionPair n) (θ rate : ℝ) :
    Measurable (Function.uncurry (collisionResolvent α θ rate)) := by
  have hp : Measurable (fun p : (FusedConfiguration α × FusedConfiguration α) × ℝ =>
      ((θ, p.2), p.1)) := (measurable_const.prodMk measurable_snd).prodMk measurable_fst
  have hK := ((measurable_collisionKernel α).comp hp).ennreal_ofReal
  have he : Measurable (fun p : (FusedConfiguration α × FusedConfiguration α) × ℝ =>
      ENNReal.ofReal (Real.exp (-(rate * p.2)))) := by fun_prop
  exact (he.mul hK).lintegral_prod_right' (ν := volume.restrict (Ioi 0))

/-- The collision resolvent is symmetric in its fused endpoints. -/
theorem collisionResolvent_symm {n : ℕ} (α : CollisionPair n) (θ rate : ℝ)
    (z w : FusedConfiguration α) :
    collisionResolvent α θ rate z w = collisionResolvent α θ rate w z := by
  unfold collisionResolvent
  simp_rw [collisionKernel_symm α θ]

/-- Exact mass of the damped collision resolvent above its critical rate. -/
theorem lintegral_collisionResolvent_right {n : ℕ} (α : CollisionPair n) {θ rate : ℝ}
    (hrate : 0 < rate) (hθ : θ < Real.log rate) (z : FusedConfiguration α) :
    (∫⁻ w : FusedConfiguration α, collisionResolvent α θ rate z w) =
      ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹) := by
  have hp : Measurable (fun p : FusedConfiguration α × ℝ => ((θ, p.2), z, p.1)) :=
    (measurable_const.prodMk measurable_snd).prodMk (measurable_const.prodMk measurable_fst)
  have hK := ((measurable_collisionKernel α).comp hp).ennreal_ofReal
  have he : Measurable (fun p : FusedConfiguration α × ℝ =>
      ENNReal.ofReal (Real.exp (-(rate * p.2)))) := by fun_prop
  unfold collisionResolvent
  rw [lintegral_lintegral_swap (he.mul hK).aemeasurable]
  have hmass : (∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-(rate * t))) *
      ENNReal.ofReal (4 * Real.pi * scalarDensity θ t)) =
      ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹) := by
    have hi := (integrable_scalarDensity_laplace hrate hθ).const_mul (4 * Real.pi)
    have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
        (fun t => (4 * Real.pi) * (Real.exp (-(rate * t)) * scalarDensity θ t)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (by positivity) (mul_nonneg (Real.exp_pos _).le (scalarDensity_pos θ ht).le)
    calc (∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-(rate * t))) *
        ENNReal.ofReal (4 * Real.pi * scalarDensity θ t))
        = ∫⁻ t in Ioi 0, ENNReal.ofReal ((4 * Real.pi) *
            (Real.exp (-(rate * t)) * scalarDensity θ t)) := by
          apply lintegral_congr
          intro t
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          ring
      _ = ENNReal.ofReal (∫ t in Ioi 0, (4 * Real.pi) *
          (Real.exp (-(rate * t)) * scalarDensity θ t)) :=
        (ofReal_integral_eq_lintegral_ofReal hi hn).symm
      _ = ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹) := by
        rw [integral_const_mul, integral_scalarDensity_laplace hrate hθ]
  rw [← hmass]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_collisionKernel_right α θ ht]

/-- The damped collision resolvent has the exact scalar-resolvent Schur bound. -/
theorem collisionResolvent_l2_sq_le {n : ℕ} (α : CollisionPair n) {θ rate : ℝ}
    (hrate : 0 < rate) (hθ : θ < Real.log rate)
    {f : FusedConfiguration α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : FusedConfiguration α,
      (∫⁻ w : FusedConfiguration α, collisionResolvent α θ rate z w * f w) ^ 2) ≤
      ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹) ^ 2 *
        ∫⁻ w : FusedConfiguration α, f w ^ 2 := by
  have hrow (z : FusedConfiguration α) :
      (∫⁻ w : FusedConfiguration α, collisionResolvent α θ rate z w) ≤
        ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹) :=
    (lintegral_collisionResolvent_right α hrate hθ z).le
  have hcol (w : FusedConfiguration α) :
      (∫⁻ z : FusedConfiguration α, collisionResolvent α θ rate z w) ≤
        ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹) := by
    simp_rw [collisionResolvent_symm α θ rate]
    exact hrow w
  simpa only [pow_two] using lintegral_kernel_sq_le volume volume
    (measurable_collisionResolvent α θ rate) hrow hcol hf

end Critical2DKPZ.DeltaBose
