/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.FreeMass
public import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.Tactic

/-! # Exact mass identities for incoming and repeated-collision blocks -/

public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Integrating the full endpoint of an incoming kernel gives one. -/
theorem integral_incomingKernel_full {n : ℕ} (α : CollisionPair n) {t : ℝ} (ht : 0 < t)
    (z : FusedConfiguration α) : (∫ x : Configuration n, incomingKernel α t z x) = 1 :=
  integral_freeKernel_left n ht (collisionEmbedding α z)

/-- An incoming kernel is absolutely integrable in its full endpoint. -/
theorem integrable_incomingKernel_full {n : ℕ} (α : CollisionPair n) {t : ℝ} (ht : 0 < t)
    (z : FusedConfiguration α) : Integrable (incomingKernel α t z) :=
  integrable_freeKernel_left n ht (collisionEmbedding α z)

/-- Integrability of the repeated-collision block in its outgoing free coordinates. -/
theorem integrable_collisionKernel_right {n : ℕ} (α : CollisionPair n) (θ : ℝ) {t : ℝ}
    (ht : 0 < t) (z : FusedConfiguration α) : Integrable (collisionKernel α θ t z) := by
  have hc := (integrable_heatKernel (by linarith : 0 < t / 2)).comp_sub_right z.1
  have hs : Integrable (fun w : Spectator α → Plane => ∏ i, heatKernel t (w i - z.2 i)) :=
    Integrable.fintype_prod fun i => (integrable_heatKernel ht).comp_sub_right (z.2 i)
  exact ((hc.mul_prod hs).const_mul (4 * Real.pi * scalarDensity θ t)).congr
    (Filter.Eventually.of_forall fun w => by unfold collisionKernel; ring)

/-- A repeated collision has exact mass `4π j_θ(t)` in its collision space. -/
theorem integral_collisionKernel_right {n : ℕ} (α : CollisionPair n) (θ : ℝ) {t : ℝ}
    (ht : 0 < t) (z : FusedConfiguration α) :
    (∫ w : FusedConfiguration α, collisionKernel α θ t z w) = 4 * Real.pi * scalarDensity θ t := by
  calc (∫ w : FusedConfiguration α, collisionKernel α θ t z w)
      = (4 * Real.pi * scalarDensity θ t) *
          ∫ w : FusedConfiguration α, heatKernel (t / 2) (w.1 - z.1) *
            ∏ i, heatKernel t (w.2 i - z.2 i) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with w
        unfold collisionKernel
        ring
    _ = (4 * Real.pi * scalarDensity θ t) *
        ((∫ w : Plane, heatKernel (t / 2) (w - z.1)) *
          ∫ w : Spectator α → Plane, ∏ i, heatKernel t (w i - z.2 i)) := by
        congr 1
        exact integral_prod_mul (μ := volume) (ν := volume)
          (fun w : Plane => heatKernel (t / 2) (w - z.1))
          (fun w : Spectator α → Plane => ∏ i, heatKernel t (w i - z.2 i))
    _ = 4 * Real.pi * scalarDensity θ t := by
      rw [integral_heatKernel_sub (by linarith : 0 < t / 2),
        integral_fintype_prod_volume_eq_prod (fun (i : Spectator α) (w : Plane) => heatKernel t (w - z.2 i))]
      simp only [integral_heatKernel_sub ht, Finset.prod_const_one, mul_one]

/-- The nonnegative mass identity, in the form used in Tonelli and Schur estimates. -/
theorem lintegral_collisionKernel_right {n : ℕ} (α : CollisionPair n) (θ : ℝ) {t : ℝ}
    (ht : 0 < t) (z : FusedConfiguration α) :
    (∫⁻ w : FusedConfiguration α, ENNReal.ofReal (collisionKernel α θ t z w)) =
      ENNReal.ofReal (4 * Real.pi * scalarDensity θ t) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_collisionKernel_right α θ ht z)
    (Filter.Eventually.of_forall fun w => (collisionKernel_pos α θ ht z w).le),
    integral_collisionKernel_right α θ ht z]

/-- The nonnegative incoming mass identity. -/
theorem lintegral_incomingKernel_full {n : ℕ} (α : CollisionPair n) {t : ℝ} (ht : 0 < t)
    (z : FusedConfiguration α) :
    (∫⁻ x : Configuration n, ENNReal.ofReal (incomingKernel α t z x)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_incomingKernel_full α ht z)
    (Filter.Eventually.of_forall fun x => (incomingKernel_pos α ht z x).le),
    integral_incomingKernel_full α ht z, ENNReal.ofReal_one]

end Critical2DKPZ.DeltaBose
