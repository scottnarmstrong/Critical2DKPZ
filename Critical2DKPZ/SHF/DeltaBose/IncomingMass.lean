/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.CollisionMass
import Mathlib.Tactic

/-! # The exact mass of the incoming trace kernel in fused coordinates -/

public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Split a product into the two colliding labels and the spectators. -/
@[to_additive /-- Split a sum into the colliding labels and spectators. -/]
theorem prod_collision_labels {n : ℕ} (α : CollisionPair n) {M : Type*} [CommMonoid M]
    (f : Fin n → M) :
    (∏ i, f i) = f α.1.1 * f α.1.2 * ∏ i : Spectator α, f i.1 := by
  classical
  have ha : α.1.2 ≠ α.1.1 := ne_of_gt α.2
  have hs : (∏ i ∈ (Finset.univ.erase α.1.1).erase α.1.2, f i) =
      ∏ i : Spectator α, f i.1 := by
    apply Finset.prod_subtype
    intro i
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact and_comm
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ α.1.1),
    ← Finset.mul_prod_erase (Finset.univ.erase α.1.1) f
      (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩), hs, mul_assoc]

/-- The incoming trace separates into a two-strand center and independent spectators. -/
theorem incomingKernel_eq_prod {n : ℕ} (α : CollisionPair n) (t : ℝ)
    (z : FusedConfiguration α) (x : Configuration n) :
    incomingKernel α t z x =
      (heatKernel t (z.1 - x α.1.1) * heatKernel t (z.1 - x α.1.2)) *
        ∏ i : Spectator α, heatKernel t (z.2 i - x i.1) := by
  classical
  unfold incomingKernel freeKernel
  rw [prod_collision_labels α]
  simp only [collisionEmbedding, true_or, dite_true, or_true]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [i.2.1, i.2.2, or_self, dite_false]

/-- The center part of the incoming kernel is integrable. -/
theorem integrable_heatKernel_mul_sameTime {t : ℝ} (ht : 0 < t) (a b : Plane) :
    Integrable (fun z : Plane => heatKernel t (z - a) * heatKernel t (z - b)) := by
  apply ((integrable_heatKernel ht).comp_sub_right a).mul_bdd
    ((continuous_heatKernel t).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  filter_upwards [] with z
  change ‖heatKernel t (z - b)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (Critical2DKPZ.heatKernel_pos ht _)]
  exact heatKernel_le_at_zero ht.le _

/-- Two equal-time heat strands integrate to the heat kernel at twice the time. -/
theorem integral_heatKernel_mul_sameTime {t : ℝ} (ht : 0 < t) (a b : Plane) :
    (∫ z : Plane, heatKernel t (z - a) * heatKernel t (z - b)) =
      heatKernel (2 * t) (b - a) := by
  have he : (fun z : Plane => heatKernel t (z - a) * heatKernel t (z - b)) =
      (fun z : Plane => heatKernel t z * heatKernel t ((b - a) - z)) ∘
        (fun z : Plane => z - a) := by
    funext z
    dsimp only [Function.comp_apply]
    rw [sub_sub_sub_cancel_right, ← neg_sub (z) b, heatKernel_neg]
  rw [he]
  simp only [Function.comp_def]
  simpa only [two_mul] using (integral_sub_right_eq_self
    (fun z : Plane => heatKernel t z * heatKernel t ((b - a) - z)) a).trans
    (integral_heatKernel_mul_sub ht ht (b - a))

/-- The incoming kernel is integrable in the free coordinates of its collision space. -/
theorem integrable_incomingKernel_fused {n : ℕ} (α : CollisionPair n) {t : ℝ} (ht : 0 < t)
    (x : Configuration n) : Integrable (fun z : FusedConfiguration α => incomingKernel α t z x) := by
  simp_rw [incomingKernel_eq_prod]
  exact (integrable_heatKernel_mul_sameTime ht _ _).mul_prod
    (Integrable.fintype_prod fun i : Spectator α =>
      (integrable_heatKernel ht).comp_sub_right (x i.1))

/-- Exact fused mass, including the pair-separation Gaussian. -/
theorem integral_incomingKernel_fused {n : ℕ} (α : CollisionPair n) {t : ℝ} (ht : 0 < t)
    (x : Configuration n) :
    (∫ z : FusedConfiguration α, incomingKernel α t z x) =
      heatKernel (2 * t) (x α.1.2 - x α.1.1) := by
  simp_rw [incomingKernel_eq_prod]
  have he := integral_prod_mul (μ := (volume : Measure Plane))
    (ν := (volume : Measure (Spectator α → Plane)))
    (fun z : Plane => heatKernel t (z - x α.1.1) * heatKernel t (z - x α.1.2))
    (fun z : Spectator α → Plane => ∏ i, heatKernel t (z i - x i.1))
  exact he.trans (by
    rw [integral_heatKernel_mul_sameTime ht,
      integral_fintype_prod_volume_eq_prod (fun (i : Spectator α) (z : Plane) =>
        heatKernel t (z - x i.1))]
    simp only [integral_heatKernel_sub ht, Finset.prod_const_one, mul_one])

/-- The same exact fused mass for the nonnegative incoming kernel. -/
theorem lintegral_incomingKernel_fused {n : ℕ} (α : CollisionPair n) {t : ℝ} (ht : 0 < t)
    (x : Configuration n) :
    (∫⁻ z : FusedConfiguration α, ENNReal.ofReal (incomingKernel α t z x)) =
      ENNReal.ofReal (heatKernel (2 * t) (x α.1.2 - x α.1.1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_incomingKernel_fused α ht x)
    (Filter.Eventually.of_forall fun z => (incomingKernel_pos α ht z x).le),
    integral_incomingKernel_fused α ht x]

end Critical2DKPZ.DeltaBose
