/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.BlockTransport
public import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-! # Translation and orthogonal invariance of the complete positive diagram series -/

public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Applying a planar volume-preserving equivalence to all fused coordinates preserves volume. -/
theorem lintegral_mapFused {n : ℕ} (α : CollisionPair n) (f : Plane ≃ᵐ Plane)
    (hf : MeasurePreserving f) (F : FusedConfiguration α → ℝ≥0∞) :
    (∫⁻ z : FusedConfiguration α, F (mapFused f z)) = ∫⁻ z : FusedConfiguration α, F z := by
  let e : FusedConfiguration α ≃ᵐ FusedConfiguration α :=
    f.prodCongr (MeasurableEquiv.piCongrRight fun _ : Spectator α => f)
  have hp : MeasurePreserving e := hf.prod (volume_preserving_pi fun _ : Spectator α => hf)
  exact hp.lintegral_comp_emb e.measurableEmbedding F

/-- Heat-preserving spatial equivalences preserve free particle strands. -/
theorem freeKernel_covariant (n : ℕ) (f : Plane ≃ᵐ Plane)
    (hheat : ∀ t : ℝ, ∀ z w : Plane, heatKernel t (f z - f w) = heatKernel t (z - w))
    (t : ℝ) (x y : Configuration n) :
    freeKernel n t (fun i => f (x i)) (fun i => f (y i)) = freeKernel n t x y := by
  unfold freeKernel
  exact Finset.prod_congr rfl fun i _ => hheat t (y i) (x i)

/-- Heat-preserving spatial equivalences preserve incoming kernels. -/
theorem incomingKernel_covariant {n : ℕ} (α : CollisionPair n) (f : Plane ≃ᵐ Plane)
    (hheat : ∀ t : ℝ, ∀ z w : Plane, heatKernel t (f z - f w) = heatKernel t (z - w))
    (t : ℝ) (z : FusedConfiguration α) (x : Configuration n) :
    incomingKernel α t (mapFused f z) (fun i => f (x i)) = incomingKernel α t z x := by
  unfold incomingKernel
  rw [collisionEmbedding_map]
  exact freeKernel_covariant n f hheat t _ _

/-- Heat-preserving spatial equivalences preserve repeated-collision kernels. -/
theorem collisionKernel_covariant {n : ℕ} (α : CollisionPair n) (f : Plane ≃ᵐ Plane)
    (hheat : ∀ t : ℝ, ∀ z w : Plane, heatKernel t (f z - f w) = heatKernel t (z - w))
    (θ t : ℝ) (z w : FusedConfiguration α) :
    collisionKernel α θ t (mapFused f z) (mapFused f w) = collisionKernel α θ t z w := by
  unfold collisionKernel mapFused
  simp only [hheat]

/-- Volume-preserving heat symmetries commute with every individual diagram. -/
theorem diagramKernel_covariant {n : ℕ} (f : Plane ≃ᵐ Plane) (hf : MeasurePreserving f)
    (hheat : ∀ t : ℝ, ∀ z w : Plane, heatKernel t (f z - f w) = heatKernel t (z - w))
    (θ : ℝ) (w : List (CollisionPair n)) (h : ℝ) (x y : Configuration n) :
    diagramKernel θ w h (fun i => f (x i)) (fun i => f (y i)) = diagramKernel θ w h x y := by
  induction w generalizing h x y with
  | nil => simp only [diagramKernel, freeKernel_covariant n f hheat]
  | cons α w ih =>
    simp only [diagramKernel]
    apply lintegral_congr
    intro r
    apply lintegral_congr
    intro u
    rw [← lintegral_mapFused α f hf]
    apply lintegral_congr
    intro z
    rw [← lintegral_mapFused α f hf]
    apply lintegral_congr
    intro z'
    rw [incomingKernel_covariant α f hheat, collisionKernel_covariant α f hheat,
      collisionEmbedding_map, ih]

/-- Volume-preserving heat symmetries commute with the full moment-kernel series. -/
theorem momentKernel_covariant (n : ℕ) (f : Plane ≃ᵐ Plane) (hf : MeasurePreserving f)
    (hheat : ∀ t : ℝ, ∀ z w : Plane, heatKernel t (f z - f w) = heatKernel t (z - w))
    (θ h : ℝ) (x y : Configuration n) :
    momentKernel n θ h (fun i => f (x i)) (fun i => f (y i)) = momentKernel n θ h x y := by
  unfold momentKernel
  rw [freeKernel_covariant n f hheat]
  congr 1
  apply tsum_congr
  intro m
  exact Finset.sum_congr rfl fun w _ => diagramKernel_covariant f hf hheat θ _ h x y

/-- Translation invariance of the full moment kernels. -/
theorem momentKernel_translate (n : ℕ) (θ h : ℝ) (x y : Configuration n) (a : Plane) :
    momentKernel n θ h (fun i => x i + a) (fun i => y i + a) = momentKernel n θ h x y := by
  apply momentKernel_covariant n (MeasurableEquiv.addRight a) (measurePreserving_add_right volume a)
  intro t z w
  change heatKernel t ((z + a) - (w + a)) = heatKernel t (z - w)
  rw [add_sub_add_right_eq_sub]

/-- Orthogonal invariance, including reflections, of the full moment kernels. -/
theorem momentKernel_linearIsometry (n : ℕ) (O : Plane ≃ₗᵢ[ℝ] Plane) (θ h : ℝ)
    (x y : Configuration n) :
    momentKernel n θ h (fun i => O (x i)) (fun i => O (y i)) = momentKernel n θ h x y := by
  apply momentKernel_covariant n O.toHomeomorph.toMeasurableEquiv O.measurePreserving
  intro t z w
  change heatKernel t (O z - O w) = heatKernel t (z - w)
  rw [← O.map_sub, heatKernel_linearIsometry]

end Critical2DKPZ.DeltaBose
