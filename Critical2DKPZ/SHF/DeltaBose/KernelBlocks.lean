/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Analysis.Heat.Basic
public import Critical2DKPZ.SHF.DeltaBose.CollisionWords
public import Critical2DKPZ.SHF.DeltaBose.ScalarDensity
import Mathlib.Tactic

/-! The free and fused kernels in Tsai’s equations (2.1)–(2.5) use product Lebesgue measure, a collision coefficient of `4π` and center heat time `t/2`. -/

@[expose] public section

open MeasureTheory

namespace Critical2DKPZ.DeltaBose

/-- An `n`-particle configuration consists of points in the Euclidean plane. -/
abbrev Configuration (n : ℕ) := Fin n → Plane

/-- A label unaffected by a specified collision. -/
abbrev Spectator {n : ℕ} (α : CollisionPair n) :=
  {i : Fin n // i ≠ α.1.1 ∧ i ≠ α.1.2}

/-- Free coordinates on the collision space: a center and the spectators. -/
abbrev FusedConfiguration {n : ℕ} (α : CollisionPair n) := Plane × (Spectator α → Plane)

/-- Embed the collision space by duplicating its center at the two colliding labels. -/
def collisionEmbedding {n : ℕ} (α : CollisionPair n) (y : FusedConfiguration α) :
    Configuration n := fun i =>
  if h : i = α.1.1 ∨ i = α.1.2 then y.1 else y.2 ⟨i, not_or.mp h⟩

/-- The collision embedding is measurable in the free collision coordinates. -/
theorem measurable_collisionEmbedding {n : ℕ} (α : CollisionPair n) :
    Measurable (collisionEmbedding α) := by
  apply Measurable.of_eval
  intro i
  unfold collisionEmbedding
  split_ifs
  · exact measurable_fst
  · exact (measurable_pi_apply _).comp measurable_snd


/-- The planar heat kernel is invariant under reflection. -/
theorem heatKernel_neg (t : ℝ) (z : Plane) : heatKernel t (-z) = heatKernel t z := by
  simp only [heatKernel, norm_neg]

/-- Orthogonal invariance, including reflections. -/
theorem heatKernel_linearIsometry (O : Plane ≃ₗᵢ[ℝ] Plane) (t : ℝ) (z : Plane) :
    heatKernel t (O z) = heatKernel t z := by
  simp only [heatKernel, O.norm_map]

/-- Joint continuity in space and positive time. -/
theorem continuousOn_heatKernel :
    ContinuousOn (fun p : ℝ × Plane => heatKernel p.1 p.2) {p | 0 < p.1} := by
  unfold heatKernel
  apply ContinuousOn.mul
  · apply ContinuousOn.inv₀
    · fun_prop
    · intro p hp
      exact (mul_pos (mul_pos (by norm_num) Real.pi_pos) hp).ne'
  · apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro p hp
      exact (mul_pos (by norm_num) hp).ne'

/-- The free `n`-particle kernel. -/
noncomputable def freeKernel (n : ℕ) (t : ℝ) (x y : Configuration n) : ℝ :=
  ∏ i, heatKernel t (y i - x i)

/-- Incoming kernel on the free coordinates of a collision. -/
noncomputable def incomingKernel {n : ℕ} (α : CollisionPair n) (t : ℝ)
    (y : FusedConfiguration α) (x : Configuration n) : ℝ :=
  freeKernel n t x (collisionEmbedding α y)

/-- Swapping kernel between two specified collision spaces. -/
noncomputable def swappingKernel {n : ℕ} (α β : CollisionPair n) (t : ℝ)
    (y : FusedConfiguration α) (z : FusedConfiguration β) : ℝ :=
  freeKernel n t (collisionEmbedding α y) (collisionEmbedding β z)

/-- The resummed repeated-collision kernel is `4π j_θ(t)` times the center heat kernel at time `t/2` and the spectator heat kernels at time `t`. -/
noncomputable def collisionKernel {n : ℕ} (α : CollisionPair n) (θ t : ℝ)
    (y z : FusedConfiguration α) : ℝ :=
  4 * Real.pi * scalarDensity θ t * heatKernel (t / 2) (z.1 - y.1) *
    ∏ i : Spectator α, heatKernel t (z.2 i - y.2 i)

/-- Positivity of the free kernel at positive time. -/
theorem freeKernel_pos (n : ℕ) {t : ℝ} (ht : 0 < t) (x y : Configuration n) :
    0 < freeKernel n t x y :=
  Finset.prod_pos fun _ _ => Critical2DKPZ.heatKernel_pos ht _

/-- Positivity of incoming and swapping kernels needs no distinct-pair assumption. -/
theorem incomingKernel_pos {n : ℕ} (α : CollisionPair n) {t : ℝ} (ht : 0 < t)
    (y : FusedConfiguration α) (x : Configuration n) : 0 < incomingKernel α t y x :=
  freeKernel_pos n ht _ _


/-- Positivity of the collision block. -/
theorem collisionKernel_pos {n : ℕ} (α : CollisionPair n) (θ : ℝ) {t : ℝ} (ht : 0 < t)
    (y z : FusedConfiguration α) : 0 < collisionKernel α θ t y z := by
  unfold collisionKernel
  exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (scalarDensity_pos θ ht)) (Critical2DKPZ.heatKernel_pos (by linarith) _))
    (Finset.prod_pos fun _ _ => Critical2DKPZ.heatKernel_pos ht _)

/-- The free kernel is symmetric in its endpoints. -/
theorem freeKernel_symm (n : ℕ) (t : ℝ) (x y : Configuration n) :
    freeKernel n t x y = freeKernel n t y x := by
  apply Finset.prod_congr rfl
  intro i _
  rw [← neg_sub (y i) (x i), heatKernel_neg]

/-- Swapping the collision spaces transposes the swapping kernel. -/
theorem swappingKernel_symm {n : ℕ} (α β : CollisionPair n) (t : ℝ)
    (y : FusedConfiguration α) (z : FusedConfiguration β) :
    swappingKernel α β t y z = swappingKernel β α t z y :=
  freeKernel_symm n t _ _

/-- The collision kernel is symmetric in its fused endpoints. -/
theorem collisionKernel_symm {n : ℕ} (α : CollisionPair n) (θ t : ℝ)
    (y z : FusedConfiguration α) : collisionKernel α θ t y z = collisionKernel α θ t z y := by
  unfold collisionKernel
  rw [← neg_sub z.1 y.1, heatKernel_neg]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← neg_sub (z.2 i) (y.2 i), heatKernel_neg]



/-- At one particle the first-moment kernel is the planar heat kernel. -/
theorem freeKernel_one (t : ℝ) (x y : Configuration 1) :
    freeKernel 1 t x y = heatKernel t (y 0 - x 0) := Fin.prod_univ_one _

end Critical2DKPZ.DeltaBose
