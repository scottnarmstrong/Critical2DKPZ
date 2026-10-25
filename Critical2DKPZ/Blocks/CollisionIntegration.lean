/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.CollisionCellSums
import Mathlib.Tactic

/-! # Integration through finite spatial collision cells -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Blocks

private theorem spatialCell_eq_finite (β : ℝ) (n : ℕ) (W : Site → ℝ)
    (S : Finset Site) (hW : ∀ x, x ∉ S → W x = 0) (F : Site → ℝ) :
    (∑' x, ∑' y, W x * (Polymer.sigmaSq β *
      Collision.spatialRenewal (Polymer.sigmaSq β) n (y - x)) * F y) =
      ∑ x ∈ S, ∑ y ∈ Polymer.endpoints x n, W x * (Polymer.sigmaSq β *
        Collision.spatialRenewal (Polymer.sigmaSq β) n (y - x)) * F y := by
  rw [tsum_eq_sum (s := S)]
  · apply Finset.sum_congr rfl
    intro x _
    apply tsum_eq_sum
    intro y hy
    rw [spatialRenewal_sigmaSq_eq_zero_of_not_mem β n x y hy,
      mul_zero, mul_zero, zero_mul]
  · intro x hx
    simp only [hW x hx, zero_mul, tsum_zero]

private theorem spatialCell_integrable_integral (β : ℝ) (n : ℕ) (W : Site → ℝ)
    (S : Finset Site) (hW : ∀ x, x ∉ S → W x = 0) (F : Site → Disorder → ℝ)
    (hF : ∀ y, Integrable (F y) disorderLaw) :
    Integrable (fun ω => ∑' x, ∑' y, W x * (Polymer.sigmaSq β *
      Collision.spatialRenewal (Polymer.sigmaSq β) n (y - x)) * F y ω) disorderLaw ∧
    (∫ ω, (∑' x, ∑' y, W x * (Polymer.sigmaSq β *
      Collision.spatialRenewal (Polymer.sigmaSq β) n (y - x)) * F y ω) ∂disorderLaw) =
      ∑' x, ∑' y, W x * (Polymer.sigmaSq β *
        Collision.spatialRenewal (Polymer.sigmaSq β) n (y - x)) *
          (∫ ω, F y ω ∂disorderLaw) := by
  have heq : (fun ω => ∑' x, ∑' y, W x * (Polymer.sigmaSq β *
      Collision.spatialRenewal (Polymer.sigmaSq β) n (y - x)) * F y ω) =
      (fun ω => ∑ x ∈ S, ∑ y ∈ Polymer.endpoints x n, W x * (Polymer.sigmaSq β *
        Collision.spatialRenewal (Polymer.sigmaSq β) n (y - x)) * F y ω) := by
    funext ω
    exact spatialCell_eq_finite β n W S hW (fun y => F y ω)
  have hInt (x y : Site) : Integrable (fun ω => W x * (Polymer.sigmaSq β *
      Collision.spatialRenewal (Polymer.sigmaSq β) n (y - x)) * F y ω) disorderLaw :=
    (hF y).const_mul _
  rw [heq]
  constructor
  · exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => hInt x y
  · rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hInt x y))]
    rw [spatialCell_eq_finite β n W S hW]
    apply Finset.sum_congr rfl
    intro x _
    rw [integral_finsetSum _ (fun y _ => hInt x y)]
    apply Finset.sum_congr rfl
    intro y _
    exact integral_const_mul _ _

/-- A collision cell with finitely supported initial weights is a finite sum over times and reachable sites. -/
theorem collisionCellSum_eq_finite (β : ℝ) (A B : ℕ) (W : ℕ → Site → ℝ)
    (S : ℕ → Finset Site) (hW : ∀ a x, x ∉ S a → W a x = 0) (F : ℕ → Site → ℝ) :
    collisionCellSum (Polymer.sigmaSq β) A B W F =
      ∑ a ∈ Finset.Ioc A B, ∑ b ∈ Finset.Icc a B, ∑ x ∈ S a,
        ∑ y ∈ Polymer.endpoints x (b - a), W a x *
          (Polymer.sigmaSq β * Collision.spatialRenewal (Polymer.sigmaSq β) (b - a) (y - x)) *
            F b y := by
  unfold collisionCellSum
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact spatialCell_eq_finite β (b - a) (W a) (S a) (hW a) (F b)

/-- Collision operators commute with finite sums of continuation data. -/
theorem collisionCellSum_finsetSum {ι : Type*} (β : ℝ) (A B : ℕ)
    (W : ℕ → Site → ℝ) (S : ℕ → Finset Site)
    (hW : ∀ a x, x ∉ S a → W a x = 0) (I : Finset ι) (F : ι → ℕ → Site → ℝ) :
    collisionCellSum (Polymer.sigmaSq β) A B W (fun b y => ∑ i ∈ I, F i b y) =
      ∑ i ∈ I, collisionCellSum (Polymer.sigmaSq β) A B W (F i) := by
  simp only [collisionCellSum_eq_finite β A B W S hW, Finset.mul_sum]
  simp_rw [← Finset.sum_comm (s := I)]

/-- Collision continuations are used only at last times at most the upper cell endpoint. -/
theorem collisionCellSum_congr (σ2 : ℝ) (A B : ℕ) (W : ℕ → Site → ℝ)
    {F G : ℕ → Site → ℝ} (hFG : ∀ b, b ≤ B → ∀ y, F b y = G b y) :
    collisionCellSum σ2 A B W F = collisionCellSum σ2 A B W G := by
  unfold collisionCellSum
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b hb
  apply tsum_congr
  intro x
  apply tsum_congr
  intro y
  rw [hFG b (Finset.mem_Icc.1 hb).2 y]

/-- Integrable continuation data can be integrated through a collision cell sum. -/
theorem collisionCellSum_integrable_integral (β : ℝ) (A B : ℕ)
    (W : ℕ → Site → ℝ) (S : ℕ → Finset Site)
    (hW : ∀ a x, x ∉ S a → W a x = 0) (F : ℕ → Site → Disorder → ℝ)
    (hF : ∀ b y, Integrable (F b y) disorderLaw) :
    Integrable (fun ω => collisionCellSum (Polymer.sigmaSq β) A B W
      (fun b y => F b y ω)) disorderLaw ∧
    (∫ ω, collisionCellSum (Polymer.sigmaSq β) A B W (fun b y => F b y ω) ∂disorderLaw) =
      collisionCellSum (Polymer.sigmaSq β) A B W (fun b y => ∫ ω, F b y ω ∂disorderLaw) := by
  have hc (a b : ℕ) := spatialCell_integrable_integral β (b - a) (W a) (S a)
    (hW a) (F b) (hF b)
  unfold collisionCellSum
  constructor
  · exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hc a b).1
  · rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (hc a b).1))]
    apply Finset.sum_congr rfl
    intro a _
    rw [integral_finsetSum _ (fun b _ => (hc a b).1)]
    apply Finset.sum_congr rfl
    intro b _
    exact (hc a b).2

end Critical2DKPZ.Blocks
