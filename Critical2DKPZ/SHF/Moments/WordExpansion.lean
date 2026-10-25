/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.SpatialRenewal
public import Critical2DKPZ.Definitions.Cell
public import Critical2DKPZ.Definitions.CriticalBeta
public import Critical2DKPZ.Definitions.EvenCeil
public import Critical2DKPZ.Definitions.SrwKernel
public import Critical2DKPZ.Polymer.Chaos
public import Critical2DKPZ.SHF.DeltaBose.CollisionWords
public import Critical2DKPZ.SHF.Moments.CollisionExpansion
public import Critical2DKPZ.SHF.Moments.CollisionKernel
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Collision-word expansions of polymer moments -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose

/-- A collision-edge set selects at most one pair at each time. -/
def IsPairSimple {h : ℕ} (A : Finset (ℕ × CollisionPair h)) : Prop :=
  ∀ e ∈ A, ∀ e' ∈ A, e.1 = e'.1 → e = e'

/-- The resummed lattice kernel of a collision word: free walks, then for each letter `α` a first
`α`-collision after `s ≥ 1` steps, the pair's renewal block of `r ≥ 0` further steps (`spatialRenewal`,
spectators free), and the rest of the word in the remaining time. -/
def blockWordKernel {h : ℕ} (σ2 : ℝ) :
    List (CollisionPair h) → ℕ → (Fin h → Site) → (Fin h → Site) → ℝ
  | [], n, x, y => ∏ i, srwKernel n (y i - x i)
  | α :: w, n, x, y =>
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        ∑' u : Fin h → Site, ∑' v : Fin h → Site,
          (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
            (∏ i, srwKernel s (u i - x i)) * σ2 *
            Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
            (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else srwKernel r (v i - u i)) *
            blockWordKernel σ2 w (n - s - r) v y

/-- The non-pair part of the collision expansion: edge sets with two pairs selected at one time. -/
def nonpairCollisionRemainder (β : ℝ) (n h : ℕ) (x y : Fin h → Site) : ℝ := by
  classical
  exact ∑ A ∈ (collisionEdges n h).powerset.filter (fun A => ¬ IsPairSimple A),
    sigmaSq β ^ A.card * collisionSubsetCoefficient n h A x y

/-- The lattice test weight of a cell pair: `(N/4) ∫_{cell w × cell z} φ`. -/
def cellTestWeight (N : ℕ) (φ : C_c(Plane × Plane, ℝ)) (w z : Site) : ℝ :=
  (N / 4 : ℝ) * ∫ p in cell N w ×ˢ cell N z, φ p

/-- A word's contribution to the `h`-th moment of compact pairings. -/
def testedBlockWord (ϑ : ℝ) (N : ℕ) (s t : ℝ) {h : ℕ} (φ : Fin h → C_c(Plane × Plane, ℝ))
    (w : List (CollisionPair h)) : ℝ :=
  ∑' x : Fin h → Site, ∑' y : Fin h → Site, (∏ i, cellTestWeight N (φ i) (x i) (y i)) *
    blockWordKernel (sigmaSq (criticalBeta ϑ N)) w (evenCeil (N * t) - evenCeil (N * s)) x y

/-- The non-pair remainder of the `h`-th moment of compact pairings. -/
def testedNonpairRemainder (ϑ : ℝ) (N : ℕ) (s t : ℝ) {h : ℕ}
    (φ : Fin h → C_c(Plane × Plane, ℝ)) : ℝ :=
  ∑' x : Fin h → Site, ∑' y : Fin h → Site, (∏ i, cellTestWeight N (φ i) (x i) (y i)) *
    nonpairCollisionRemainder (criticalBeta ϑ N) (evenCeil (N * t) - evenCeil (N * s)) h x y

end Critical2DKPZ.SHF.Moments

end
