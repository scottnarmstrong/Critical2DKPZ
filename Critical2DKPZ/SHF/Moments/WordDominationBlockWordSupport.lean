/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionRunExpansionSupport
public import Critical2DKPZ.SHF.Flow.SlabProductsCore
import Mathlib.Tactic

/-! # Finite endpoint support of block-word kernels -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.Polymer

/-- Configurations reachable coordinatewise from the initial configuration in
the given number of walk steps. -/
def collisionWordConfigurationEndpointSet {h : ℕ} (n : ℕ)
    (x : Fin h → Site) : Finset (Fin h → Site) :=
  Fintype.piFinset (fun i => endpoints (x i) n)

/-- A block-word kernel vanishes when its terminal configuration cannot be
reached from its initial configuration in the allotted number of steps. -/
theorem blockWordKernel_zero_of_endpoint_not_mem {h : ℕ} (σ : ℝ)
    (w : List (CollisionPair h)) (n : ℕ) (x y : Fin h → Site)
    (hy : y ∉ collisionWordConfigurationEndpointSet n x) :
    blockWordKernel σ w n x y = 0 := by
  apply blockWordKernel_zero_of_start_endpoint_not_mem σ w n x y
  intro hx
  apply hy
  apply Fintype.mem_piFinset.mpr
  intro i
  have hxi := Fintype.mem_piFinset.mp hx i
  exact Critical2DKPZ.SHF.Flow.mem_endpoints_reverse hxi

/-- Multiplication by an arbitrary endpoint profile preserves summability of
a block-word kernel row, since its terminal support is finite. -/
theorem summable_mul_blockWordKernel_row {h : ℕ} (σ : ℝ)
    (w : List (CollisionPair h)) (n : ℕ) (x : Fin h → Site)
    (f : (Fin h → Site) → ℝ) :
    Summable (fun y => blockWordKernel σ w n x y * f y) := by
  classical
  apply summable_of_ne_finset_zero (s := collisionWordConfigurationEndpointSet n x)
  intro y hy
  rw [blockWordKernel_zero_of_endpoint_not_mem σ w n x y hy]
  simp

end Critical2DKPZ.SHF.Moments

end
