/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Occupied
public import Critical2DKPZ.Collision.SpatialRenewal

/-! # Collision sums for closed discrepancy strings

The zero-gap atom of `spatialRenewal` is included: a block with a single
collision has equal first and last collision times.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Blocks

/-- The collision sum over the remaining occupied blocks. -/
def stringTail (σ2 : ℝ) (t : ℕ → ℕ) : List ℕ → ℕ → Site → ℝ
  | [], _, _ => 1
  | i :: is, bprev, yprev =>
    ∑ a ∈ Finset.Ioc (t (i - 1)) (t i), ∑ b ∈ Finset.Icc a (t i), ∑' x, ∑' y,
      (srwKernel (a - bprev) (x - yprev) - srwKernel a x) ^ 2 *
        (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) * stringTail σ2 t is b y

/-- The squared-chaos sum, with both endpoint blocks occupied. Intended for `u < v`; at `u = v`
the block `u` would be used twice. -/
def closedStringSum (σ2 : ℝ) (t : ℕ → ℕ) (u v : ℕ) : ℝ :=
  ∑ S ∈ (Finset.Ioo u v).powerset,
    ∑ a ∈ Finset.Ioc (t (u - 1)) (t u), ∑ b ∈ Finset.Icc a (t u), ∑' x, ∑' y,
      srwKernel a x ^ 2 * (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) *
        stringTail σ2 t (S.sort (· ≤ ·) ++ [v]) b y

end Critical2DKPZ.Blocks
