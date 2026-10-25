/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25Profiles
public import Critical2DKPZ.Definitions.SrwKernel

/-! # Green energies and localisation in CSZ25 Section 5 -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- The truncated Green function sums the even-time transition kernel up to the given horizon. -/
def truncatedGreen (L : ℕ) (z : Site) : ℝ :=
  ∑ n ∈ Finset.Icc 1 L, srwKernel (2 * n) z

/-- The Green energy `R_L(φ, φ)`, including both parity classes. -/
def greenEnergy (L : ℕ) (φ : Site → ℝ) : ℝ :=
  ∑' z, ∑' w, φ z * truncatedGreen L (z - w) * φ w

/-- The damped overlap at a microscopic damping rate. -/
def dampedOverlap (lam : ℝ) (L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 L, Real.exp (-lam * n) * srwKernel (2 * n) 0

/-- Exponential localisation at diffusive scale, including summability of the weight. -/
def ExpLocalized (t c₁ : ℝ) (L : ℕ) (φ : Site → ℝ) : Prop :=
  ∃ z₀ : Plane,
    Summable (fun z => φ z * Real.exp (2 * t * ‖siteToPlane z - z₀‖ / Real.sqrt L)) ∧
      ∑' z, φ z * Real.exp (2 * t * ‖siteToPlane z - z₀‖ / Real.sqrt L) ≤ c₁

end Critical2DKPZ.MomentBounds
