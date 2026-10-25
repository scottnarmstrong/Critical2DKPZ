/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.Basic
public import Critical2DKPZ.Definitions.IsCriticalSHF
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Geometric flow blocks for the scale limit

These are the flow-level masses and truncated logarithms in the note. Estimates
and independence concern positive block indices and strictly ordered times.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The decreasing geometric time grid. -/
def tau (ρ : ℝ) (j : ℕ) : ℝ := (ρ⁻¹) ^ j

/-- The flow mass of block `j`, used for `j ≥ 1`. -/
def blockMass {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ρ : ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  shfPairing Z (tau ρ j) (tau ρ (j - 1))
    (fun y => heatKernel (tau ρ j) y) (fun _ => 1) ω

/-- The logarithm of a block mass, truncated to the event of small mass fluctuation. -/
def logTrunc {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ρ : ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  if |blockMass Z ρ j ω - 1| ≤ 1 / 2 then Real.log (blockMass Z ρ j ω) else 0

/-- The sum of the first `n` truncated logarithmic block masses. -/
def partialSum {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ρ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, logTrunc Z ρ j ω

/-- The heat-start flow logarithm with terminal time one. -/
def Fheat {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (δ : ℝ) (y : Plane) (ω : Ω) : ℝ :=
  Real.log (shfPairing Z δ 1 (fun y' => heatKernel δ (y' - y)) (fun _ => 1) ω)

/-- The mass of the flow from geometric time `n` to geometric time `ℓ`. -/
def blockA {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ρ : ℝ) (n ℓ : ℕ) (ω : Ω) : ℝ :=
  shfPairing Z (tau ρ n) (tau ρ ℓ) (fun y => heatKernel (tau ρ n) y) (fun _ => 1) ω

/-- The ratio comparing a multi-block mass to the product of its block masses. -/
def blockR {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ρ : ℝ) (n ℓ : ℕ) (ω : Ω) : ℝ :=
  blockA Z ρ n ℓ ω / (∏ j ∈ Finset.Ioc ℓ n, blockMass Z ρ j ω)

/-- The mass of the remaining time interval, relative to the multi-block mass. -/
def blockQ {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ρ : ℝ) (n ℓ : ℕ) (ω : Ω) : ℝ :=
  shfPairing Z (tau ρ n) 1 (fun y => heatKernel (tau ρ n) y) (fun _ => 1) ω /
    blockA Z ρ n ℓ ω

/-- The exponentially growing geometric block index associated with the scale clock. -/
def nL (ρ L s : ℝ) : ℕ := ⌊2 * Real.exp (L * s) / Real.log ρ⌋₊

/-- Every geometric time is positive. -/
theorem tau_pos {ρ : ℝ} (hρ : 1 < ρ) (j : ℕ) : 0 < tau ρ j :=
  pow_pos (inv_pos.mpr (lt_trans zero_lt_one hρ)) j

/-- Consecutive geometric times are strictly decreasing. -/
theorem tau_succ_lt {ρ : ℝ} (hρ : 1 < ρ) (j : ℕ) : tau ρ (j + 1) < tau ρ j := by
  dsimp [tau]
  rw [pow_succ]
  calc
    (ρ⁻¹) ^ j * ρ⁻¹ < (ρ⁻¹) ^ j * 1 :=
      mul_lt_mul_of_pos_left (inv_lt_one_of_one_lt₀ hρ) (tau_pos hρ j)
    _ = (ρ⁻¹) ^ j := mul_one _

/-- The geometric time grid is strictly decreasing. -/
theorem strictAnti_tau {ρ : ℝ} (hρ : 1 < ρ) : StrictAnti (tau ρ) :=
  strictAnti_nat_of_succ_lt (fun j => tau_succ_lt hρ j)

/-- All positive block indices lie strictly below terminal time one. -/
theorem tau_lt_one {ρ : ℝ} (hρ : 1 < ρ) {j : ℕ} (hj : 0 < j) : tau ρ j < 1 := by
  simpa only [tau, pow_zero] using strictAnti_tau hρ hj

/-- The geometric times tend to zero. -/
theorem tendsto_tau_zero {ρ : ℝ} (hρ : 1 < ρ) :
    Tendsto (tau ρ) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one
    (inv_nonneg.mpr (lt_trans zero_lt_one hρ).le) (inv_lt_one_of_one_lt₀ hρ)

end Critical2DKPZ.Extensions.ScaleLimit
